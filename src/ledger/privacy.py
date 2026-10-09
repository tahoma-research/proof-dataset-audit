"""What may never reach the public tree: the patterns the gate file checks each line against, and the sweeps
`stage` and `publish` run over every path and byte a commit would hold."""

import ipaddress
import os
import re
import socket
import tempfile
from pathlib import Path, PurePosixPath

from ledger import confine
from ledger.types import LedgerStop

URL = re.compile(r"https?://[^/\s]+")  # a link's scheme and host, exempt from the path checks; https:/// has none
ROOTED = re.compile(r"(?<![\w/.\-])/+(?=[\w.\-~])|~[\w.\-]*/")  # an absolute path, file:// and ~user/ included
ADDRESS_LIKE = re.compile(r"[0-9A-Fa-f:.]+")
IPV4 = re.compile(r"(?<!\d)(?=(\d{1,3}(?:\.\d{1,3}){3})(?!\d))", re.A)  # each dotted quad, overlapping ones too
FIB_TRIE, IF_INET6 = Path("/proc/net/fib_trie"), Path("/proc/net/if_inet6")
LOCAL = re.compile(r"\|-- (\S+)\n(?:[ ]+/.*\n)*?[ ]+/32 host LOCAL$", re.M)  # a fib_trie leaf holding a local address
NO_HOST = ipaddress.ip_network("0.0.0.0/8")  # "this network": names no host, so 0.4.0.1 is a version string
# The IPv6 prefixes whose low 32 bits are an IPv4 address: IPv4-mapped, NAT64's well-known prefix, IPv4-compatible.
EMBEDS_IPV4 = [ipaddress.ip_network(net) for net in ("::ffff:0:0/96", "64:ff9b::/96", "::/96")]
# The addresses published prose may name: the documentation ranges, and the public resolvers recipe/stranger.sh gives
# its container.
PUBLISHABLE = [ipaddress.ip_network(net) for net in ("192.0.2.0/24", "198.51.100.0/24", "203.0.113.0/24",
                                                     "2001:db8::/32", "1.1.1.1/32", "9.9.9.9/32")]
SENTINEL = ("src/ledger/diagnostics.py", "src/ledger/privacy.py")  # whose `# path-sentinel` lines name a path pattern
PROSE = ("recipe/", "templates/")  # published text that must stand on its own for a public reader
CODE = ("src/", "tests/", "templates/")  # where a template placeholder is code, not an unrendered one
PLACEHOLDER = re.compile(r"\{(?:public_name|publisher)\}")
INFO_ATTRIBUTES = ".git/info/attributes"  # the git directory's own attributes file, never committed
HOST_PATH = re.compile(r"/home/(?!example/)|/mnt/(?!example/)|/srv/(?!example/)")  # path-sentinel
# from the `@`, one local-part character behind it: linear, where a leading [\w.%+-]+ rescans a long word
EMAIL = re.compile(r"(?<=[\w.%+-])@(?!example\.invalid\b)[\w-]+(?:\.[\w-]+)+")
# What the sweep refuses, and whether only in PROSE. Paths are looked for once each URL's host is replaced.
PATTERNS = (
    ("host path", HOST_PATH, False),
    ("e-mail address", EMAIL, False),
    ("development-overlay record", re.compile(r'"dev_overlay":\s*true'), False),
    ("absolute path", ROOTED, True),
    ("private reference", re.compile(r"\bPRD\b|\bstor(?:y|ies)\s+\d|open decision|§|\bspec\b|docs/", re.I), True),
)


def addresses(text: str) -> list:
    """Every host address the text may name: each dotted quad of ASCII digits bounded by others, each octet read as a
    decimal number, zero-padded too; in each run of ADDRESS_LIKE, each IPv6 address that starts at the run's start or
    after a colon or dot and ends at its end or before a colon or dot, so that a label, a :port or a .port glued on is
    read past; and the IPv4 address an IPv6 one embeds (under EMBEDS_IPV4, or 6to4's).
    A candidate too many is the safe side. The unspecified address (::, as in `x :: xs`) and 0.0.0.0/8 name no host."""
    return [address for _, _, address in located(text)]


def located(text: str) -> list:
    """Each address of `addresses` as (start, end, address): the span of the text it is read from, an embedded
    address its carrier's."""
    found = []
    for quad in IPV4.finditer(text):
        try:
            found.append((*quad.span(1), ipaddress.IPv4Address(bytes(map(int, quad[1].split("."))))))
        except ValueError:
            continue
    for run in ADDRESS_LIKE.finditer(text):
        if text.count(":", *run.span()) < 2:  # an IPv6 address holds two to eight colons
            continue
        cuts = [i for i in range(*run.span()) if text[i] in ":."]
        ends = [*cuts, run.end()]
        for j, start in enumerate([run.start(), *(i + 1 for i in cuts)]):
            for end in ends[j:]:
                if end - start > 45:  # an IPv6 address is at most 45 characters long
                    break
                if not 2 <= text.count(":", start, end) <= 8:
                    continue
                try:
                    address = ipaddress.IPv6Address(text[start:end])
                except ValueError:
                    continue
                embedded = [ipaddress.IPv4Address(int(address) & 0xFFFFFFFF) for net in EMBEDS_IPV4 if address in net]
                found += [(start, end, each) for each in (address, *embedded, address.sixtofour)]
    return [(start, end, each) for start, end, each in found
            if each and not (each.is_unspecified or each in NO_HOST)]


def own(policy) -> list:
    """The networks whose addresses are this host's or the house's: each entry of the policy's host_addresses, an
    address or a prefix, and every address this host holds live but loopback, which names no host, as the kernel
    lists them: its local IPv4 routes and its IPv6 addresses, none where IPv6 is disabled and if_inet6 is absent."""
    live = [*map(ipaddress.IPv4Address, LOCAL.findall(FIB_TRIE.read_text())),
            *(ipaddress.IPv6Address(int(line.split()[0], 16))
              for line in (IF_INET6.read_text().splitlines() if IF_INET6.exists() else []))]
    return [*(ipaddress.ip_network(entry, strict=False) for entry in policy.values["host_addresses"]),
            *(ipaddress.ip_network(address) for address in live if not address.is_loopback)]


def covered(text: str, nets: list) -> bool:
    """Whether the text names an address, in any form, inside one of the networks."""
    return any(address in net for address in addresses(text) for net in nets)


def stored(tree: Path, files: list[tuple[str, Path]]) -> list[tuple[str, bytes]]:
    """What the sweeps read for a commit of `files`, (path in the commit, file) pairs, in the repository `tree`:
    each one's content as a commit holds it (a symlink's target, a file's bytes), and the git directory's
    attributes file when it exists, which would convert those bytes as git add stores them."""
    info = tree / INFO_ATTRIBUTES
    return [(rel, os.readlink(path).encode() if path.is_symlink() else path.read_bytes())
            for rel, path in files + ([(INFO_ATTRIBUTES, info)] if os.path.lexists(info) else [])]


def hosts(policy) -> re.Pattern:
    """The policy's scrub list and this host's name, each matched in any case where no letter touches it; the package
    name is public, never a scrub term."""
    names = [n for n in (*policy.values["scrub"], socket.gethostname())
             if n.lower() != __package__]
    return re.compile("|".join(rf"(?<![A-Za-z]){re.escape(name)}(?![A-Za-z])" for name in names), re.I)


def terms(policy) -> list[str]:
    """The policy's denylist terms, in lower case; stops when it has none, since a sweep would pass blind."""
    found = [term.strip().lower() for term in Path(policy.values["privacy_denylist"]).read_text().splitlines()
             if term.strip() and not term.strip().startswith("#")]
    if not found:
        raise LedgerStop("the privacy denylist has no terms: the sweep would pass blind")
    return found


def refused(policy) -> re.Pattern:
    """What `sweep` refuses in any file, in any case, each at its widest: each host path, up to a space, quote, comma
    or bracket, and e-mail address whole, its local part from where a run of local-part characters starts (so a long
    one is read once), before any name or term within it; each name of `hosts`, each denylist term and each NUL."""
    whole = [rf"(?:{HOST_PATH.pattern})[^\s\"'`,()\[\]{{}}<>]*", rf"(?<![\w.%+-])[\w.%+-]+{EMAIL.pattern}"]
    return re.compile("|".join([*whole, hosts(policy).pattern, *map(re.escape, terms(policy)), "\0"]), re.I)


def sweep(files: list[tuple[str, bytes]], policy, dev: bool = False) -> None:
    """Stop when anything personal or private appears in the files, (path in the commit, content) pairs,
    naming each as `path:line: kind` (line 0 is the path itself), never the text found. A path or content that
    is not UTF-8, holds a NUL byte or is a git attributes file (which rewrites what git stores) is refused.
    Every file is checked against the policy's denylist (`terms`) in any case, `hosts` and any address in `own`; every
    file outside CODE against an unrendered placeholder; PROSE also against any absolute path, any IP address outside
    PUBLISHABLE but an IPv6 one read within a PUBLISHABLE IPv6 address's text (2001:db8::1's db8::1), and any private
    reference.
    `dev`, staging under the development overlay, admits its records."""
    denylist, host, nets = terms(policy), hosts(policy), own(policy)
    hits = []
    for rel, data in sorted(files):
        try:
            rel.encode()
            text = data.decode()
        except UnicodeError:
            text = ""
            hits.append(f"{rel}:0: not UTF-8")
        if "\ufffd" in rel:  # a name read from git's output, which replaces each byte that is not UTF-8
            hits.append(f"{rel}:0: not UTF-8")
        if b"\0" in data:
            hits.append(f"{rel}:0: NUL byte")
        if PurePosixPath(rel).name == ".gitattributes" or rel == INFO_ATTRIBUTES:
            hits.append(f"{rel}:0: git attributes file")
        prose = rel.startswith(PROSE)
        for number, line in enumerate([rel, *text.splitlines()]):
            for kind, pattern, prose_only in PATTERNS:
                sentinel = kind == "host path" and rel in SENTINEL and "# path-sentinel" in line
                if (prose_only and not prose) or sentinel or dev and kind == "development-overlay record":
                    continue
                if pattern.search(URL.sub("url", line) if kind.endswith("path") else line):
                    hits.append(f"{rel}:{number}: {kind}")
            if not rel.startswith(CODE) and PLACEHOLDER.search(line):
                hits.append(f"{rel}:{number}: unrendered placeholder")
            if prose:
                found = [(start, end, a, any(a in net for net in PUBLISHABLE)) for start, end, a in located(line)]
                public = [(start, end) for start, end, a, publishable in found if publishable and a.version == 6]
                if any(not publishable and not (a.version == 6 and any(s <= start and end <= e for s, e in public))
                       for start, end, a, publishable in found):
                    hits.append(f"{rel}:{number}: IP address")
            if any(term in line.lower() for term in denylist):
                hits.append(f"{rel}:{number}: denylist term")
            if host.search(line) or covered(line, nets):
                hits.append(f"{rel}:{number}: host name or address")
    if hits:
        raise LedgerStop("privacy sweep: " + "; ".join(dict.fromkeys(hits)))


def house(files: list[tuple[str, bytes]], policy) -> None:
    """Stop unless the house privacy sweep (policy.house_sweep) finds nothing in the files, each written out
    under a scratch directory of its own; a path that recurs (in several commits) goes in the next one."""
    (policy.root / "tmp").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=policy.root / "tmp") as scratch:
        seen: dict[str, int] = {}
        for rel, data in files:
            seen[rel] = seen.get(rel, -1) + 1
            (path := Path(scratch, str(seen[rel]), rel)).parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        found = confine.run([confine.PY, policy.values["house_sweep"], "--path", scratch, "--no-db"], cwd=Path(scratch),
                            writes=[])
    if found.exit:
        raise LedgerStop(f"house privacy sweep, exit {found.exit}: {found.output.strip()}")
