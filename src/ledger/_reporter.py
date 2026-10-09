"""Run a command inside its systemd scope and, before exiting, record the scope's memory peak and OOM-kill
count in FILE, which must not exist yet, with the signal that killed the command (0: none); then exit with
the command's status (128 + N when signal N killed it). The scope's cgroup vanishes when the scope ends, so
these can be read only from inside it, and only before its last process exits.

Usage: python -m ledger._reporter --out FILE -- COMMAND [ARG...]
"""

import json
import os
import subprocess
import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) < 4 or argv[0] != "--out" or argv[2] != "--":
        sys.exit("usage: python -m ledger._reporter --out FILE -- COMMAND [ARG...]")
    status = subprocess.run(argv[3:]).returncode
    cgroup = Path("/sys/fs/cgroup" + Path("/proc/self/cgroup").read_text().strip().removeprefix("0::"))
    events = dict(line.split() for line in (cgroup / "memory.events").read_text().splitlines())
    with open(os.open(argv[1], os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600), "w") as f:
        json.dump({"peak_mem_kb": int((cgroup / "memory.peak").read_text()) // 1024,
                   "oom_kill": int(events["oom_kill"]), "signal": max(0, -status)}, f)
    return status if status >= 0 else 128 - status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
