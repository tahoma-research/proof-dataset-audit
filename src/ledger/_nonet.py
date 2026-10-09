"""Exec a command under the child confinement layers, which the command and all its descendants keep:

- seccomp: socket() and socketpair() fail with EACCES for every domain, because a build step needs no
  socket, and code running in a step must not ask a local service to act outside the confinement (the
  user's D-Bus, and through it the systemd user manager; a container daemon). With --tcp, AF_INET and
  AF_INET6 sockets are allowed, and socketpair(AF_UNIX, SOCK_STREAM) (elan's libcurl starts its resolver
  thread with one): a stream pair is born connected, so it can neither connect nor send to a named socket.
  Other pairs stay refused, because a datagram socket from a pair can still send to a named socket, and
  socket(AF_UNIX) stays refused. listen() fails with EACCES, so neither a pair end nor a TCP socket listens
  (listen() binds an unbound TCP socket itself, past Landlock's bind rule); bind() stays allowed, because
  elan's resolver binds its UDP sockets. io_uring_setup fails with EACCES because an io_uring operation can
  create a socket without socket(). A system call from another ABI (i386 through int 0x80, or x32) kills the
  process, since its numbers would bypass these checks. Landlock mediates no change to a file's mode, owner,
  timestamps or extended attributes, which would reach any file of this uid, outside every WRITABLE directory:
  the calls that change an owner or an extended attribute (OWNER_XATTR) fail with EPERM, and with --no-meta,
  which every call that runs proof code takes, so do those that change a mode or timestamps (MODE_TIME; env
  builds and fetch steps keep them, since elan and git set file modes). An ioctl that sets a file's inode flags
  (INODE_FLAGS: append-only, no-dump, project ID …) fails with EPERM too, since no tool sets them;
- Landlock, with what the kernel's ABI handles (confine.handled: all of it from ABI 6, which the host requires):
  writes only beneath each WRITABLE directory and /dev/null; no ioctl on a device; no signal to a process outside
  the domain (the run that started the step, another step, any other process of the user);
  and with --tcp, a TCP connect to port 443 only and no TCP bind, so a fetch step reaches no local service;
- with --read-allow=PATH (repeated), which every call that runs proof code takes, a second Landlock layer: reads
  only beneath (or of) each such PATH, so proof code cannot read the operator's other files.

With --container, under the container's policy, the same layers but Landlock's TCP rule, and confine.run passes no
--read-allow there. The container runs as its own root, so the write layer is what keeps one call from rewriting what
a later call starts: this module, the interpreter, the toolchain.

Usage: python -m ledger._nonet [--container] [--tcp] [--no-meta] [--read-allow=PATH...] [WRITABLE...] --
       COMMAND [ARG...]
"""

import ctypes
import os
import sys

from ledger import confine

_PR_SET_SECCOMP, _SECCOMP_MODE_FILTER = 22, 2
# struct seccomp_data: int nr at offset 0, u32 arch at 4, u64 instruction pointer at 8, u64 args[6] at 16.
_NR, _ARCH, _ARG0_LOW, _ARG1_LOW = 0, 4, 16, 24  # x86_64 is little-endian: args[n]'s low 32 bits at 16 + 8n
_AUDIT_ARCH_X86_64 = 0xC000003E
_X32_SYSCALL_BIT = 0x40000000
_IOCTL, _SOCKET, _LISTEN, _SOCKETPAIR, _IO_URING_SETUP = 16, 41, 50, 53, 425
_AF_UNIX, _AF_INET, _AF_INET6 = 1, 2, 10
_SOCK_STREAM, _SOCK_FLAGS = 1, 0o4000 | 0o2000000  # SOCK_NONBLOCK | SOCK_CLOEXEC, which a type may carry
_EPERM, _EACCES = 1, 13
# chown, fchown, lchown, fchownat; setxattr, lsetxattr, fsetxattr, setxattrat; removexattr, lremovexattr,
# fremovexattr, removexattrat
OWNER_XATTR = (92, 93, 94, 260, 188, 189, 190, 463, 197, 198, 199, 466)
# chmod, fchmod, fchmodat, fchmodat2; utime, utimes, futimesat, utimensat
MODE_TIME = (90, 91, 268, 452, 132, 235, 261, 280)
INODE_FLAGS = (0x40086602, 0x40046602, 0x401C5820)  # ioctl FS_IOC_SETFLAGS, FS_IOC32_SETFLAGS, FS_IOC_FSSETXATTR
_RET_ALLOW, _RET_ERRNO, _RET_KILL_PROCESS = 0x7FFF0000, 0x00050000, 0x80000000
# BPF_LD|W|ABS, BPF_ALU|AND|K, BPF_JMP|JA, BPF_JMP|JEQ|K, BPF_JMP|JGE|K, BPF_RET|K
_LD, _AND, _JA, _JEQ, _JGE, _RET = 0x20, 0x54, 0x05, 0x15, 0x35, 0x06


# Classic BPF: (opcode, jump if true, jump if false, k). A jump of n skips the next n instructions (JA: k of
# them); "→ i" names the instruction it lands on. Comparisons are unsigned 32-bit.
def program(tcp: bool, no_meta: bool) -> list[tuple[int, int, int, int]]:
    meta = OWNER_XATTR + (MODE_TIME if no_meta else ())
    return [
        (_LD, 0, 0, _ARCH),                       # 0  A = the calling ABI
        (_JEQ, 0, 18, _AUDIT_ARCH_X86_64),        # 1  x86_64 → 2, any other ABI → 20
        (_LD, 0, 0, _NR),                         # 2  A = the system call number
        (_JGE, 16, 0, _X32_SYSCALL_BIT),          # 3  x32 numbering → 20, else → 4
        (_JEQ, 14, 0, _IO_URING_SETUP),           # 4  io_uring_setup → 19, else → 5
        (_JEQ, 13, 0, _LISTEN),                   # 5  listen → 19, else → 6
        (_JEQ, 1, 0, _SOCKET),                    # 6  socket → 8, else → 7
        (_JEQ, 0, 10, _SOCKETPAIR),               # 7  socketpair → 8, else → 18
        (_LD, 0, 0, _ARG0_LOW),                   # 8  A = the domain; the kernel reads only its low 32 bits
        (_JEQ, 7, 0, _AF_INET),                   # 9  AF_INET → 17, else → 10
        (_JEQ, 6, 0, _AF_INET6),                  # 10 AF_INET6 → 17, else → 11
        (_JEQ, 0, 7, _AF_UNIX),                   # 11 AF_UNIX → 12, any other domain → 19
        (_LD, 0, 0, _NR),                         # 12 A = the system call number again
        (_JEQ, 0, 5, _SOCKETPAIR),                # 13 socketpair → 14, socket(AF_UNIX) → 19
        (_LD, 0, 0, _ARG1_LOW),                   # 14 A = the type, low 32 bits as the kernel reads it
        (_AND, 0, 0, ~_SOCK_FLAGS & 0xFFFFFFFF),  # 15 A = the type without its two flags
        (_JEQ, 0, 2, _SOCK_STREAM),               # 16 SOCK_STREAM → 17, any other type or bit → 19
        (_RET, 0, 0, _RET_ALLOW if tcp else _RET_ERRNO | _EACCES),  # 17 an IP socket or a stream pair: --tcp only
        (_JA, 0, 0, 2),                           # 18 any other call → 21, A still its number
        (_RET, 0, 0, _RET_ERRNO | _EACCES),       # 19 fail with EACCES
        (_RET, 0, 0, _RET_KILL_PROCESS),          # 20 kill the whole process
        # 21 to 20 + n, one per call of `meta` (n of them): that call → 27 + n, else the next
        *((_JEQ, len(meta) - i + 5, 0, nr) for i, nr in enumerate(meta)),
        (_JEQ, 0, 4, _IOCTL),                     # 21 + n ioctl → 22 + n, any other call → 26 + n
        (_LD, 0, 0, _ARG1_LOW),                   # 22 + n A = the request, low 32 bits as the kernel reads it
        # 23 + n to 25 + n, one per request of INODE_FLAGS: that request → 27 + n, else the next
        *((_JEQ, len(INODE_FLAGS) - i, 0, request) for i, request in enumerate(INODE_FLAGS)),
        (_RET, 0, 0, _RET_ALLOW),                 # 26 + n allow
        (_RET, 0, 0, _RET_ERRNO | _EPERM),        # 27 + n fail with EPERM
    ]


class _Instruction(ctypes.Structure):
    _fields_ = [("code", ctypes.c_uint16), ("jt", ctypes.c_uint8), ("jf", ctypes.c_uint8), ("k", ctypes.c_uint32)]


class _Program(ctypes.Structure):
    _fields_ = [("len", ctypes.c_ushort), ("filter", ctypes.POINTER(_Instruction))]


def main(argv: list[str]) -> None:
    split = argv.index("--") if "--" in argv else len(argv)
    options, command = argv[:split], argv[split + 1:]
    if not command:
        sys.exit("usage: python -m ledger._nonet [--container] [--tcp] [--no-meta] [--read-allow=PATH...] "
                 "[WRITABLE...] -- COMMAND [ARG...]")
    tcp = "--tcp" in options
    fs, scoped = confine.handled(confine.landlock_abi())
    confine.restrict(fs=fs, scoped=scoped,  # sets no_new_privs
                     beneath=[*((path, fs) for path in options if not path.startswith("--")),
                              ("/dev/null", confine.FILE_WRITE & fs)],
                     tcp_connect=(443,) if tcp and "--container" not in options else None)
    if reads := [option.removeprefix("--read-allow=") for option in options if option.startswith("--read-allow=")]:
        confine.restrict(fs=confine.FS_READ, beneath=[
            (path, confine.FS_READ if os.path.isdir(path) else confine.READ_FILE) for path in reads])
    rules = program(tcp, "--no-meta" in options)
    instructions = (_Instruction * len(rules))(*(_Instruction(*i) for i in rules))
    confine.prctl(_PR_SET_SECCOMP, _SECCOMP_MODE_FILTER, ctypes.byref(_Program(len(rules), instructions)))
    os.execvp(command[0], command)


if __name__ == "__main__":
    main(sys.argv[1:])
