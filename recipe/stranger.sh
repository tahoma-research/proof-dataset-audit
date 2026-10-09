# The reproduction procedure, run unmodified on an x86_64 host with rootless podman:
#
#   sh stranger.sh [<repository> <tag>] [--pair <pair_id or pair_sha256> [--with-legacy]]
#
# It starts one container from the public base image below, pinned by digest, on a network of its own that
# slirp4netns gives it in user mode (never the host's, whatever podman's configuration says), with public resolvers,
# no search domain, a memory limit, swap included, equal to the largest memory cap in the constants.toml of <tag>
# where it reads <tag> from its clone, else in the one beside it, no capability but the five apt needs and the one
# that drops them all, no new privileges and at most 4096 processes. Inside, it installs git, curl, ca-certificates
# and time from the distribution, fetches the elan release below and checks its sha256, clones <tag> of
# <repository>, and runs the date-free command over the container's policy, with no capability left, which prints
# the verdict. <repository> is a URL, or a local repository, which enters the container as a bundle on standard
# input; nothing else enters it.
# Without <repository> and <tag>, they are the origin of the clone this file is in, over https where it is GitHub's
# over ssh, which the container has no client for, and the latest tag of its checkout; it stops on any other origin
# that is neither https nor a directory, and on a <repository> or origin over https with credentials, which would enter
# the container. Its git calls read the clone it is in, never a repository the caller's environment names.
set -eu
unset GIT_DIR GIT_WORK_TREE
image=docker.io/library/python@sha256:fd3817f3a855f6c2ada16ac9468e5ee93e361005bd226fd5a5ee1a504e038c84
elan=https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz
elan_sha256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
inside='set -eu
cd "$HOME"
elan=$1 elan_sha256=$2 source=$3 tag=$4
shift 4
if [ "$source" = - ]; then cat > tree.bundle; source=tree.bundle; fi
export DEBIAN_FRONTEND=noninteractive
{ apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git time; } > apt.log 2>&1 ||
    { cat apt.log >&2; exit 1; }
curl -fsSL -o elan.tar.gz "$elan"
echo "$elan_sha256  elan.tar.gz" | sha256sum -c - >&2
git -c advice.detachedHead=false clone -q --branch "$tag" "$source" tree
mkdir -p tree/elan/bin
tar -xzf elan.tar.gz -C tree/elan/bin
mv tree/elan/bin/elan-init tree/elan/bin/elan
cd tree
PYTHONPATH=src exec setpriv --inh-caps=-all --bounding-set=-all -- \
    python3 -m ledger run --policy recipe/policy/container.toml "$@"'
constants=$(cat "${0%stranger.sh}constants.toml")  # the checkout's; the form without <repository> takes its tag's
case ${1:---} in
--*) origin=$(git -C "${0%stranger.sh}." remote get-url origin)
     case $origin in
     https://*) repository=$origin ;;
     git@github\.com:?*/?* | ssh:[/][/]git@github\.com/?*/?*) repository=https://github.com/${origin#*github.com[:/]} ;;
     *) [ -d "$origin" ] ||
        { echo "stranger.sh: the origin is neither https nor a directory: clone it over https" >&2; exit 1; }
        repository=$origin ;;
     esac
     tag=$(git -C "${0%stranger.sh}." describe --tags --abbrev=0)
     constants=$(git -C "${0%stranger.sh}." show "$tag:recipe/constants.toml") ;;
*) repository=$1 tag=$2; shift 2 ;;
esac
case $repository in https://*) case ${repository%%@*} in https://*/* | "$repository") ;; *)  # an @ before the path
    echo "stranger.sh: the repository URL holds credentials: give one without them" >&2; exit 1 ;; esac ;; esac
memory=$(printf '%s\n' "$constants" | awk '/^((leg|agg)_memory_max_mb|replay_memory_floor_mib) / && $3 > m {m = $3} END {print m "m"}')
flags="--rm -i --network=slirp4netns --dns=1.1.1.1 --dns=9.9.9.9 --dns-search=. --memory=$memory --memory-swap=$memory --cap-drop=ALL --cap-add=CHOWN,DAC_OVERRIDE,FOWNER,SETUID,SETGID,SETPCAP --security-opt=no-new-privileges --pids-limit=4096"
if [ -d "$repository" ]; then source=-; else source=$repository; fi
{ if [ "$source" = - ]; then git -C "$repository" bundle create -q - --all; fi; } |
    podman run $flags "$image" \
    sh -c "$inside" sh "$elan" "$elan_sha256" "$source" "$tag" "$@"
