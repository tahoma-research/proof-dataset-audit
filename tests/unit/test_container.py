import json
import os
import re
import shutil
import subprocess
import tomllib

from helpers import REPO, git

from ledger import constants, report


def test_stranger_launch_has_one_source(tmp_path):
    """The image and podman flags, read from recipe/stranger.sh as ops/stranger/smoke.sh reads them: the image is
    recipe/Containerfile's base, the network is named, never the reader's default, the memory limit, swap included,
    is the largest memory cap the constants publish, and the container starts with no capability but those apt needs
    and SETPCAP, which drops them all, no new privileges and a bound on its processes. From a clone whose origin is GitHub over ssh, which the container
    cannot reach, in either form, the container clones the latest tag over https with the memory limit that tag's
    constants publish, where the checkout's differ; a URL given keeps the checkout's, whatever the caller's
    environment holds, a repository named by GIT_DIR included. A clone with no origin, one neither https nor a
    directory, or a <repository> or origin over https with credentials stops before any container starts, its message
    naming no URL."""
    shown = subprocess.run(["sh", "-c", 'eval "$(sed -n "/^image=/p; /^constants=/p; /^memory=/p; /^flags=/p" "$0")"; '
                            'echo "$image"; echo "$flags"', REPO / "recipe/stranger.sh"], capture_output=True, text=True,
                           check=True)
    image, flags = shown.stdout.splitlines()
    limits = tomllib.loads((REPO / "recipe/constants.toml").read_text())["limits"]
    cap = max(limits[key] for key in ("leg_memory_max_mb", "agg_memory_max_mb", "replay_memory_floor_mib"))
    assert f"FROM {image}\n" in (REPO / "recipe/Containerfile").read_text()
    assert {"--network=slirp4netns", f"--memory={cap}m", f"--memory-swap={cap}m", "--cap-drop=ALL",
            "--cap-add=CHOWN,DAC_OVERRIDE,FOWNER,SETUID,SETGID,SETPCAP", "--security-opt=no-new-privileges",
            "--pids-limit=4096"} <= set(flags.split())
    shutil.copytree(REPO / "recipe", tmp_path / "recipe")
    (podman := tmp_path / "bin/podman").parent.mkdir()
    podman.write_text('#!/bin/sh\necho "$@"\n')
    podman.chmod(0o755)
    for args in (["init", "-q"], ["add", "."], ["-c", "user.name=x", "-c", "user.email=x@example.invalid", "commit",
                  "-qm", "x"], ["tag", "v1"]):
        git("-C", tmp_path, *args)
    (moved := tmp_path / "recipe/constants.toml").write_text(re.sub(r"(?m)^replay_memory_floor_mib = \d+",
                                                                    f"replay_memory_floor_mib = {cap + 1}",
                                                                    moved.read_text()))

    def stranger(*args):
        return subprocess.run(["sh", "recipe/stranger.sh", *args], cwd=tmp_path, capture_output=True, text=True,
                              env=os.environ | {"PATH": f"{podman.parent}:{os.environ['PATH']}",
                                                "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_NOSYSTEM": "1",
                                                "GIT_DIR": str(tmp_path / "elsewhere"),
                                                "constants": "replay_memory_floor_mib = 1"})
    stops = ""
    for origin in (None, "@".join(["git", "github.com:org/repo.git"]),
                   "ssh:" + "//" + "@".join(["git", "github.com/org/repo.git"]),
                   "https://" + "@".join(["user:token", "example.invalid/org/repo.git"]),
                   "ssh:" + "//" + "@".join(["git", "example.invalid/org/repo.git"])):
        if origin:
            git("-C", tmp_path, "config", "remote.origin.url", origin)
        run = stranger("--pair", "p")
        if origin and "github" in origin:
            assert run.stdout.endswith(" https://github.com/org/repo.git v1 --pair p\n"), run.stderr
            assert f"--memory={cap}m" in run.stdout.split()
        else:
            assert run.returncode and run.stdout == "", run.stdout
            stops += run.stderr
    stops += stranger("https://" + "@".join(["user:token", "example.invalid/org/repo.git"]), "v1").stderr
    assert "neither https nor a directory: clone it over https" in stops and "example.invalid" not in stops
    assert stops.count("the repository URL holds credentials: give one without them") == 2
    assert f"--memory={cap + 1}m" in stranger("https://example.invalid/org/repo.git", "v1").stdout.split()


def test_image_digest_recorded_nonevidential(snapshot, stage_policy, root):
    """With the convenience image's digest recorded in measure/image.json, the report's index gives it as the pin
    environment's image, marked not evidence; with none recorded, the index names no image. The README's reproduction
    asks for the largest memory cap the constants publish and the container policy's disk_floor_gb + disk_need_gb."""
    public, _ = snapshot
    index = root / "results/index.json"
    report.run(stage_policy, constants.load(public))
    assert json.loads(index.read_text())["environments"]["pin"]["image"] is None
    limits = tomllib.loads((public / "recipe/constants.toml").read_text())["limits"]
    container = tomllib.loads((public / "recipe/policy/container.toml").read_text())
    memory = max(limits[key] for key in ("leg_memory_max_mb", "agg_memory_max_mb", "replay_memory_floor_mib"))
    page = " ".join(report.render(json.loads((root / "results/summary.json").read_text()))["README.md"].split())
    assert (f"{memory:,} MiB of memory" in page and f"{container['disk_floor_gb'] + container['disk_need_gb']:,} GB "
            "of free disk" in page), page
    digest = "sha256:" + "a" * 64
    (root / "measure/image.json").write_text(json.dumps({"digest": digest}))
    report.run(stage_policy, constants.load(public))
    assert json.loads(index.read_text())["environments"]["pin"]["image"] == {"digest": digest, "evidential": False}
