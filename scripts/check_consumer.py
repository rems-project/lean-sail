#!/usr/bin/env python3
"""Build ordinary public imports against a clean Git dependency at an exact revision."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    with tempfile.TemporaryDirectory(prefix="lean-sail-consumer-") as directory:
        consumer = Path(directory)
        shutil.copytree(root / "tests/consumer", consumer, dirs_exist_ok=True)
        (consumer / "lean-toolchain").write_text(args.toolchain + "\n")
        (consumer / "lakefile.toml").write_text(
            'name = "runtime-consumer"\ndefaultTargets = ["Consumer"]\n\n'
            '[[lean_lib]]\nname = "Consumer"\nglobs = ["Consumer.**"]\n\n'
            '[[require]]\nname = "Sail"\n'
            f'git = {json.dumps(root.as_uri())}\nrev = "{revision}"\n'
        )
        lake = ["elan", "run", args.toolchain, "lake"]
        subprocess.run(lake + ["update", "Sail"], cwd=consumer, check=True)
        result = subprocess.run(
            lake + ["--no-cache", "build", "--wfail", "--iofail"],
            cwd=consumer, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        print(result.stdout, end="")
        result.check_returncode()
        if "Build completed successfully" not in result.stdout:
            raise RuntimeError("Lake exited without its successful-build marker")
        actual = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=consumer / ".lake/packages/Sail", text=True
        ).strip()
        if actual != revision:
            raise RuntimeError(f"Consumer used {actual}, expected {revision}")
    print(f"Clean Git consumer passed at {revision} on {args.toolchain}")


if __name__ == "__main__":
    main()
