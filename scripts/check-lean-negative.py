#!/usr/bin/env python3
"""Reject Lean fixtures for their specified EXPECT diagnostics, including audits."""

from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def expectations(source: str) -> list[str]:
    return [line.removeprefix("-- EXPECT: ").strip()
            for line in source.splitlines() if line.startswith("-- EXPECT: ")]


def main() -> int:
    failures = []
    for path in sorted((ROOT / "Test" / "Negative").glob("*.lean")):
        expected = expectations(path.read_text())
        if not expected:
            failures.append(f"{path.name}: missing EXPECT diagnostic")
            continue
        result = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", str(path.relative_to(ROOT))],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=120,
        )
        if result.returncode == 0 or any(item not in result.stdout for item in expected):
            failures.append(f"{path.name}: wrong verdict/diagnostic\n{result.stdout[:12000]}")
        else:
            print(f"expected failure: {path.name}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
