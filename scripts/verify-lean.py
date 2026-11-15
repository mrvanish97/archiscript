#!/usr/bin/env python3
"""Build and audit the exact checked source tree using the pinned Lean toolchain.

Reports are reproducible artifacts under .lake/reports. Proof acceptance uses
Lean's transitive dependency audit, controlled negative fixtures and kernel
replay. Source hashing detects changes during verification, not mathematical
truth. Independent contract authorship remains a modeling responsibility.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / ".lake" / "reports"


def source_digest() -> str:
    digest = hashlib.sha256()
    paths = []
    for directory, directories, filenames in os.walk(ROOT, topdown=True, followlinks=False):
        directories[:] = [name for name in directories
                          if name not in {".git", ".lake", "__pycache__"}]
        for name in filenames:
            path = Path(directory) / name
            if path.is_file() and (path.suffix in {".lean", ".py", ".sh", ".toml", ".yml"}
                                   or path.name == "lean-toolchain"):
                paths.append(path)
    for path in sorted(paths):
        digest.update(str(path.relative_to(ROOT)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def warning_overrides() -> list[str]:
    bad = []
    parents = [ROOT]
    for directory, directories, _ in os.walk(ROOT, topdown=True, followlinks=False):
        parent = Path(directory)
        # Unlike the digest, warnings exclude only these root-relative subtrees.
        if parent == ROOT:
            directories[:] = [name for name in directories if name not in {".lake", ".git"}]
        elif parent == ROOT / "Test":
            directories[:] = [name for name in directories if name != "Negative"]
        # Preserve Python 3.12 rglob's order: root, then each walk entry's children.
        parents.extend(parent / name for name in directories if not (parent / name).is_symlink())
    for parent in parents:
        # glob also matches directory names; retain their read errors.
        for path in parent.glob("*.lean"):
            if re.search(r"(?m)^\s*set_option\s+warningAsError\s+false\b", path.read_text()):
                bad.append(str(path.relative_to(ROOT)))
    return bad


def main() -> int:
    REPORTS.mkdir(parents=True, exist_ok=True)
    before = source_digest()
    report = {"source_sha256": before, "commands": [], "status": "failed"}
    report["git_sha"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    try:
        overrides = warning_overrides()
        if overrides:
            raise RuntimeError(f"warningAsError suppression outside negative fixtures: {overrides}")
        commands = [
            ("clean", ["lake", "clean"]),
            ("build", ["lake", "build"]),
            ("audit-build", ["lake", "build", "ArchiScript.ProofAudit"]),
            ("smoke", ["lake", "env", "lean", "-DwarningAsError=true", "skills/archiscript/examples/CurrentApi.lean"]),
            ("axioms", ["lake", "env", "lean", "-DwarningAsError=true", "scripts/audit-proofs.lean"]),
            ("negative", [sys.executable, "scripts/check-lean-negative.py"]),
            ("kernel", ["lake", "env", "leanchecker", "ArchiScript", "ArchiScriptExamples", "ArchiScriptTests"]),
        ]
        for name, command in commands:
            start = time.monotonic()
            log = REPORTS / f"{name}.log"
            with log.open("w") as output:
                result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
            report["commands"].append({"name": name, "command": command, "returncode": result.returncode,
                                       "seconds": round(time.monotonic() - start, 3)})
            print(f"{name}: {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
            if result.returncode:
                raise RuntimeError(f"{name} failed; see {log.relative_to(ROOT)}")
            if source_digest() != before:
                raise RuntimeError("sources changed during verification; report is stale")
        entries = [json.loads(line) for line in (REPORTS / "axioms.log").read_text().splitlines()
                   if line.startswith('{"declaration":') or line.startswith('{"axioms":')]
        if not entries:
            raise RuntimeError("axiom audit emitted no declaration records")
        (REPORTS / "axioms.json").write_text(json.dumps(entries, indent=2) + "\n")
        report["audited_declarations"] = len(entries)
        report["status"] = "passed"
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
        print(error, file=sys.stderr)
    finally:
        (REPORTS / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
