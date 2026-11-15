"""Compare pruned walks with the original algorithms in isolated source trees."""

import hashlib
import importlib.util
import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "verify_lean", Path(__file__).with_name("verify-lean.py"))
verify = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verify)


def original_source_digest(root):
    digest = hashlib.sha256()
    paths = [p for p in root.rglob("*") if p.is_file()
             and not any(part in {".git", ".lake", "__pycache__"} for part in p.relative_to(root).parts)
             and (p.suffix in {".lean", ".py", ".sh", ".toml", ".yml"} or p.name == "lean-toolchain")]
    for path in sorted(paths):
        digest.update(str(path.relative_to(root)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def original_warning_overrides(root):
    bad = []
    for path in root.rglob("*.lean"):
        relative = path.relative_to(root)
        if relative.parts[0] in {".lake", ".git"} or relative.parts[:2] == ("Test", "Negative"):
            continue
        if re.search(r"(?m)^\s*set_option\s+warningAsError\s+false\b", path.read_text()):
            bad.append(str(relative))
    return bad


class VerifyLeanTraversalTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="archiscript-verify-test-")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.root = self.base / "repo"
        self.root.mkdir()
        root_patch = patch.object(verify, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)

    def write(self, relative, content=b"source\n"):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return path

    def symlink(self, relative, target, *, directory=False):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        try:
            path.symlink_to(target, target_is_directory=directory)
        except (NotImplementedError, OSError) as error:
            self.skipTest(f"symlinks unavailable: {error}")
        return path

    def digest_fixture(self):
        included = {
            "z.lean": b"\xff\0\r\n",
            "a.lean": b"same bytes\n",
            "a/first.lean": b"same bytes\n",
            "nested/tool.py": b"print('checked')\n",
            "nested/tool.sh": b"#!/bin/sh\n",
            "lakefile.toml": b"name = 'fixture'\n",
            ".github/workflows/gate.yml": b"on: push\n",
            "lean-toolchain": b"leanprover/lean4:v4.0.0\n",
            "nested/lean-toolchain": b"nested toolchain\n",
            "Test/Negative/Suppressed.lean": b"set_option warningAsError false\n",
            "nested/.lake-other/Kept.lean": b"kept\n",
            "unicodé/é.lean": "-- é\n".encode("utf-8"),
        }
        ignored = [
            ".git/objects/Hidden.lean", ".lake/build/hidden.py", "__pycache__/hidden.sh",
            "nested/.git/hidden.toml", "nested/.lake/hidden.yml",
            "nested/__pycache__/Hidden.lean", "Test/Negative/.lake/Hidden.lean",
            "notes.md", "nested/config.yaml", "Upper.LEAN", ".lean",
        ]
        for name, content in included.items():
            self.write(name, content)
        for name in ignored:
            self.write(name)
        return included, ignored

    def warning_fixture(self):
        included = [
            "Root.lean", "nested/.lake/Warning.lean", "nested/.git/Warning.lean",
            "__pycache__/Warning.lean", "nested/__pycache__/Warning.lean",
            "nested/Test/Negative/Warning.lean", "Test/NegativeExtra/Warning.lean",
            ".lean", ".hidden.lean",
        ]
        ignored = [
            ".git/Warning.lean", ".lake/build/Warning.lean",
            "Test/Negative/Allowed.lean", "Test/Negative/deep/Allowed.lean",
            "other.py", "Other/not-lean.txt",
        ]
        for name in included + ignored:
            self.write(name, b"set_option warningAsError false\n")
        self.write("Other/Good.lean", b"-- set_option warningAsError false\n")
        return included

    def scanned_directories(self, action):
        scanned = []
        scandir = os.scandir

        def record(directory):
            scanned.append(Path(directory).relative_to(self.root))
            return scandir(directory)

        with patch.object(verify.os, "scandir", side_effect=record):
            result = action()
        return result, scanned

    def test_empty_tree(self):
        self.assertEqual(verify.source_digest(), hashlib.sha256().hexdigest())
        self.assertEqual(verify.source_digest(), original_source_digest(self.root))
        self.assertEqual(verify.warning_overrides(), original_warning_overrides(self.root))
        self.assertEqual(verify.warning_overrides(), [])

    def test_digest_preserves_coverage_sorted_paths_and_exact_bytes(self):
        included, _ = self.digest_fixture()
        paths = [Path(name) for name in included]
        # Component-wise Path order differs from sorting path strings here.
        self.assertNotEqual(sorted(paths), sorted(paths, key=str))
        expected = hashlib.sha256()
        for path in sorted(paths):
            expected.update(str(path).encode("utf-8") + b"\0" + included[str(path)] + b"\0")
        self.assertEqual(verify.source_digest(), expected.hexdigest())
        self.assertEqual(verify.source_digest(), original_source_digest(self.root))

    def test_digest_detects_content_and_name_changes_in_every_selected_file(self):
        included, _ = self.digest_fixture()
        before = verify.source_digest()
        for name, content in included.items():
            with self.subTest(name=name, edit="content"):
                path = self.write(name, content + b"changed\0")
                self.assertNotEqual(verify.source_digest(), before)
                self.assertEqual(verify.source_digest(), original_source_digest(self.root))
                path.write_bytes(content)
            with self.subTest(name=name, edit="name"):
                # Keep the basename so extensionless toolchain files stay selected.
                renamed = self.root / "renamed" / name
                renamed.parent.mkdir(parents=True, exist_ok=True)
                path.rename(renamed)
                self.assertNotEqual(verify.source_digest(), before)
                self.assertEqual(verify.source_digest(), original_source_digest(self.root))
                renamed.rename(path)
        self.assertEqual(verify.source_digest(), before)

    def test_digest_ignores_excluded_and_unrelated_file_edits(self):
        _, ignored = self.digest_fixture()
        before = verify.source_digest()
        for name in ignored:
            with self.subTest(name=name):
                self.write(name, b"changed\xff\0")
                self.assertEqual(verify.source_digest(), before)
                self.assertEqual(verify.source_digest(), original_source_digest(self.root))
        (self.root / "nested/config.yaml").rename(self.root / "nested/config.yml")
        self.assertNotEqual(verify.source_digest(), before)
        self.assertEqual(verify.source_digest(), original_source_digest(self.root))

    def test_digest_prunes_excluded_directories_before_scanning(self):
        self.digest_fixture()
        expected = original_source_digest(self.root)
        actual, scanned = self.scanned_directories(verify.source_digest)
        self.assertEqual(actual, expected)
        self.assertIn(Path("."), scanned)
        self.assertIn(Path("nested"), scanned)
        self.assertIn(Path("Test/Negative"), scanned)
        for directory in scanned:
            self.assertFalse({".git", ".lake", "__pycache__"}.intersection(directory.parts),
                             f"scanned excluded directory: {directory}")

    def test_digest_keeps_file_symlinks_without_following_directory_symlinks(self):
        external = self.base / "outside"
        external.mkdir()
        target = external / "source.txt"
        target.write_bytes(b"external\xff\0")
        hidden = external / "Hidden.lean"
        hidden.write_bytes(b"unvisited\n")
        self.symlink("alias.lean", target)
        self.symlink("ignored.txt", hidden)
        self.symlink("lean-toolchain", target)
        self.symlink("directory", external, directory=True)
        self.symlink("directory.lean", external, directory=True)
        self.symlink("loop", self.root, directory=True)
        self.symlink("broken.lean", external / "missing")
        excluded = self.write(".lake/Target.lean", b"excluded target\n")
        self.symlink("from-excluded.lean", excluded)
        expected = original_source_digest(self.root)
        actual, scanned = self.scanned_directories(verify.source_digest)
        self.assertEqual(actual, expected)
        self.assertEqual(scanned, [Path(".")])
        hidden.write_bytes(b"still unvisited\n")
        self.assertEqual(verify.source_digest(), actual)
        for path in (target, excluded):
            with self.subTest(target=path.name):
                before = verify.source_digest()
                path.write_bytes(b"changed target\n")
                self.assertNotEqual(verify.source_digest(), before)
                self.assertEqual(verify.source_digest(), original_source_digest(self.root))

    def test_warning_coverage_and_report_order_match_original(self):
        included = self.warning_fixture()
        actual = verify.warning_overrides()
        self.assertEqual(actual, original_warning_overrides(self.root))
        self.assertCountEqual(actual, included)

    def test_warning_pruning_retains_nested_exclusions_and_negative_lookalikes(self):
        self.warning_fixture()
        expected = original_warning_overrides(self.root)
        actual, scanned = self.scanned_directories(verify.warning_overrides)
        self.assertEqual(actual, expected)
        for directory in (".", "nested/.lake", "nested/.git", "__pycache__",
                          "nested/__pycache__", "nested/Test/Negative", "Test/NegativeExtra"):
            self.assertIn(Path(directory), scanned)
        for directory in scanned:
            self.assertNotIn(directory.parts[:1], ((".git",), (".lake",)))
            self.assertNotEqual(directory.parts[:2], ("Test", "Negative"))

    def test_warning_regex_behavior_matches_original(self):
        cases = [
            (b"set_option warningAsError false\n", True),
            (b"\n\tset_option\n  warningAsError\tfalse -- reason\n", True),
            (b"set_option warningAsError false;\n", True),
            (b"-- set_option warningAsError false\n", False),
            (b"prefix set_option warningAsError false\n", False),
            (b"set_option warningAsError falsehood\n", False),
            (b"set_option warningAsError false_extra\n", False),
            (b"set_option warningAsError true\n", False),
        ]
        for content, matches in cases:
            with self.subTest(content=content):
                self.write("Case.lean", content)
                actual = verify.warning_overrides()
                self.assertEqual(actual, original_warning_overrides(self.root))
                self.assertEqual(actual, ["Case.lean"] if matches else [])

    def test_warning_symlinks_keep_alias_paths_without_directory_traversal(self):
        external = self.base / "outside"
        external.mkdir()
        target = external / "source.txt"
        target.write_text("set_option warningAsError false\n")
        (external / "Hidden.lean").write_text("set_option warningAsError false\n")
        self.symlink("alias.lean", target)
        self.symlink("directory", external, directory=True)
        self.symlink("loop", self.root, directory=True)
        self.assertEqual(verify.warning_overrides(), original_warning_overrides(self.root))
        actual, scanned = self.scanned_directories(verify.warning_overrides)
        self.assertEqual(actual, ["alias.lean"])
        self.assertEqual(set(scanned), {Path(".")})
        self.symlink("broken.lean", external / "missing")
        for action in (lambda: original_warning_overrides(self.root), verify.warning_overrides):
            with self.assertRaises(FileNotFoundError):
                action()

    def test_warning_directory_matches_retain_read_errors(self):
        (self.root / "Directory.lean").mkdir()
        for action in (lambda: original_warning_overrides(self.root), verify.warning_overrides):
            with self.assertRaises(IsADirectoryError):
                action()


if __name__ == "__main__":
    unittest.main()
