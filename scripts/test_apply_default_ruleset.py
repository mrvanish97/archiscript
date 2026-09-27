"""Exercise remote parsing with local git/gh stubs; no GitHub request is sent."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().with_name("apply-default-ruleset.sh")


class RulesetRemoteTests(unittest.TestCase):
    def run_with_remote(self, remote):
        with tempfile.TemporaryDirectory() as temporary:
            bin_dir = Path(temporary)
            git = bin_dir / "git"
            git.write_text('#!/bin/sh\nprintf "%s\\n" "$FAKE_REMOTE"\n')
            git.chmod(0o755)
            gh = bin_dir / "gh"
            gh.write_text('''#!/bin/sh
if [ "$1" = "repo" ]; then exit 1; fi
if [ "$1" = "api" ] && [ "$2" = "--method" ]; then
  printf '%s\\n' "$4" > "$API_LOG"
fi
''')
            gh.chmod(0o755)
            log = bin_dir / "api.log"
            result = subprocess.run(["bash", str(SCRIPT)], capture_output=True,
                                    text=True, env={**os.environ,
                                                    "PATH": f"{bin_dir}:{os.environ['PATH']}",
                                                    "FAKE_REMOTE": remote,
                                                    "API_LOG": str(log)})
            return result, log.read_text().strip() if log.exists() else None

    def test_supported_github_remote_forms(self):
        for remote in ("git@github.com:owner/project.git", "git@github.com:owner/project",
                       "https://github.com/owner/project.git",
                       "https://github.com/owner/project"):
            with self.subTest(remote=remote):
                result, api_path = self.run_with_remote(remote)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(api_path, "repos/owner/project/rulesets")

    def test_other_host_is_rejected_before_api(self):
        result, api_path = self.run_with_remote("git@example.com:owner/project.git")
        self.assertEqual(result.returncode, 64)
        self.assertIsNone(api_path)


if __name__ == "__main__":
    unittest.main()
