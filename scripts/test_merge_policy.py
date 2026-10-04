"""Keep the repository merge policy and CI gate in executable agreement."""

import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
RULESET = ROOT / ".github" / "rulesets" / "default.json"
WORKFLOW = ROOT / ".github" / "workflows" / "pr-gate.yml"


class MergePolicyTests(unittest.TestCase):
    def setUp(self):
        self.ruleset = json.loads(RULESET.read_text())
        self.workflow = WORKFLOW.read_text()

    def test_default_branch_requires_pr_gate(self):
        required = [
            rule for rule in self.ruleset["rules"]
            if rule["type"] == "required_status_checks"
        ]
        self.assertEqual(len(required), 1)
        parameters = required[0]["parameters"]
        self.assertTrue(parameters["strict_required_status_checks_policy"])
        contexts = {
            check["context"] for check in parameters["required_status_checks"]
        }
        self.assertIn("pr-gate", contexts)

    def test_pull_request_review_is_required(self):
        pull_request = next(
            rule for rule in self.ruleset["rules"] if rule["type"] == "pull_request"
        )
        parameters = pull_request["parameters"]
        self.assertGreaterEqual(parameters["required_approving_review_count"], 1)
        self.assertTrue(parameters["require_code_owner_review"])
        self.assertEqual(parameters["allowed_merge_methods"], ["squash"])

    def test_workflow_runs_required_commands(self):
        for command in (
            "lake build",
            "bash scripts/check-negative.sh",
            "lake env lean skills/archiscript/examples/CurrentApi.lean",
            'python -m unittest discover -s scripts -p "test_*.py"',
            "node --test examples/payment-webhook.test.mjs",
        ):
            with self.subTest(command=command):
                self.assertIn(command, self.workflow)

    def test_workflow_exposes_required_context(self):
        self.assertIn("name: pr-gate", self.workflow)
        self.assertIn("pull_request:", self.workflow)
        self.assertIn("branches: [main]", self.workflow)


if __name__ == "__main__":
    unittest.main()
