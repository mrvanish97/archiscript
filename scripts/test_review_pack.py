import importlib.util
from pathlib import Path
import unittest


MODULE_PATH = Path(__file__).with_name("build-review-pack.py")
SPEC = importlib.util.spec_from_file_location("build_review_pack", MODULE_PATH)
review_pack = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(review_pack)


class ReviewPackTests(unittest.TestCase):
    def test_approval_requires_matching_revision_and_closed_findings(self):
        record = {
            "state": "approved",
            "approval": {"reviewer": "engineer", "revision": "v1"},
            "findings": [{"disposition": "addressed"}],
        }
        self.assertTrue(review_pack.approval_status(record, "v1"))
        self.assertFalse(review_pack.approval_status(record, "v2"))
        record["findings"][0]["disposition"] = "open"
        self.assertFalse(review_pack.approval_status(record, "v1"))
        record["findings"][0]["disposition"] = "accepted"
        record["state"] = "changes-requested"
        self.assertFalse(review_pack.approval_status(record, "v1"))

    def test_findings_must_reference_model_objects(self):
        projection = {"model": "M", "objects": [{"id": "M.Input", "kind": "carrier"}]}
        review = {
            "model": "M", "state": "draft", "boundary": {"subject": "M.Input"},
            "assumptions": [], "effectNotes": [], "questions": [],
            "findings": [{"id": "RV-1", "subject": "M.Missing", "disposition": "open"}],
        }
        with self.assertRaisesRegex(ValueError, "unknown review subject"):
            review_pack.validate_review(projection, review)

    def test_semantic_diff_reports_changed_branch_target(self):
        branch = {
            "id": "M.decide.success", "source": "success", "target": "fulfill",
            "responsibility": ["payments"],
            "implementation": {"status": "planned", "binding": {
                "primary": {"repository": "repo", "path": "a.ts", "symbol": "handle"}}},
        }
        previous = {
            "inputMembers": ["success"], "decisionMembers": ["fulfill"],
            "ledgerMembers": [], "inputRegions": [], "decideBranches": [branch],
            "ledgerBranches": [], "ledgerMappings": [],
        }
        current = {**previous, "decideBranches": [{**branch, "target": "acknowledgeDuplicate"}]}
        changes = review_pack.semantic_changes(current, previous)
        self.assertIn("M.decide.success target: fulfill → acknowledgeDuplicate", changes)

    def test_review_diff_reports_new_finding_and_changed_assumption(self):
        projection = {
            "inputMembers": [], "decisionMembers": [], "ledgerMembers": [],
            "inputRegions": [], "decideBranches": [], "ledgerBranches": [],
            "ledgerMappings": [],
        }
        prior_review = {
            "boundary": {"subject": "M.Input", "description": "old"},
            "assumptions": [{"subject": "M.Input", "statement": "snapshot is stable"}],
            "effectNotes": [], "questions": [], "findings": [],
        }
        revised_review = {
            **prior_review,
            "assumptions": [{"subject": "M.Input", "statement": "snapshot stability unknown"}],
            "findings": [{"id": "RV-1", "concern": "ledger race", "disposition": "open"}],
        }
        changes = review_pack.semantic_changes(
            projection, projection, revised_review, prior_review)
        self.assertTrue(any("snapshot stability unknown" in change for change in changes))
        self.assertIn("New review finding RV-1: ledger race", changes)


if __name__ == "__main__":
    unittest.main()
