import importlib.util
import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
from unittest.mock import patch
import unittest


MODULE_PATH = Path(__file__).with_name("build-review-pack.py")
SPEC = importlib.util.spec_from_file_location("build_review_pack", MODULE_PATH)
review_pack = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(review_pack)


class ReviewPackTests(unittest.TestCase):
    def test_revision_covers_review_contract_without_circular_approval(self):
        projection = {"model": "M", "checkedClaims": [{"claim": "proved"}]}
        review = {"state": "approved", "approval": {"reviewer": "A", "revision": "old"},
                  "boundary": {"description": "original"},
                  "assumptions": [{"statement": "stable"}], "effectNotes": []}
        revision = review_pack.model_revision(projection, review, "checked-sources")
        review["approval"]["revision"] = revision
        self.assertEqual(revision, review_pack.model_revision(projection, review, "checked-sources"))
        self.assertTrue(review_pack.approval_status({**review, "findings": []}, revision))
        for key, value in (("boundary", {"description": "changed"}),
                           ("assumptions", [{"statement": "unknown"}]),
                           ("effectNotes", [{"statement": "new effect"}])):
            altered = copy.deepcopy(review)
            altered[key] = value
            self.assertNotEqual(revision, review_pack.model_revision(
                projection, altered, "checked-sources"), key)
        self.assertNotEqual(revision, review_pack.model_revision(
            {**projection, "checkedClaims": []}, review, "checked-sources"))

    def test_python_approval_agrees_with_lean(self):
        subprocess.run(["lake", "build", "ArchiScript.Review"],
                       cwd=review_pack.ROOT, capture_output=True, text=True, check=True)
        result = subprocess.run(["lake", "env", "lean", "--run",
                                 "scripts/approval-agreement.lean"], cwd=review_pack.ROOT,
                                capture_output=True, text=True, check=True)
        cases = [("approved", "engineer", "v1", "addressed"),
                 ("approved", "engineer", "v2", "addressed"),
                 ("approved", "engineer", "", "addressed"),
                 ("approved", "", "v1", "addressed"),
                 ("approved", "engineer", "v1", "open"),
                 ("draft", "engineer", "v1", "addressed"),
                 ("approved", "engineer", "v1", "accepted")]
        python = [review_pack.approval_status({
            "state": state, "approval": {"reviewer": reviewer, "revision": revision},
            "findings": [{"disposition": disposition}]}, "v1")
            for state, reviewer, revision, disposition in cases]
        self.assertEqual(json.loads(result.stdout), python)

    def test_projection_builds_import_before_export(self):
        calls = []
        def run(command, **_kwargs):
            calls.append(command)
            return type("Result", (), {"stdout": json.dumps({"model": "fresh"})})()
        with patch.object(review_pack.subprocess, "run", side_effect=run):
            self.assertEqual(review_pack.projection_from_lean()["model"], "fresh")
        self.assertEqual(calls[0][:3], ["lake", "build", "ArchiScriptExamples.PaymentWebhook"])
        self.assertEqual(calls[1][:4], ["lake", "env", "lean", "--run"])

    def test_export_rebuilds_changed_input_region_in_isolated_project(self):
        with tempfile.TemporaryDirectory(prefix="archiscript-export-test-") as temporary:
            root = Path(temporary)
            for name in (*review_pack.MODEL_SOURCES,
                         "scripts/export-payment-review.lean", "lakefile.toml",
                         "lean-toolchain"):
                destination = root / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(review_pack.ROOT / name, destination)
            with patch.object(review_pack, "ROOT", root):
                original = review_pack.projection_from_lean()
                model = root / "ArchiScriptExamples/PaymentWebhook.lean"
                text = model.read_text()
                description = original["inputRegions"][0]["description"]
                self.assertIn(description, text)
                model.write_text(text.replace(description, "Changed region description", 1))
                revised = review_pack.projection_from_lean()
                self.assertEqual(revised["inputRegions"][0]["description"],
                                 "Changed region description")
                self.assertNotEqual(original["inputRegions"], revised["inputRegions"])

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
        projection = {"model": "M", "objects": [{"id": "M.Input", "kind": "carrier"}],
                      "semanticPartitions": [], "topology": [], "mappingCoverage": []}
        review = {
            "model": "M", "state": "draft", "boundary": {"subject": "M.Input"},
            "assumptions": [], "effectNotes": [], "questions": [],
            "findings": [{"id": "RV-1", "subject": "M.Missing", "disposition": "open"}],
        }
        with self.assertRaisesRegex(ValueError, "unknown review subject"):
            review_pack.validate_review(projection, review)

    def test_review_generation_rejects_unnamed_defined_mappings(self):
        subprocess.run(["lake", "build", "ArchiScriptExamples.UserRegistration"],
                       cwd=review_pack.ROOT, capture_output=True, text=True, check=True)
        result = subprocess.run(["lake", "env", "lean", "--run",
                                 "scripts/export-omitted-mapping-fixture.lean"],
                                cwd=review_pack.ROOT, capture_output=True,
                                text=True, check=True)
        missing_count = json.loads(result.stdout)
        self.assertEqual(missing_count, 3)
        projection = review_pack.projection_from_lean()
        review = json.loads(review_pack.REVIEW_SOURCE.read_text())
        projection["mappingCoverage"][0]["missingDefinedMappings"] = missing_count
        with self.assertRaisesRegex(ValueError, "defined mappings lack named branches"):
            review_pack.validate_review(projection, review)

    def test_review_requires_semantic_evidence_for_each_partition(self):
        projection = review_pack.projection_from_lean()
        review = json.loads(review_pack.REVIEW_SOURCE.read_text())
        review_pack.validate_review(projection, review)
        self.assertIn('subgraph INPUT["inputPartition"]',
                      "\n".join(review_pack.mermaid_decide_branches(projection)))
        self.assertIn(r"\begin{tikzpicture}",
                      review_pack.tikz_decide_branches(projection))
        altered = copy.deepcopy(projection)
        altered["semanticPartitions"].pop()
        with self.assertRaisesRegex(ValueError, "semantic member evidence"):
            review_pack.validate_review(altered, review)

    def test_review_rejects_missing_carrier_provenance(self):
        projection = review_pack.projection_from_lean()
        review = json.loads(review_pack.REVIEW_SOURCE.read_text())
        altered = copy.deepcopy(projection)
        altered["architecturalPartitions"].pop()
        with self.assertRaisesRegex(ValueError, "carrier provenance"):
            review_pack.validate_review(altered, review)
        altered = copy.deepcopy(projection)
        altered["architecturalPartitions"][0]["carrierProvenance"]["revision"] = ""
        with self.assertRaisesRegex(ValueError, "external carrier guarantee"):
            review_pack.validate_review(altered, review)
        altered = copy.deepcopy(projection)
        altered["architecturalPartitions"][0]["carrierProvenance"] = {
            "status": "derived-contract", "upstream": "M.upstream",
            "sourceMember": "M.upstream.accepted"}
        with self.assertRaisesRegex(ValueError, "no upstream provenance"):
            review_pack.validate_review(altered, review)

    def test_opaque_member_remains_valid_and_visible(self):
        projection = review_pack.projection_from_lean()
        review = json.loads(review_pack.REVIEW_SOURCE.read_text())
        altered = copy.deepcopy(projection)
        definition = altered["architecturalPartitions"][0]["members"][0]["definition"]
        definition.clear()
        definition.update({"status": "opaque", "reason": "upstream predicate has no formula"})
        review_pack.validate_review(altered, review)
        self.assertIn("upstream predicate has no formula",
                      review_pack.markdown_pack(altered, review, "test", [], False))
        self.assertNotEqual(review_pack.model_revision(projection, review, "sources"),
                            review_pack.model_revision(altered, review, "sources"))
        definition["reason"] = ""
        with self.assertRaisesRegex(ValueError, "opaque subdomain needs a reason"):
            review_pack.validate_review(altered, review)

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
        self.assertEqual(changes, [
            "projection.decideBranches[M.decide.success].target: 'fulfill' → 'acknowledgeDuplicate'"])

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
        self.assertTrue(any("review.findings[RV-1]" in change and "ledger race" in change
                            for change in changes))

    def test_diff_covers_exported_removals_and_finding_edits(self):
        previous = {"model": "M", "inputMembers": [], "decisionMembers": [],
                    "ledgerMembers": [], "inputRegions": [], "decideBranches": [],
                    "ledgerBranches": [], "ledgerMappings": [],
                    "checkedClaims": [{"claim": "proof"}]}
        current = {**previous, "checkedClaims": []}
        prior_review = {"boundary": {"subject": "M", "description": "old"},
                        "assumptions": [], "effectNotes": [], "questions": [],
                        "findings": [{"id": "F", "subject": "M", "concern": "old",
                                      "requestedChange": "old", "disposition": "open"}]}
        for field in ("subject", "concern", "requestedChange"):
            revised = copy.deepcopy(prior_review)
            revised["findings"][0][field] = "changed"
            changes = review_pack.semantic_changes(previous, previous, revised, prior_review)
            self.assertEqual(len(changes), 1)
            self.assertTrue(any(f"review.findings[F].{field}" in item for item in changes), field)
        changes = review_pack.semantic_changes(current, previous, prior_review, prior_review)
        self.assertTrue(any("projection.checkedClaims" in item for item in changes))
        self.assertFalse(any("No semantic changes" in item for item in changes))

        old_binding = {"status": "resolved", "binding": {
            "primary": {"repository": "r", "path": "a", "symbol": None},
            "supporting": [{"repository": "r", "path": "support", "symbol": None}]}}
        old_branch = {"id": "M.op.b", "source": "a", "target": "b",
                      "responsibility": [], "implementation": old_binding}
        revised_branch = copy.deepcopy(old_branch)
        revised_branch["implementation"]["binding"]["supporting"] = []
        changes = review_pack.semantic_changes(
            {**previous, "decideBranches": [revised_branch]},
            {**previous, "decideBranches": [old_branch]})
        self.assertTrue(any("implementation.binding.supporting" in item for item in changes))

    def test_semantic_diff_ignores_reordering_of_named_entries(self):
        branches = [{"id": "M.a", "source": "a", "target": "x"},
                    {"id": "M.b", "source": "b", "target": "y"}]
        findings = [{"id": "F1", "subject": "M.a", "concern": "one"},
                    {"id": "F2", "subject": "M.b", "concern": "two"}]
        previous = {"decideBranches": branches,
                    "checkedClaims": [{"proof": "one", "claim": "one"},
                                      {"proof": "two", "claim": "two"}]}
        current = {"decideBranches": list(reversed(branches)),
                   "checkedClaims": list(reversed(previous["checkedClaims"]))}
        review = {"findings": findings}
        reordered_review = {"findings": list(reversed(findings))}
        self.assertEqual(review_pack.semantic_changes(current, previous,
                                                      reordered_review, review),
                         ["No semantic changes detected in the exported projection or review contract."])


if __name__ == "__main__":
    unittest.main()
