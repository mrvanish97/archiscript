import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch


MODULE_PATH = Path(__file__).with_name("build-webhook-network-showcase.py")
SPEC = importlib.util.spec_from_file_location("webhook_network_showcase", MODULE_PATH)
showcase = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(showcase)


class NetworkShowcaseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        snapshot = json.loads((showcase.OUTPUT / "PaymentWebhookNetwork.snapshot.json").read_text())
        cls.projection = snapshot["projection"]
        cls.review = snapshot["review"]

    def test_all_exported_endpoints_and_review_subjects_are_addressable(self):
        showcase.validate(self.projection, self.review)
        altered = json.loads(json.dumps(self.projection))
        altered["topology"][0]["target"] = "missingPartition"
        with self.assertRaisesRegex(ValueError, "not a selected VDP"):
            showcase.validate(altered, self.review)

    def test_branch_view_changes_with_exported_mapping(self):
        before = "\n".join(showcase.mermaid_notification_map(self.projection))
        self.assertIn('subgraph DECISION["decisionPartition"]', before)
        self.assertIn('subgraph NOTIFICATION["notificationPartition"]', before)
        self.assertIn('S4 -->|"planNotification"| U', before)
        altered = json.loads(json.dumps(self.projection))
        duplicate = next(item for item in altered["notificationMappings"]
                         if item["source"] == "acknowledgeDuplicate")
        duplicate["target"] = "successReceipt"
        after = "\n".join(showcase.mermaid_notification_map(altered))
        self.assertIn('S4 -->|"planNotification"| T1', after)
        self.assertNotEqual(before, after)

    def test_missing_named_mapping_rejects_network_review(self):
        altered = json.loads(json.dumps(self.projection))
        altered["mappingCoverage"][0]["missingDefinedMappings"] = 1
        with self.assertRaisesRegex(ValueError, "defined mappings lack named branches"):
            showcase.validate(altered, self.review)

    def test_missing_carrier_origin_rejects_network_review(self):
        altered = json.loads(json.dumps(self.projection))
        altered["architecturalPartitions"].pop()
        with self.assertRaisesRegex(ValueError, "carrier provenance"):
            showcase.validate(altered, self.review)


class NamedDefinitionTests(unittest.TestCase):
    def test_named_opaque_boundary_keeps_its_reason(self):
        named = {"status": "named", "name": "external region", "parts": [
            {"status": "opaque", "reason": "supplied external semantics"}]}
        showcase.validate_definition(named, "region")
        self.assertEqual(showcase.opaque_reasons(named), ["supplied external semantics"])
        named["parts"][0]["reason"] = ""
        with self.assertRaises(ValueError):
            showcase.validate_definition(named, "region")

    def test_named_definition_cannot_hide_missing_evidence(self):
        with self.assertRaises(ValueError):
            showcase.validate_definition({"status": "named", "parts": []}, "region")


class RevisionBindingTests(unittest.TestCase):
    def test_approval_does_not_change_the_revision_it_approves(self):
        before = showcase.revision({}, {"scope": "model", "state": "draft"}, "sources")
        self.assertEqual(before, showcase.revision({}, {
            "scope": "model", "state": "approved", "approval": {"revision": before}}, "sources"))
        self.assertNotEqual(before, showcase.revision({}, {"scope": "changed"}, "sources"))
        self.assertNotEqual(before, showcase.revision({}, {"scope": "model"}, "changed sources"))

    def test_changed_sources_during_export_reject_the_pack(self):
        with patch.object(showcase, "source_fingerprint", side_effect=["before", "after"]), \
                patch.object(showcase, "export_projection", return_value={}):
            with self.assertRaisesRegex(RuntimeError, "sources changed"):
                showcase.main()


if __name__ == "__main__":
    unittest.main()
