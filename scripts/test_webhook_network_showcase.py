import importlib.util
import json
from pathlib import Path
import unittest


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
        self.assertIn('S4 -->|"planNotification"| T0', before)
        altered = json.loads(json.dumps(self.projection))
        duplicate = next(item for item in altered["notificationMappings"]
                         if item["source"] == "acknowledgeDuplicate")
        duplicate["target"] = "successReceipt"
        after = "\n".join(showcase.mermaid_notification_map(altered))
        self.assertIn('S4 -->|"planNotification"| T2', after)
        self.assertNotEqual(before, after)


if __name__ == "__main__":
    unittest.main()
