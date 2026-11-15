import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lean_negative", Path(__file__).with_name("check-lean-negative.py"))
negative = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(negative)


class NegativeDiagnosticTests(unittest.TestCase):
    source = "-- EXPECT: CONTRACT_AUDIT bad\n-- ONLY_ERROR: CONTRACT_AUDIT\n"

    def test_audit_rejections_alone_are_allowed(self):
        output = "Bad.lean:10:0: error: CONTRACT_AUDIT bad.admissibleInput\n" \
                 "Bad.lean:10:0: error: CONTRACT_AUDIT alias.admissibleEffect\n"
        self.assertEqual(negative.unexpected_errors(self.source, output), [])

    def test_incidental_type_error_cannot_masquerade_as_contract_rejection(self):
        output = "Bad.lean:4:0: error: Unknown identifier `missing`\n" \
                 "Bad.lean:10:0: error: CONTRACT_AUDIT bad\n"
        self.assertEqual(len(negative.unexpected_errors(self.source, output)), 1)
        self.assertIn("Unknown identifier", negative.unexpected_errors(self.source, output)[0])

    def test_admitted_proof_cannot_masquerade_as_contract_rejection(self):
        output = "Bad.lean:10:0: error: CONTRACT_AUDIT bad\n" \
                 "Bad.lean:10:0: error: AXIOM_AUDIT rejected bad: [sorryAx]\n"
        self.assertEqual(len(negative.unexpected_errors(self.source, output)), 1)
        self.assertIn("sorryAx", negative.unexpected_errors(self.source, output)[0])


if __name__ == "__main__":
    unittest.main()
