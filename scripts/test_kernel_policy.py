"""Regression tests for the no-new-axioms/no-new-unfinished-proofs CI gate."""
import unittest
from check_kernel_axioms import check


class KernelPolicyTests(unittest.TestCase):
    def report(self, axioms, baseline, kind="theorem"):
        metadata = {"test": {"project": "local", "kind": kind,
                             "source_status": "proof_candidate"}}
        return check(metadata, {"test": axioms}, baseline=baseline)[1]

    def test_new_proof_with_standard_foundations_passes(self):
        self.assertEqual(self.report(["propext", "Classical.choice", "Quot.sound"], {}), [])

    def test_new_transitively_unfinished_proof_fails(self):
        self.assertTrue(self.report(["sorryAx"], {}))

    def test_proved_declaration_cannot_regress(self):
        self.assertTrue(self.report(["sorryAx"], {"test": {"axioms": ["propext"]}}))

    def test_known_open_obligation_remains_explicit(self):
        self.assertEqual(self.report(["sorryAx"], {"test": {"axioms": ["sorryAx"]}}), [])

    def test_nonstandard_axiom_always_fails(self):
        self.assertTrue(self.report(["Preiss.assume_the_result"], {}))

    def test_definitions_cannot_depend_on_unfinished_proofs(self):
        self.assertTrue(self.report(["sorryAx"], {"test": {"axioms": ["sorryAx"]}}, kind="def"))


if __name__ == "__main__":
    unittest.main()
