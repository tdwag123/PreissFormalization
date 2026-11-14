"""Prevent unfinished or stale proofs from receiving completion colours."""
import unittest
from blueprint_kernel_status import node_status, same_sources
from render_blueprint import annotate_tex


class KernelColors(unittest.TestCase):
    def test_every_declaration_in_a_node_must_be_verified(self):
        records = {"proved": {"axioms": ["propext"]}, "open": {"axioms": ["sorryAx"]}}
        result = node_status(["proved", "open"], records, True)
        self.assertTrue(result["statement_checked"])
        self.assertFalse(result["proof_checked"])
        self.assertFalse(node_status(["missing"], records, True)["proof_checked"])
        self.assertFalse(node_status([], records, True)["proof_checked"])

    def test_new_axioms_and_stale_sources_are_not_green(self):
        records = {"good": {"axioms": ["Classical.choice", "Quot.sound"]},
                   "bad": {"axioms": ["extraAxiom"]}}
        self.assertTrue(node_status(["good"], records, True)["proof_checked"])
        self.assertFalse(node_status(["good"], records, False)["proof_checked"])
        self.assertFalse(node_status(["bad"], records, True)["proof_checked"])

    def test_dependency_changes_invalidate_the_snapshot(self):
        old = {"Main.lean": b"same\r\n", "Dependency.lean": b"old"}
        self.assertTrue(same_sources(old, {"Main.lean": b"same\n", "Dependency.lean": b"old"}))
        self.assertFalse(same_sources(old, {"Main.lean": b"same\n", "Dependency.lean": b"new"}))
        self.assertFalse(same_sources(old, {**old, "New.lean": b"new"}))

    def test_completed_theorem_without_prose_proof_gets_a_proof_marker(self):
        source = r"\begin{theorem}\label{done}\lean{good}Text.\end{theorem}"
        result = annotate_tex(source, {"done": {"statement_checked": True, "proof_checked": True}})
        self.assertEqual(result.count(r"\leanok"), 2)
        self.assertIn(r"\begin{proof}", result)

    def test_old_handwritten_markers_cannot_certify_an_unfinished_proof(self):
        source = (r"\begin{lemma}\label{open}\leanok Text.\end{lemma}"
                  r"\begin{proof}[Sketch]\leanok Old claim.\end{proof}")
        result = annotate_tex(source, {"open": {"statement_checked": True, "proof_checked": False}})
        self.assertEqual(result.count(r"\leanok"), 1)  # Compiled statement only.
        self.assertNotIn(r"\leanok", result.split(r"\begin{proof}")[1])
        stale = annotate_tex(source, {"open": {"statement_checked": False, "proof_checked": False}})
        self.assertNotIn(r"\leanok", stale)


if __name__ == "__main__":
    unittest.main()
