"""Regression checks for proof-status reporting and placeholder policy."""
from pathlib import Path
import unittest
from lean_source import parse_source, audit_records, mask_noncode, project_audit
from tempfile import TemporaryDirectory
from check_kernel_axioms import parse_axioms, check
from lean_targets import module_targets


class SourceChecks(unittest.TestCase):
    def audit(self, source):
        return audit_records(parse_source(source, Path("Fixture.lean")))

    def test_public_namespaces_and_default_arguments(self):
        result = self.audit("""
module
@[expose] public section
namespace Preiss
public def sample (n : Nat := 0) : Nat := n
section
public theorem missing : sample = sample := by sorry
end
theorem assembled : sample = sample := missing
end Preiss
""")
        self.assertEqual(set(result), {"Preiss.sample", "Preiss.missing", "Preiss.assembled"})
        self.assertIn("(n : Nat := 0)", result["Preiss.sample"].signature)
        self.assertEqual(result["Preiss.missing"].source_status, "unproved_statement")
        self.assertEqual(result["Preiss.assembled"].source_status, "depends_on_unproved")
        self.assertEqual(result["Preiss.sample"].source_status, "definition")

    def test_nested_comments_and_strings_do_not_create_obligations(self):
        result = self.audit('''/- outer /- axiom fake : False -/ sorry -/
def message : String := "sorry -- axiom /- not a comment"
theorem ready : True := by trivial
''')
        self.assertEqual(result["ready"].source_status, "proof_candidate")
        self.assertFalse(result["message"].direct_sorry)

    def test_definition_and_type_placeholders_rejected(self):
        for source in ["def bad : Nat := by sorry",
                       "theorem bad : (by sorry) := by trivial",
                       "instance : Inhabited Nat := by sorry",
                       "axiom bad : False"]:
            with self.subTest(source=source), self.assertRaises(AssertionError):
                self.audit(source)

    def test_transitive_obligations_cross_namespaces(self):
        result = self.audit("""
namespace A
theorem first : True := by sorry
theorem second : True := first
end A
namespace B
theorem third : True := A.second
def usesProof : Subtype (fun _ : Nat => True) := ⟨0, A.second⟩
end B
""")
        self.assertEqual(result["B.third"].source_status, "depends_on_unproved")
        self.assertEqual(result["B.usesProof"].source_status, "definition_depends_on_unproved")

    def test_root_names_and_structure(self):
        result = self.audit("""
namespace A
structure Piece where
  value : Nat
theorem _root_.outside : True := by trivial
end A
""")
        self.assertIn("A.Piece", result)
        self.assertIn("outside", result)

    def test_other_command_placeholder_is_rejected(self):
        with TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "Preiss").mkdir()
            (root / "Preiss/Bad.lean").write_text(
                "theorem fine : True := by trivial\n#check (show Nat from by sorry)\n", encoding="utf-8")
            with self.assertRaises(AssertionError):
                project_audit(root)


class TargetChecks(unittest.TestCase):
    def test_unimported_canonical_modules_are_built(self):
        with TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "Preiss/New").mkdir(parents=True)
            (root / "Preiss.lean").write_text("-- no imports\n")
            (root / "Preiss/New/NotInUmbrella.lean").write_text("-- standalone\n")
            self.assertEqual(module_targets(root),
                             ["FormalizingGMT", "Preiss", "Preiss.New.NotInUmbrella"])


class KernelChecks(unittest.TestCase):
    def test_actual_transitive_sorry_overrides_source_candidate(self):
        text = "'Preiss.assembled' depends on axioms: [propext,\n sorryAx, Classical.choice, Quot.sound]"
        records, failures = check(
            {"Preiss.assembled": {"project": "local", "kind": "theorem", "source_status": "proof_candidate"}},
            parse_axioms(text))
        self.assertFalse(failures)
        self.assertEqual(records["Preiss.assembled"]["kernel_status"], "depends_on_sorry")

    def test_definition_sorry_and_extra_axiom_fail(self):
        for kind, used in [("def", ["sorryAx"]), ("theorem", ["Untrusted.fact"])]:
            records, failures = check({"bad": {"project": "local", "kind": kind}}, {"bad": used})
            self.assertTrue(failures)

    def test_primed_name_and_no_axioms(self):
        reports = parse_axioms("'Preiss.empty' depends on axioms: [propext]\n'Preiss.empty2' does not depend on any axioms\n'Preiss.helper\'' depends on axioms: [Classical.choice]")
        self.assertEqual(reports["Preiss.empty2"], [])
        self.assertEqual(reports["Preiss.helper'"], ["Classical.choice"])

    def test_missing_report_is_not_success(self):
        with self.assertRaises(AssertionError):
            check({"missing": {"project": "local", "kind": "theorem"}}, {})


if __name__ == "__main__":
    unittest.main()
