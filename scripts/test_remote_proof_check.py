from pathlib import Path
import tempfile
import unittest

from remote_proof_check import audit, candidate


class ProofCheckTests(unittest.TestCase):
    def test_standard_report(self):
        self.assertEqual(audit(["T"], "'T' depends on axioms: [propext, Quot.sound]"),
                         {"T": ["Quot.sound", "propext"]})

    def test_missing_report(self):
        with self.assertRaises(ValueError):
            audit(["T"], "")

    def test_forbidden_dependency(self):
        for axiom in ["sorryAx", "unprovedLemma"]:
            with self.assertRaises(ValueError):
                audit(["T"], f"'T' depends on axioms: [{axiom}]")

    def test_path_restriction(self):
        with self.assertRaises(ValueError):
            candidate("checks/../../secret.lean")

    def test_source_policy(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "checks").mkdir()
            path = root / "checks" / "Test.lean"
            for body in ["axiom T : True", "theorem T : True := by sorry"]:
                path.write_text("import Mathlib.Tactic\n" + body, encoding="utf-8")
                with self.assertRaises(ValueError):
                    candidate("checks/Test.lean", root)
            path.write_text("import Mathlib.Tactic\nnamespace Example\n"
                            "theorem T : True := by trivial\nend Example", encoding="utf-8")
            _, names, modules = candidate("checks/Test.lean", root)
            self.assertEqual(names, ["Example.T"])
            self.assertEqual(modules, ["Mathlib.Tactic"])


if __name__ == "__main__":
    unittest.main()
