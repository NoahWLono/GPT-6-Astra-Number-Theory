#!/usr/bin/env python3
"""Exercise the acceptance gate against genuine Lean output, including bad proofs.

The intentionally invalid fixtures are temporary infrastructure tests. They are
never part of the research library or result registry.
"""
from pathlib import Path
import subprocess
import tempfile
import unittest

from audit_axioms import check_declaration, ROOT


class AxiomGateTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory(prefix="gate-test-", dir=ROOT / ".lake") as directory:
            path = Path(directory) / "GateTest.lean"
            path.write_text("""theorem clean : True := True.intro
axiom inventedAssumption : False
theorem contaminated : False := inventedAssumption
theorem unfinished : False := by sorry
theorem classicalExample (p : Prop) : p ∨ ¬p := Classical.em p
#print axioms clean
#print axioms contaminated
#print axioms unfinished
#print axioms classicalExample
""")
            cls.output = subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=ROOT,
                check=True, capture_output=True, text=True).stdout

    def test_accepts_kernel_proof(self):
        check_declaration("clean", self.output)

    def test_accepts_standard_classical_axioms(self):
        check_declaration("classicalExample", self.output)

    def test_rejects_transitive_custom_axiom(self):
        with self.assertRaisesRegex(ValueError, "inventedAssumption"):
            check_declaration("contaminated", self.output)

    def test_rejects_proof_hole(self):
        with self.assertRaisesRegex(ValueError, "sorryAx"):
            check_declaration("unfinished", self.output)

    def test_rejects_missing_declaration(self):
        with self.assertRaisesRegex(ValueError, "Missing axiom output"):
            check_declaration("unregistered", self.output)


if __name__ == "__main__":
    unittest.main()
