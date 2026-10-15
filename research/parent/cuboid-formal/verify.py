#!/usr/bin/env python3
"""Freshly compile the supporting quintic proof and audit its transitive axioms."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SOURCE = Path("research/parent/cuboid-formal")
sys.path.insert(0, str(ROOT / "scripts"))
from audit_axioms import check_declaration

PARENT_MODULES = {
    "ParityObstruction": [
        "constant_zero_of_mod_two_divisor",
        "no_two_three_integral_factorization",
    ],
    "GaussTransfer": [
        "integral_divisor_of_rational_divisor",
        "rational_quadratic_divisor_integral_factorization",
    ],
    "IntegralQuintic": [
        "integralQuintic_natDegree",
        "integralQuintic_mod_two",
        "integralQuintic_constant_not_four_dvd",
        "odd_half_sum_squares",
        "twice_half_sum_squares",
    ],
    "QuinticExclusion": [
        "integralQuintic_no_quadratic",
        "transformedQuintic_no_quadratic",
        "odd_odd_transformedQuintic_no_quadratic",
        "odd_odd_ratio_transformedQuintic_no_quadratic",
    ],
}

BATCH_MODULES = {
    "CuboidIdentities": ["P_at_neg_s", "T_comp", "inverse_v_cleared", "inverse_w_cleared"],
    "FactorDegreeTransfer": ["factor_degree_transfer"],
    "CuboidEquivalence": ["tEquivG", "tEquivP", "pEquivG", "quadratic_factor_transfer"],
    "OddOddExclusion": ["odd_odd_P_no_quadratic"],
}


def main():
    (ROOT / ".local").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cuboid-check-", dir=ROOT / ".local") as cache:
        env = os.environ.copy()
        env["LEAN_PATH"] = cache + os.pathsep + env.get("LEAN_PATH", "")
        groups = [
            (SOURCE, "CuboidResearch", PARENT_MODULES),
            (Path("research/batch-a"), "NumberTheoryResearch.BatchA.Cuboid", BATCH_MODULES),
        ]
        for source, namespace, modules in groups:
            out = Path(cache) / source
            out.mkdir(parents=True)
            for module, declarations in modules.items():
                run = subprocess.run(
                    ["lean", "-j1", "-o", str(out / f"{module}.olean"), str(source / f"{module}.lean")],
                    cwd=ROOT, env=env, text=True, capture_output=True, timeout=600,
                )
                print(run.stdout, end="", flush=True)
                if run.stderr:
                    print(run.stderr, end="", file=sys.stderr, flush=True)
                run.check_returncode()
                for name in declarations:
                    check_declaration(f"{namespace}.{name}", run.stdout)
    print("Fresh compilation and axiom checks passed for the odd/odd cuboid restriction.")
    print("The opposite-parity case, full conjecture, and novelty remain unresolved here.")


if __name__ == "__main__":
    main()
