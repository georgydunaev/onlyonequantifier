#!/usr/bin/env python3
"""Verification tests for onlyonequantifier (my_IFOL.thy and quantifier duality)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestOnlyOneQuantifier(unittest.TestCase):
    def test_my_ifol_theory_structure(self):
        thy = os.path.join(ROOT, "my_IFOL.thy")
        self.assertTrue(os.path.isfile(thy))
        with open(thy, encoding="utf-8") as f:
            content = f.read()
        self.assertIn("theory", content)
        self.assertIn("end", content)

    def test_classical_quantifier_interdefinability(self):
        domain = [0, 1, 2, 3]
        predicates = [
            lambda x: True,
            lambda x: False,
            lambda x: x % 2 == 0,
            lambda x: x > 1,
        ]
        for p in predicates:
            forall_p = all(p(x) for x in domain)
            not_exists_not_p = not any(not p(x) for x in domain)
            self.assertEqual(forall_p, not_exists_not_p)


if __name__ == "__main__":
    unittest.main()
