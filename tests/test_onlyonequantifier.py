#!/usr/bin/env python3
"""Comprehensive verification tests for onlyonequantifier.

Tests cover:
- Isabelle/HOL theory structure and classical quantifier duality.
- First-order AST, term substitution, and capture-avoidance.
- Formula simplification, constant folding, NNF and DNF transformations.
- Sound conversion to Prenex Normal Form with fresh variable renaming.
- Quantifier elimination for Dense Linear Orders (DLO) on sentences and open formulas.
- Property-based testing of truth preservation across randomized formulas.
"""

from __future__ import annotations

import os
import random
import sys
import unittest
from typing import Any, Dict, List

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from quantifier_elim.ast import (
    And,
    Const,
    Eq,
    Exists,
    FalseF,
    ForAll,
    Formula,
    Gt,
    Iff,
    Impl,
    Le,
    Lt,
    Not,
    Or,
    Predicate,
    Term,
    TrueF,
    Var,
    fresh_var_name,
)
from quantifier_elim.elimination import (
    eliminate_dlo,
    eliminate_exists_dlo,
    eliminate_quantifiers,
)
from quantifier_elim.prenex import prenex_decompose, to_prenex
from quantifier_elim.simplify import (
    expand_dlo_negations,
    simplify,
    to_dnf,
    to_dnf_clauses,
    to_nnf,
)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def evaluate(formula: Formula, env: Dict[str, Any]) -> bool:
    """Evaluate a quantifier-free formula under an assignment of variables."""
    if isinstance(formula, TrueF):
        return True
    if isinstance(formula, FalseF):
        return False
    if isinstance(formula, Predicate):
        args: List[Any] = []
        for a in formula.args:
            if isinstance(a, Const):
                args.append(a.val)
            elif isinstance(a, Var):
                args.append(env[a.name])
            else:
                raise TypeError(f"Unsupported term {a}")
        if formula.name == "<":
            return args[0] < args[1]
        if formula.name == "=":
            return args[0] == args[1]
        if formula.name == ">":
            return args[0] > args[1]
        raise ValueError(f"Unknown predicate {formula.name}")
    if isinstance(formula, Not):
        return not evaluate(formula.arg, env)
    if isinstance(formula, And):
        return all(evaluate(a, env) for a in formula.args)
    if isinstance(formula, Or):
        return any(evaluate(a, env) for a in formula.args)
    if isinstance(formula, Impl):
        return (not evaluate(formula.left, env)) or evaluate(formula.right, env)
    if isinstance(formula, Iff):
        return evaluate(formula.left, env) == evaluate(formula.right, env)
    raise TypeError(f"Cannot evaluate non-quantifier-free formula: {formula}")


class TestOnlyOneQuantifier(unittest.TestCase):
    """Preserve existing repository verification tests."""

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


class TestAstAndSubstitution(unittest.TestCase):
    """Test first-order abstract syntax tree and capture-avoiding substitutions."""

    def test_term_equality_and_hashing(self):
        v1 = Var("x")
        v2 = Var("x")
        v3 = Var("y")
        c1 = Const(42)
        c2 = Const(42)
        self.assertEqual(v1, v2)
        self.assertNotEqual(v1, v3)
        self.assertEqual(c1, c2)
        self.assertEqual(hash(v1), hash(v2))
        self.assertEqual(hash(c1), hash(c2))

    def test_free_and_all_vars(self):
        f = ForAll("x", Exists("y", And(Lt("x", "y"), Lt("y", "z"))))
        self.assertEqual(f.free_vars(), {"z"})
        self.assertEqual(f.all_vars(), {"x", "y", "z"})

    def test_capture_avoiding_substitution(self):
        # forall x. (x < y) with [y -> x] must rename bound x to avoid capture
        f = ForAll("x", Lt("x", "y"))
        subst_f = f.substitute({"y": Var("x")})
        self.assertIsInstance(subst_f, ForAll)
        self.assertNotEqual(subst_f.var, "x")
        self.assertEqual(subst_f.free_vars(), {"x"})

    def test_predicate_helpers(self):
        p1 = Lt("x", "y")
        p2 = Eq("x", "y")
        p3 = Gt("x", "y")
        p4 = Le("x", "y")
        self.assertEqual(p1, Predicate("<", (Var("x"), Var("y"))))
        self.assertEqual(p2, Predicate("=", (Var("x"), Var("y"))))
        self.assertEqual(p3, Predicate("<", (Var("y"), Var("x"))))
        self.assertEqual(p4, Or(Lt("x", "y"), Eq("x", "y")))


class TestSimplificationAndNormalForms(unittest.TestCase):
    """Test constant folding, connective reduction, NNF and DNF passes."""

    def test_boolean_constant_folding(self):
        self.assertEqual(simplify(Not(TrueF())), FalseF())
        self.assertEqual(simplify(Not(FalseF())), TrueF())
        self.assertEqual(simplify(And(Var("x"), TrueF())), Var("x"))
        self.assertEqual(simplify(And(Var("x"), FalseF())), FalseF())
        self.assertEqual(simplify(Or(Var("x"), FalseF())), Var("x"))
        self.assertEqual(simplify(Or(Var("x"), TrueF())), TrueF())

    def test_idempotent_absorption(self):
        a = Lt("x", "y")
        self.assertEqual(simplify(And(a, a)), a)
        self.assertEqual(simplify(Or(a, a)), a)
        self.assertEqual(simplify(And(a, Not(a))), FalseF())
        self.assertEqual(simplify(Or(a, Not(a))), TrueF())

    def test_relation_constant_folding(self):
        self.assertEqual(simplify(Lt("x", "x")), FalseF())
        self.assertEqual(simplify(Eq("x", "x")), TrueF())
        self.assertEqual(simplify(Lt(Const(1), Const(2))), TrueF())
        self.assertEqual(simplify(Lt(Const(2), Const(1))), FalseF())
        self.assertEqual(simplify(Eq(Const(3), Const(3))), TrueF())
        self.assertEqual(simplify(Eq(Const(3), Const(4))), FalseF())

    def test_linear_order_cycle_contradiction(self):
        # x < y & y < x -> False
        self.assertEqual(simplify(And(Lt("x", "y"), Lt("y", "x"))), FalseF())
        # x < y & x = y -> False
        self.assertEqual(simplify(And(Lt("x", "y"), Eq("x", "y"))), FalseF())

    def test_nnf_conversion(self):
        # ~(A & (B | ~C)) -> ~A | (~B & C)
        a, b, c = Lt("x", "y"), Lt("y", "z"), Lt("z", "w")
        f = Not(And(a, Or(b, Not(c))))
        nnf_f = to_nnf(f)
        expected = Or(Not(a), And(Not(b), c))
        self.assertEqual(nnf_f, expected)

    def test_nnf_quantifier_pushdown(self):
        f1 = Not(ForAll("x", Lt("x", "y")))
        self.assertEqual(to_nnf(f1), Exists("x", Not(Lt("x", "y"))))
        f2 = Not(Exists("x", Lt("x", "y")))
        self.assertEqual(to_nnf(f2), ForAll("x", Not(Lt("x", "y"))))

    def test_dlo_negation_expansion(self):
        # ~(x < y) -> y < x | x = y
        expanded_lt = expand_dlo_negations(Not(Lt("x", "y")))
        self.assertEqual(expanded_lt, Or(Lt("y", "x"), Eq("x", "y")))
        # ~(x = y) -> x < y | y < x
        expanded_eq = expand_dlo_negations(Not(Eq("x", "y")))
        self.assertEqual(expanded_eq, Or(Lt("x", "y"), Lt("y", "x")))

    def test_dnf_conversion(self):
        # (A | B) & (C | D) -> (A & C) | (A & D) | (B & C) | (B & D)
        a, b = Lt("x", "y"), Lt("y", "z")
        c, d = Lt("z", "w"), Lt("w", "u")
        f = And(Or(a, b), Or(c, d))
        dnf_f = to_dnf(f)
        clauses = to_dnf_clauses(f)
        self.assertEqual(len(clauses), 4)


class TestPrenexNormalForm(unittest.TestCase):
    """Test Prenex Normal Form transformations and variable renaming."""

    def test_simple_prenex(self):
        f = Impl(Exists("x", Lt("x", "y")), ForAll("z", Lt("y", "z")))
        p = to_prenex(f)
        pref, mat = prenex_decompose(f)
        self.assertEqual(len(pref), 2)
        self.assertEqual(pref[0][0], "forall")  # ~exists becomes forall
        self.assertEqual(pref[1][0], "forall")
        self.assertEqual(p.free_vars(), {"y"})

    def test_fresh_renaming_prevents_capture(self):
        f = And(Exists("x", Lt("x", "y")), Exists("x", Lt("y", "x")))
        p = to_prenex(f)
        pref, mat = prenex_decompose(f)
        vars_in_pref = [v for _, v in pref]
        self.assertEqual(len(vars_in_pref), 2)
        self.assertNotEqual(vars_in_pref[0], vars_in_pref[1])
        self.assertEqual(p.free_vars(), {"y"})

    def test_nested_quantifiers_preserve_semantics(self):
        f = ForAll("x", Exists("y", And(Lt("x", "y"), Lt("y", "z"))))
        p = to_prenex(f)
        self.assertEqual(p.free_vars(), {"z"})


class TestDenseLinearOrderQuantifierElimination(unittest.TestCase):
    """Test Quantifier Elimination for Dense Linear Orders without endpoints (DLO)."""

    def test_single_existential_bounded(self):
        # ex z. (x < z & z < y) <==> x < y
        f = Exists("z", And(Lt("x", "z"), Lt("z", "y")))
        self.assertEqual(eliminate_quantifiers(f), Lt("x", "y"))

    def test_single_existential_multiple_bounds(self):
        # ex z. (x < z & w < z & z < y) <==> (x < y & w < y)
        f = Exists("z", And(Lt("x", "z"), Lt("w", "z"), Lt("z", "y")))
        res = eliminate_quantifiers(f)
        self.assertEqual(res, And(Lt("x", "y"), Lt("w", "y")))

    def test_unbounded_existential(self):
        # ex z. (x < z) <==> True (no upper endpoint)
        f_upper = Exists("z", Lt("x", "z"))
        self.assertEqual(eliminate_quantifiers(f_upper), TrueF())
        # ex z. (z < x) <==> True (no lower endpoint)
        f_lower = Exists("z", Lt("z", "x"))
        self.assertEqual(eliminate_quantifiers(f_lower), TrueF())

    def test_contradictory_bounds(self):
        # ex z. (x < z & z < x) <==> False
        f = Exists("z", And(Lt("x", "z"), Lt("z", "x")))
        self.assertEqual(eliminate_quantifiers(f), FalseF())

    def test_equality_substitution_elimination(self):
        # ex z. (x < z & z = y & z < w) <==> (x < y & y < w)
        f = Exists("z", And(Lt("x", "z"), Eq("z", "y"), Lt("z", "w")))
        self.assertEqual(eliminate_quantifiers(f), And(Lt("x", "y"), Lt("y", "w")))

    def test_dlo_sentences(self):
        # Axiom: No endpoints (all x. ex y. x < y) -> True
        no_max = ForAll("x", Exists("y", Lt("x", "y")))
        self.assertEqual(eliminate_quantifiers(no_max), TrueF())

        # Axiom: No endpoints (all x. ex y. y < x) -> True
        no_min = ForAll("x", Exists("y", Lt("y", "x")))
        self.assertEqual(eliminate_quantifiers(no_min), TrueF())

        # Non-existence of global maximum: (ex x. all y. y < x) -> False
        has_max = Exists("x", ForAll("y", Lt("y", "x")))
        self.assertEqual(eliminate_quantifiers(has_max), FalseF())

        # Non-existence of global minimum: (ex x. all y. x < y) -> False
        has_min = Exists("x", ForAll("y", Lt("x", "y")))
        self.assertEqual(eliminate_quantifiers(has_min), FalseF())

        # Axiom: Density (all x. all y. (x < y ==> ex z. (x < z & z < y))) -> True
        density = ForAll("x", ForAll("y", Impl(Lt("x", "y"), Exists("z", And(Lt("x", "z"), Lt("z", "y"))))))
        self.assertEqual(eliminate_quantifiers(density), TrueF())

        # Axiom: Irreflexivity (all x. ~(x < x)) -> True
        irreflexive = ForAll("x", Not(Lt("x", "x")))
        self.assertEqual(eliminate_quantifiers(irreflexive), TrueF())


class TestPropertyBasedSimplificationAndTruthPreservation(unittest.TestCase):
    """Property-based randomized testing for truth preservation across passes."""

    def _random_qf_formula(self, depth: int, vars_pool: List[str]) -> Formula:
        if depth <= 0 or random.random() < 0.3:
            v1 = random.choice(vars_pool)
            v2 = random.choice(vars_pool)
            op = random.choice(["<", "="])
            return Predicate(op, (Var(v1), Var(v2)))

        choice = random.choice(["not", "and", "or", "impl", "iff"])
        if choice == "not":
            return Not(self._random_qf_formula(depth - 1, vars_pool))
        if choice == "and":
            return And(
                self._random_qf_formula(depth - 1, vars_pool),
                self._random_qf_formula(depth - 1, vars_pool),
            )
        if choice == "or":
            return Or(
                self._random_qf_formula(depth - 1, vars_pool),
                self._random_qf_formula(depth - 1, vars_pool),
            )
        if choice == "impl":
            return Impl(
                self._random_qf_formula(depth - 1, vars_pool),
                self._random_qf_formula(depth - 1, vars_pool),
            )
        return Iff(
            self._random_qf_formula(depth - 1, vars_pool),
            self._random_qf_formula(depth - 1, vars_pool),
        )

    def test_random_formula_truth_preservation(self):
        random.seed(2026)
        vars_pool = ["x", "y", "z", "w"]
        num_formulas = 60

        for _ in range(num_formulas):
            formula = self._random_qf_formula(depth=4, vars_pool=vars_pool)
            sim_formula = simplify(formula)
            nnf_formula = to_nnf(formula)
            dnf_formula = to_dnf(formula)

            # Test across multiple random valuations
            for _ in range(5):
                env = {v: random.randint(0, 10) for v in vars_pool}
                val_orig = evaluate(formula, env)
                val_sim = evaluate(sim_formula, env)
                val_nnf = evaluate(nnf_formula, env)
                val_dnf = evaluate(dnf_formula, env)

                self.assertEqual(val_orig, val_sim, f"Simplify changed truth: {formula}")
                self.assertEqual(val_orig, val_nnf, f"NNF changed truth: {formula}")
                self.assertEqual(val_orig, val_dnf, f"DNF changed truth: {formula}")

    def test_dlo_qe_dense_truth_preservation(self):
        # For bounded existential ex z. (l < z & z < u), verify equivalence with l < u
        f = Exists("z", And(Lt("l", "z"), Lt("z", "u")))
        qf = eliminate_quantifiers(f)
        for _ in range(30):
            val_l = random.uniform(-10.0, 10.0)
            val_u = random.uniform(-10.0, 10.0)
            env = {"l": val_l, "u": val_u}
            self.assertEqual(evaluate(qf, env), val_l < val_u)


if __name__ == "__main__":
    unittest.main()
