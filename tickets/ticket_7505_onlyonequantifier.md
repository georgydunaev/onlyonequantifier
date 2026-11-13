# [ONLYONEQUANTIFIER] Ticket 7505 - onlyonequantifier: Add Automated Formula Simplification Test Suite

**Repository:** `onlyonequantifier`  
**Assigned AI Model:** `opencode/glm-5.3-flash-free`  
**Harness:** `opencode`  
**Status:** `RESOLVED`  
**Created:** `2026-10-27T22:48:44Z`  
**Resolved:** `2026-11-13T23:15:00Z`  

## Task Description
Implement comprehensive unit tests verifying validity preservation across random first-order formulas.

## Execution Guidelines
1. Work autonomously in `onlyonequantifier/`.
2. Ensure existing tests continue to pass.
3. For math and foundations repos, keep modifications cosmetic, clean, and adhere to sound formal reasoning.
4. Run tests with local test runner before concluding.

## Resolution Notes
1. Implemented property-based test suite in `tests/test_onlyonequantifier.py` (`TestPropertyBasedSimplificationAndTruthPreservation`):
   - Generates randomized quantifier-free first-order formulas with arbitrary combinations of connectives and relations.
   - Verifies 100% truth-value preservation across random valuations between original formulas, `simplify`, `to_nnf`, and `to_dnf`.
   - Verifies truth preservation for DLO quantifier elimination on dense domains over real/rational valuations.
2. Implemented unit tests covering:
   - AST operations, terms, predicates, and capture-avoiding substitutions.
   - Constant folding, idempotent absorption, cycle detection, and normal forms.
   - Prenex normal form decomposition and fresh variable renaming.
   - DLO quantifier elimination on standard DLO axioms (density, no endpoints, irreflexivity, trichotomy) and open formulas with free variables.
3. All 25 tests pass with a 100% success rate (`python3 -m unittest discover tests`).
