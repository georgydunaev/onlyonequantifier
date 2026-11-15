# Project Overview: Minimal Intuitionistic First-Order Logic and Quantifier Definability (`onlyonequantifier`)

## 1. Purpose and Scope
`onlyonequantifier` (`/botworkspace/onlyonequantifier`) investigates minimal quantifier and connective bases in Intuitionistic and Classical First-Order Logic using Isabelle/Pure (`my_IFOL.thy`, `UniquenessAndSingleBinder.thy`) and Python quantifier-elimination verifiers (`quantifier_elim/`).

## 2. Key Files and Structure
- [my_IFOL.thy](file:///botworkspace/onlyonequantifier/my_IFOL.thy) — Isabelle/Pure theory developing Intuitionistic First-Order Logic, natural deduction introduction/elimination rules, and quantifier equivalences.
- [UniquenessAndSingleBinder.thy](file:///botworkspace/onlyonequantifier/UniquenessAndSingleBinder.thy) — Isabelle formalization of unique existence (`∃!`), single-binder reductions, and quantifier duality laws.
- `quantifier_elim/` — Executable Python modules verifying quantifier definability, prenex normal form conversions, and quantifier elimination over decidable fragments.
- [MANUSCRIPT_AND_PROOF_INDEX.md](file:///botworkspace/onlyonequantifier/MANUSCRIPT_AND_PROOF_INDEX.md) and [PROOF_COMPLETIONS_AND_EXTENSIONS.md](file:///botworkspace/onlyonequantifier/PROOF_COMPLETIONS_AND_EXTENSIONS.md) — Complete theorem and lemma catalog.
- `tests/` — Automated unit test suite.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/onlyonequantifier/tests -p "test_*.py"
```
