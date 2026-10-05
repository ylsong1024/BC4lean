# Chapter 4 verification

Verified on 2026-10-05 against Lean 4.33.1 and the unchanged dependency manifest
(Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`).

All 71 mathematical blueprint nodes in `04-proper-actions.tex` have checked Lean
links and verified markers. All 236 distinct linked declarations were checked
and axiom-audited against the completed project aggregate. No Chapter 4 target
remains marked `\notready`.

The weak labeled join has a genuine finite-isotropy equivariant CW structure,
a proper action, contractible finite-subgroup fixed spaces and empty
infinite-subgroup fixed spaces for every discrete group. Its cellular mapping
and equivariant homotopy uniqueness properties are proved.

For a countable discrete group, the same concrete geometric telescope has a
genuine CW structure, proper action, local compactness, second countability and
the full fixed-point criterion. The CW structure is transported through the
proved equivariant homeomorphism from the staircase prism subcomplex. It uses
actual orbit-disk pushouts and the actual skeletal colimit. Fixed contraction
uses compact finite-stage control and a continuous height majorant, rather than
an assumed global height section on the weak join.

The final witness is
`BC4lean.ProperActions.LabeledOrbitTelescope.universalProperCWModel`;
`homotopyTerminal` and `unique` in the same namespace give its universal mapping
and homotopy uniqueness properties. Invariant-subspace inclusion laws and the
fixed orbit-cell product homeomorphism also complete roadmap tasks C4-01/C4-02.

Validation:

- Every changed Lean module passed strict compilation with
  `lake env lean -DwarningAsError=true`.
- All 138 project modules are imported exactly once:
  `python3 scripts/check_project_imports.py`.
- A sequential dependency-order Lake build, followed by the prescribed
  `lake --wfail build BC4lean`, passed (3,436 jobs in the aggregate build).
- All 236 blueprint links passed `#check` and `#print axioms`. Additional public
  construction declarations were audited separately, including all 66 allowed
  CW declarations, 133 prism declarations and the final model witnesses.
- The only reported axioms are the existing standard logical foundations
  `propext`, `Classical.choice` and `Quot.sound`; no new axioms, `sorry` or
  `admit` were introduced.
- `python3 build_web.py` passed for the final blueprint source, without warnings
  or errors. Generated HTML is not committed.

This verifies Chapter 4's stated scope. Equivariant KK-theory and the assembly
construction remain subsequent chapters; the general Baum–Connes conjecture
is not claimed proved.
