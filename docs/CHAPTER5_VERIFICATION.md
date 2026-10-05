# Chapter 5: first verified milestone

Verified on 2026-10-05 with Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The toolchain, Lake configuration,
and dependency manifest are unchanged. All ten local package commits match
the manifest. Baseline: `ac1a7a58dd2928e00b23a46a246ebc956e105c9f`.

## Mathematical scope

This milestone provides ungraded right pre-Hilbert module foundations over a
possibly nonunital complex C*-algebra B, bounded adjointable maps, and rank-one
module operators. Completeness is not required by these identities. The
standard module B_B is checked as a complete example.

We use `CStarModule Bᵐᵒᵖ E`. Right multiplication x b is `op b • x`, and the
usual B-valued inner product is the unop of Mathlib's inner product. In the
standard module this gives exactly x* y; rank-one operators act by left
multiplication by x y*. This opposite-algebra convention is essential for
noncommutative coefficients.

The adjoint is unique. Adjointable complex-linear maps are automatically
B-linear, are closed under addition, complex scaling and composition, and
satisfy the identity, associativity, involution and reversed-composition laws.
Rank-one operators satisfy the norm bound, adjoint formula, and left/right
composition formulas. Their range need not be finite-dimensional over C.

## Pinned API inventory

- `Mathlib.Analysis.CStarAlgebra.Module.Defs`: `CStarModule`, coefficient-valued
  inner products, `CStarModule.norm_sq_eq`, `CStarModule.norm_inner_le`, and
  `CStarModule.innerSL`.
- `Mathlib.Analysis.CStarAlgebra.Module.Constructions`: self, product and finite
  family modules; the standard module uses the self construction on Bᵐᵒᵖ.
- `LinearMap.mkContinuous` and `ContinuousLinearMap.comp`: bounded map
  construction, composition and operator norm.
- The pinned tree has Hilbert-space adjoints and rank-one operators, but no
  general adjointable C*-module-map API. The three new modules fill this bounded
  part of that gap without replacing the existing Hilbert-module class.

## Verification

All three new modules compiled individually with the pinned Lean executable,
`-j 2 -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false`,
explicit `LEAN_PATH` to the pinned compiled packages, and `-R`/`-o` for the
checked snapshot. Reproducible repository commands are:

```sh
python3 scripts/check_project_imports.py
lake --wfail build BC4lean
lake env lean -DwarningAsError=true BC4lean/HilbertCStarModule.lean
lake env lean -DwarningAsError=true BC4lean/AdjointableOperator.lean
lake env lean -DwarningAsError=true BC4lean/RankOneOperator.lean
```

When reproducing individual checks in a fresh checkout, build the imported new
modules first so their .olean files are available. The full Lake build covers
all modules and the changed aggregate. Its result was:

`Build completed successfully (3439 jobs).`

All 44 named declarations listed below passed `#check` and
`#print axioms`. Only `Classical.choice`, `Quot.sound`, `propext` were reported.
No `sorry`, `admit`, or new axioms were introduced. All final individual
compilations and the full build passed without warnings.

`python3 build_web.py` passed with no warnings or errors, producing all eight
chapter graphs and the overall graph. Seven precise new Chapter 5 nodes have
checked Lean links and verified markers. The four broader original targets
remain `\notready`. Rendering is separate from Lean verification.

## Remaining work

The next bounded milestone is the normed *-algebra of adjointable endomorphisms
and the operator-norm closure of the span of rank-one maps, with its adjoint
and two-sided ideal properties. In particular, adjoint norm preservation and
closedness/completeness must be proved before treating the operator algebra as
fully constructed. Grading, compatible group actions, Kasparov cycles,
homotopy, KK groups, the Kasparov product and the comparison with operator
K-theory remain unverified. Chapter 5 is not complete.

## Exact declarations checked

All names are in `BC4lean.KKTheory` (with the `AdjointableMap` subnamespace
where shown):

- `BC4lean.KKTheory.module_inner_ext_left`
- `BC4lean.KKTheory.module_inner_ext_right`
- `BC4lean.KKTheory.module_add_smul`
- `BC4lean.KKTheory.module_smul_add`
- `BC4lean.KKTheory.module_mul_smul`
- `BC4lean.KKTheory.module_complex_smul`
- `BC4lean.KKTheory.module_norm_smul_le`
- `BC4lean.KKTheory.standard_module_inner`
- `BC4lean.KKTheory.standard_module_complete`
- `BC4lean.KKTheory.AdjointableMap`
- `BC4lean.KKTheory.AdjointableMap.instCoeFun`
- `BC4lean.KKTheory.AdjointableMap.adjoint_unique`
- `BC4lean.KKTheory.AdjointableMap.ext`
- `BC4lean.KKTheory.AdjointableMap.map_op_smul`
- `BC4lean.KKTheory.AdjointableMap.adjoint`
- `BC4lean.KKTheory.AdjointableMap.adjoint_adjoint`
- `BC4lean.KKTheory.AdjointableMap.zero`
- `BC4lean.KKTheory.AdjointableMap.zero_apply`
- `BC4lean.KKTheory.AdjointableMap.adjoint_zero`
- `BC4lean.KKTheory.AdjointableMap.id`
- `BC4lean.KKTheory.AdjointableMap.id_apply`
- `BC4lean.KKTheory.AdjointableMap.adjoint_id`
- `BC4lean.KKTheory.AdjointableMap.comp`
- `BC4lean.KKTheory.AdjointableMap.comp_apply`
- `BC4lean.KKTheory.AdjointableMap.adjoint_comp`
- `BC4lean.KKTheory.AdjointableMap.id_comp`
- `BC4lean.KKTheory.AdjointableMap.comp_id`
- `BC4lean.KKTheory.AdjointableMap.comp_assoc`
- `BC4lean.KKTheory.AdjointableMap.add`
- `BC4lean.KKTheory.AdjointableMap.add_apply`
- `BC4lean.KKTheory.AdjointableMap.adjoint_add`
- `BC4lean.KKTheory.AdjointableMap.smul`
- `BC4lean.KKTheory.AdjointableMap.smul_apply`
- `BC4lean.KKTheory.AdjointableMap.adjoint_smul`
- `BC4lean.KKTheory.moduleRankOneCLM`
- `BC4lean.KKTheory.moduleRankOneCLM_apply`
- `BC4lean.KKTheory.moduleRankOne`
- `BC4lean.KKTheory.moduleRankOne_apply`
- `BC4lean.KKTheory.moduleRankOne_adjoint`
- `BC4lean.KKTheory.moduleRankOne_norm_le`
- `BC4lean.KKTheory.comp_moduleRankOne`
- `BC4lean.KKTheory.moduleRankOne_comp`
- `BC4lean.KKTheory.moduleRankOne_comp_moduleRankOne`
- `BC4lean.KKTheory.standard_moduleRankOne`
