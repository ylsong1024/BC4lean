# Chapter 5 verification record

**Core proof, build and blueprint checks passed on 2026-10-13.** Scope: equivariant KK groups, Kasparov product laws and natural comparisons `KK_i(ℂ,B) ≃ K_i(B)` for `i=0,1`. Supplemental execution/publication checks were pending at this record’s freeze boundary; their actual outcomes are indexed externally.

The project has 809 Lean modules. The [Chapter 5 blueprint](../blueprint/src/parts/05-equivariant-kk.tex) has 75 blocks (17 definitions, 58 propositions), 435 distinct Lean links, and 18/72/16 required endpoints for its three main targets. The complete-ready core audit checked every required endpoint; all three main targets are ready.

## Publication status — 2026-10-14 12:42 UTC

This publication records the completed Chapter 5 core results and the current supplemental progress. It does not certify completion of the supplemental final verification or exact-revision publication CI.

The completed core checks cover all 809 modules: the strict full build (4201 jobs), warnings-as-errors cached build, 21 audit safeguards, all 809 imports, all 435 blueprint links, 75 blueprint blocks (17 definitions and 58 propositions), and the complete 18/72/16 required endpoints. The kernel census covers 18,199 declarations in 686 modules and reports exactly `Classical.choice`, `Quot.sound`, and `propext`. The ready-blueprint render exited 0. All 206 original Lean sources and the Chapter 4 record remain unchanged.

The supplemental full native replay remains **incomplete**: 78 of 149 actual native executions exited 0, and all 78 checkpoints are authenticated; 71 executions remain. The independent metadata comparison is complete within its stated scope. The compiler IR structural inventory is complete as an inventory; its global semantic-verification claim remains false. Final runtime checks, full R6 checks, the final supplemental certificate, and this publication's exact-revision CI have not passed yet.

The earlier replay worker (42996, supervisor 42995) was interrupted at 11:12 UTC after an owned wait returned 1 because the 60-second frozen-input check raised `TimeoutError`; all 69 continuation checkpoints plus the original nine were retained. The reviewed continuation (worker 30818, supervisor 30817), launched at 11:46 UTC, was healthy while requalifying the 78 checkpoints and all 149 setups in preflight; no Lean compiler had started at that observed boundary. Required Source E files (264) and original Out files (56) were restored from offload with their original hashes, without source changes. These process statements describe those observed boundaries rather than a later execution result.

This dated note was created only in a separate publication checkout. Its document hash differs from the verifier's frozen record, so the earlier frozen 819-input supplemental binding does not cover this published document. The five retained core audit artifacts are copied with their exact original bytes. The active verification Stage and user checkout were left untouched; subsequent outcomes must be recorded with their actual input and revision bindings.

## Mathematical scope

| Result | Main anchors |
| --- | --- |
| Full even/odd equivariant abelian groups | [Full homotopy](../BC4lean/FullGradedKasparovHomotopy.lean); [parity groups](../BC4lean/GroupUniverseParityGroup.lean): `KKParityGroup`, parity identifications |
| Product existence/uniqueness and all-parity bilinearity/associativity | [Existence](../BC4lean/KasparovProductExistence.lean); [uniqueness](../BC4lean/KasparovProductOperatorUniqueness.lean); [product laws](../BC4lean/GroupUniverseCommonParityProduct.lean): `productAddHom`, `product_assoc` |
| Nonunital units and functoriality | [Units](../BC4lean/GroupUniverseParityUnits.lean): `identity`, `left_identity`, `right_identity`; [functoriality](../BC4lean/GroupUniverseParityFunctoriality.lean): `sourcePullbackHom`, `coefficientPushforwardHom`, identity/composition/product laws |
| Ordinary K₀/K₁ equivalences, inverses and naturality | [K₀ comparison](../BC4lean/ScalarKasparovK0ComparisonAddEquiv.lean): `scalarKKOperatorK0AddEquiv`; [K₀ naturality](../BC4lean/ScalarKasparovK0ComparisonNaturality.lean): `scalarKKOperatorK0AddEquiv_natural`; [K₁ comparisons](../BC4lean/GroupUniverseOddFullComparison.lean): `oddKKOperatorK1AllModuleUniversesAddEquiv`, Clifford comparison; [K₁ naturality](../BC4lean/OddKTheoryIndependentCoefficientNaturality.lean): `oddKKOperatorK1AllModuleUniversesAddEquiv_independentCoefficient_natural` |

Names use `BC4lean.KKTheory` and the indicated subnamespace; full endpoint sets are required.

Applications use separable, possibly nonunital complex algebras and countable groups; raw headers remain broader. Independent group/coefficient/module universes and required tensor maxima are retained. Full homotopies use arbitrary completed interval modules/fibres. Ordinary comparisons use `PUnit`, `ℂ`, trivial actions and any module universe, even below the coefficient universe. Countable generation and coefficient separability supply the small module representatives used in universe transport; no `Small B` assumption is added.

Genuine Hilbert norms/completions, countable generation and header-permitted zero algebras, degenerate maps and empty finite indices are retained, without extra unitality/faithfulness/essentiality/nontriviality assumptions.

The [correspondence quotient](../BC4lean/GroupUniverseCompactCorrespondenceProduct.lean) requires `[SeparableSpace C]` for its target, as the full quotient does; [raw constructions](../BC4lean/GradedCompactCorrespondenceCycle.lean) remain broader. No nonseparable quotient extension is claimed. All four direct caller sites already assume separability of `C` (and `A` for the last two). Write `M(C)=CStarMatrix (Fin 2) (Fin 2) C`, which is separable for separable `C`:

| Actual caller in `GroupUniverseMatrixMoritaProduct` | Coefficient/type scope |
| --- | --- |
| [columnClass](../BC4lean/GroupUniverseMatrixMoritaProduct.lean#L21) | Full graded `KK(M(C),C)`, module universe `uC`; quotient target `C`. |
| [rowClass](../BC4lean/GroupUniverseMatrixMoritaProduct.lean#L31) | Full graded `KK(C,M(C))`, module universe `uC`; target `M(C)`. |
| [toCoefficientClass_eq_product](../BC4lean/GroupUniverseMatrixMoritaProduct.lean#L45) | `KK(A,M(C)) → KK(A,C)`, module universe `uE → max uE uC`; actual column product. |
| [toMatrixClass_eq_product](../BC4lean/GroupUniverseMatrixMoritaProduct.lean#L61) | `KK(A,C) → KK(A,M(C))`, module universe `uE → max uE uC`; actual row product. |

Both comparison inverses are explicit: K₀ `nonunitalRelativeK0KasparovMapAtUniverse_leftInverse` in the comparison file above and [`nonunitalRelativeK0KasparovMapAtUniverse_rightInverse`](../BC4lean/ScalarKasparovK0IndexUniverse.lean); K₁ [`oddOperatorK1KKInverseAllModuleUniverses_leftInverse_index` and `rightInverse_index`](../BC4lean/OddKTheoryModuleUniverseIndex.lean).

## Corrections and preservation

Reference: [Echterhoff, arXiv:1703.10912v2](https://arxiv.org/pdf/1703.10912v2). Printed `M,N ≥ 1`, `M+N=1` is inconsistent in a nonzero algebra. The intended partition has `0 ≤ M,N ≤ 1`, `M+N=1` and positive roots `m²+n²=1`. The [technical theorem](../BC4lean/KasparovDiscreteTechnicalTheorem.lean) constructs it, allowing zero algebras.

Creation `θξ : F → E ⊗Ψ F` is bounded/adjointable; compactness needs the appropriate compact-left-action condition. The [completed infinite-dimensional counterexample](../BC4lean/InteriorCreationCycleCounterexample.lean) disproves unconditional compactness. False printed claims are not verification targets. The general Baum–Connes conjecture is not proved here.

Preservation covers the [Chapter 4 record](CHAPTER4_VERIFICATION.md), verified at `ac1a7a58dd2928e00b23a46a246ebc956e105c9f`, and literal identity of all 206 original sources plus that record with base `02acce56d13e1ca45c3c2952b1bda521a05de7ae`.

`docs/CHAPTER5_CHECKPOINT.json` remains historical: the incomplete 775/809 checkpoint at `2dcd28c2da6517a8ec62ae0861106c46cb850feb`. These are historical acceptance counts.

## Core validation

The retained [core audit](audits/chapter5/core-audit.json) has SHA256 `91ac3a554e069b28fdf9697f893ee00046bd967139e9a0d0913f01767cada4f1`. The [core evidence index](audits/chapter5/core-evidence.json) binds actual build/check/render records and the exact [kernel source](audits/chapter5/Chapter5Audit.lean), [raw output](audits/chapter5/kernel-stdout-stderr.log) and [run record](audits/chapter5/kernel-run.json).

| Check | Actual result |
| --- | --- |
| `lake --wfail build BC4lean` | Exit0; full aggregate covers 809 modules. Initial full build: 4201 jobs; six-EOF-cleaned rebuild: exit0. |
| `lake --wfail --no-build --no-cache build BC4lean` | Exit0; all 809 sources and 810 module/aggregate objects held unchanged between strict/cached checks. The ready-blueprint audit’s cached gate also exited0. |
| `python3 -B scripts/test_audit_chapter5.py`; `python3 -B scripts/check_project_imports.py` | Exit0: 21 safeguards; all 809 modules imported exactly once. |
| `python3 -B scripts/audit_chapter5.py --require-complete` | Exit0 at 06:22:22 UTC; all 435 links and 18/72/16 required endpoints; `chapter_complete=true`, pending=[] in this core audit. |
| Uncapped module-origin declaration/axiom census | 18,199 declarations in 686 Chapter 5/prerequisite modules, including private/generated declarations and other namespaces. Exactly `Classical.choice`, `Quot.sound`, `propext`; no forbidden source tokens. |
| Mathematical source/context/universe/caller scope | Reviewed genuine quotient/product/tensor/index constructions, explicit reference corrections and the caller/inverse scope above. Core source/object bindings held. Independent compiled expected TYPE/DATA VALUE checks remain supplemental. |
| `(cd blueprint/src && python3 -B build_web.py)` | Exit0 at 06:36:57 UTC; no warning/error lines; tracked blueprint inputs unchanged. Generated `web.paux`/web output is accounted separately. |
| Preservation, `git diff --check`, proof-trust/secret scans | Literal identity of 206 original sources plus Chapter 4 record with the preservation base; diff exit0 with empty output; cleaned 809-source proof/secret scans clear. |
| Toolchain and manifest | Lean 4.33.1 arm64, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Actual toolchain/manifest and audit inputs are hash-bound. |

The audit retains 817 mathematical/build/blueprint source hashes and 810 object hashes. Every source-map entry can be checked directly against committed file bytes. This document and the historical checkpoint are not inputs to that core source map; neither its own hash nor its containing commit is used to certify it. Raw kernel acceptance and core readiness are distinct from the supplemental final certificate. The latter requalifies all ten final controls and the broader runtime boundary after the record is frozen.

## Supplemental methods and external evidence

Final checks bind mathematical sources, ready blueprint, this record and all ten controls. External receipt destination:

`/Users/yanlisong/Documents/Codex/2026-10-05/task-2/chapter5-recovery-20261008T1503/CHAPTER5_FINAL_VERIFICATION_EVIDENCE_20261013/INDEX.json`

The index binds receipt hashes, sources/controls/objects, actual exits and obligations. These destinations do not assert existing certificates:

| Result index | Required scope |
| --- | --- |
| `INDEPENDENT_METADATA.json` | Compile reviewed written-source expected TYPE/DATA VALUEs before target comparison; reconcile every seed/member and full binders/dictionaries/universes/kinds. |
| `COMPLETE_FAMILIES.json` | Whole original/clone name-delta census: uncapped private/generated TYPE/VALUE/dependencies/axioms, no omissions/target aliases. |
| `FULL_R6.json` | Complete expressions, full 14-row/11-capture R6 and historical coverage. Reject missing/truncated output; historical counts are floors, not caps. |
| `COMPILER_IR_ABI.json` | Actual IR/references/generated names/aliases and ABI for 809 modules plus aggregate. Classify unavailable scope; inventory does not prove independent IR semantics/compiler correctness. |
| `FINAL_RUNTIME.json` | Strict/cached builds and guarded queries on unchanged inputs; actual import/dependency and Mach-O/dyld bindings, with family/expression/universe/axiom/coverage guards. |
| `PUBLICATION.json` | Ordinary push to intended `main`, remote equality and required exact-revision CI; success unasserted until actual passes. |

Finish author/peer writes before tree freeze. Keep later outcomes external; changed inputs require fresh qualification/checks.

## Trust and fidelity

The actual core axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`. Toolchain/dependency pins and raw kernel evidence are retained above.

Check kernel acceptance and mathematical/source fidelity separately. No `sorry`, `admit`, unproved axiom, circular/vacuous premise or weakened target. Removing unused hypotheses strengthens scope. Carrier repairs do not imply a prior compiled TYPE for illtyped expressions. DATA/private/generated checks are part of the supplemental audit.

Trust Lean's kernel/compiler/runtime in their stated roles. Report full verification/publication only after all applicable final checks and exact-revision CI pass.
