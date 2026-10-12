# Chapter 5 verification checkpoint

**Chapter 5 is incomplete.** This checkpoint publishes the current work at the
user's request; it does not claim full verification or successful CI.

The canonical source snapshot contains **809 project modules**. Actual strict
module builds have verified **775** of them. Their exact source and local proof
object hashes were rechecked before publication. The complete module list and
source bindings are recorded in [CHAPTER5_CHECKPOINT.json](CHAPTER5_CHECKPOINT.json).
The remaining **34** modules are listed below. A successful individual module
build does not establish the final declaration, semantic or axiom audit.

All 206 pre-existing module sources and the
[Chapter 4 verification record](CHAPTER4_VERIFICATION.md) remain byte-identical
to base revision `02acce56d13e1ca45c3c2952b1bda521a05de7ae`. Chapter 4's verified
revision is `ac1a7a58dd2928e00b23a46a246ebc956e105c9f`.

The root aggregate now imports every current project module exactly once.
The three main blueprint targets remain explicitly `\notready`:
`def:equivariant-kk`, `prop:kasparov-product`, and `prop:kk-k-theory`.
CI continues to require the full strict build and complete chapter audit;
this incomplete checkpoint is expected to fail those gates. They have not been
weakened or bypassed to publish it.

## Scope and work completed

The blueprint contains 75 mathematical blocks (17 definitions and 58
propositions), with 435 distinct Lean links. The source includes genuine
completed Hilbert-module and interior-tensor constructions, arbitrary
interval-module endpoint fibres and gluing, full homotopy quotients,
Clifford/Morita parity, product existence and uniqueness, product laws,
nonunital units, and the ordinary K-theory comparison constructions.
Final acceptance of all these targets remains pending.

| Main target | Source anchors |
| --- | --- |
| Equivariant KK groups | [FullGradedKasparovHomotopy](../BC4lean/FullGradedKasparovHomotopy.lean), [GroupUniverseParityGroup](../BC4lean/GroupUniverseParityGroup.lean) |
| Kasparov product and laws | [KasparovProductExistence](../BC4lean/KasparovProductExistence.lean), [KasparovProductOperatorUniqueness](../BC4lean/KasparovProductOperatorUniqueness.lean), [GroupUniverseCommonParityProduct](../BC4lean/GroupUniverseCommonParityProduct.lean) |
| Ordinary K-theory comparisons | [ScalarKasparovK0ComparisonAddEquiv](../BC4lean/ScalarKasparovK0ComparisonAddEquiv.lean), [GroupUniverseOddFullComparison](../BC4lean/GroupUniverseOddFullComparison.lean) |

The intended chapter scope is separable complex, possibly nonunital algebras
and countable discrete groups. The ordinary comparison uses `PUnit` and trivial
actions. Product constructions preserve independent group, coefficient and
module universes; common maxima include their actual coefficient carriers.
Finite constructions retain their stated empty-index and zero-algebra cases.

The compact-correspondence **quotient class** explicitly requires separability
of its target algebra, as the existing full homotopy quotient already does.
Its earlier missing-instance expression was illtyped. All direct chapter
callers meet this requirement. General raw compact-correspondence cycles,
product criteria and tensor isomorphisms keep their broader scope; this work
makes no claim of a general nonseparable quotient extension.

Proof repairs use genuine operators, completed fibres, tensor maps and full
homotopy witnesses. Removing actually unused theorem assumptions produces
stronger contexts; explicit carrier/universe annotations repair illtyped or
ambiguous expressions. Neither change is described as literal equality of an
old compiled TYPE. Computational DATA changes and generated/private scope
still require the final independent TYPE/VALUE and declaration audits.

Six further source repairs have passed private strict checks: finite Julia
recovery, the odd index quotient, common-parity products, compact-unitary
classes, the two-row exponential corner, and relative projection coefficient
naturality. Those private candidates are not staged in this canonical
checkpoint and are not counted among its 775 verified modules. Their guarded
integration and all remaining downstream checks will continue after publication.

## Remaining modules

- `BC4lean.CoefficientImageFiniteUnitary`
- `BC4lean.FiniteJuliaAlignedCorner`
- `BC4lean.FiniteJuliaProjectionIndexRecovery`
- `BC4lean.FinitePairedPrefixCoordinates`
- `BC4lean.FiniteProjectionAlignedAbsorption`
- `BC4lean.FiniteRelativeProjectionK0IndexRecovery`
- `BC4lean.GroupUniverseCommonParityProduct`
- `BC4lean.GroupUniverseOddFullComparison`
- `BC4lean.GroupUniverseParityFunctoriality`
- `BC4lean.GroupUniverseParityHomCycle`
- `BC4lean.GroupUniverseParityMapCoherence`
- `BC4lean.GroupUniverseParityUnits`
- `BC4lean.OddFredholmRowFibrePullback`
- `BC4lean.OddFredholmScalarCycleRawIndex`
- `BC4lean.OddKTheoryArbitraryCycleInverse`
- `BC4lean.OddKTheoryCoefficientImageHomotopy`
- `BC4lean.OddKTheoryCoefficientTensorFiniteIndex`
- `BC4lean.OddKTheoryCompactUnitaryClass`
- `BC4lean.OddKTheoryComparisonAddEquiv`
- `BC4lean.OddKTheoryFiniteCoefficientTensorIso`
- `BC4lean.OddKTheoryFiniteCornerAbsorption`
- `BC4lean.OddKTheoryIndependentCoefficientNaturality`
- `BC4lean.OddKTheoryIndexQuotient`
- `BC4lean.OddKTheoryMatrixUnitaryClass`
- `BC4lean.OddKTheoryModuleUniverseIndex`
- `BC4lean.OddKTheoryStandardFiniteSplit`
- `BC4lean.OddKTheoryStandardPrefixEquiv`
- `BC4lean.OddKTheoryStandardPrefixIndex`
- `BC4lean.OddKTheoryStandardUnitaryInverse`
- `BC4lean.OddKTheoryTwoRowExponentialCorner`
- `BC4lean.ScalarKasparovK0ComparisonAddEquiv`
- `BC4lean.ScalarKasparovK0ComparisonNaturality`
- `BC4lean.ScalarRelativeProjectionCoefficientNaturality`
- `BC4lean.UnitizationFiniteJuliaRecovery`

## Reference corrections

The mathematical reference is
[Echterhoff, arXiv:1703.10912v2](https://arxiv.org/pdf/1703.10912v2).
Its printed auxiliary inequalities `M,N ≥ 1` together with `M+N=1` are
incompatible in a nonzero algebra. The intended partition uses positive
contractions `0 ≤ M,N ≤ 1`, `M+N=1`, and positive square roots `m,n` with
`m²+n²=1`. The zero-algebra case remains allowed.

Creation is generally bounded and adjointable as `θξ : F → E ⊗Ψ F`; it is
compact under the appropriate compact-left-action condition. The printed
unconditional compactness claim is false.
[InteriorCreationCycleCounterexample](../BC4lean/InteriorCreationCycleCounterexample.lean)
records the actual completed infinite-dimensional counterexample. These
corrections are explicit; the printed false claims are not claimed verified.

## Checks for this checkpoint

The 21 audit safeguard tests, exact aggregate import inventory, source trust
scan and secret-pattern scan passed. The staged whitespace check reports an
extra final blank line in five source files: `InteriorModuleTensorAssociator`,
`OddFredholmIntervalRowFormula`, `OddFredholmOperatorK1Index`,
`OddFredholmPolarTail`, and `OddFredholmRowEndpoint`. Their cleanup remains
pending; the current exact compiled source/object bindings are preserved.
No successful full aggregate build, final axiom audit or CI result is claimed.

## Pending full verification

Completion still requires:

- Strict builds of every remaining module and the entire aggregate.
- Independent expected TYPE, class/binder context, universes, DATA VALUE,
  generated/private declarations and all applicable runtime/alias checks.
- Exhaustive declaration axioms and source-coverage checks over the complete
  Chapter 5 prerequisite closure, including other namespaces.
- Complete verification of all 435 blueprint links and main-target endpoints,
  blueprint rendering and the final verification record.
- A final verified revision, ordinary push, and successful exact-revision CI.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed foundational
axioms. `sorry`, `admit`, new unproved axioms, vacuous hypotheses and weakened
statements cannot close a gate. Historical declaration counts and partial
source/private checks are not substitutes for the final uncapped audit.

The full repository gates remain:

```sh
python3 -B scripts/test_audit_chapter5.py
python3 scripts/check_project_imports.py
lake --wfail build BC4lean
python3 scripts/audit_chapter5.py --require-complete --output /tmp/chapter5-final-audit.json
(cd blueprint/src && python3 build_web.py)
git diff --check
```

This record describes an incomplete checkpoint. The older
`CHAPTER5_AUDIT.json` is historical prerequisite evidence and does not certify
this expanded source scope.
