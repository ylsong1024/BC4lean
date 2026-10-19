# Chapter 7 native completion record

Native evidence checked at 2026-10-19T20:46:29.943732+00:00. The actual audit reports
`status=verified_complete`, `chapter_complete=true`, and no pending statement.
The immutable mathematical source is
[`4daf13f6be649ef3e7f9fe90122bcbee4707b1b2`](https://github.com/ylsong1024/BC4lean/commit/4daf13f6be649ef3e7f9fe90122bcbee4707b1b2).

This records construction of the coefficient-free reduced assembly homomorphism
for countable discrete groups in degrees zero and one. It does not prove that
the map is injective, surjective or an isomorphism in general. The general
Baum–Connes conjecture is not proved here.

## Exact original scope

| Original blueprint label | Actual audited readiness |
| --- | --- |
| def:reduced-descent | 11 exact endpoints; ready |
| def:cutoff-projection | 7 exact endpoints; ready |
| def:assembly-piece | 9 exact endpoints; ready |
| prop:assembly-compatibility | 9 exact endpoints; ready |
| def:assembly-map | 8 exact endpoints; ready |

Reduced descent is the actual additive homomorphism on the existing even and
odd KK quotient groups. Its representatives use the completed coefficient
extension, proved reduced source action and actual lifted operator. It
preserves arbitrary full interval-coefficient Hilbert-module homotopies with
actual fibre/endpoint isomorphisms. Fixed-module operator paths do not replace
those witnesses. All four existing native parity Kasparov products are
preserved, retaining the Clifford coordinate, Koszul external-even and Pauli
row/column Morita constructions.

Actual normalized cutoffs give projections in the concrete reduced crossed
product and existing nonunital operator K₀ classes. Independence follows from
mixed-cutoff partial isometries. The piece homomorphism is the actual
cutoff-class/Kasparov-descent product, using the inverse established scalar
KK/K₀ comparison and genuine analytic K₀/K₁ comparison. Its targets are exactly
the existing ReducedK0 and ReducedK1 groups.

The actual Chapter 6 native transitions commute with the piece maps. The
construction includes cutoff and proper restricted-map naturality, actual
cofinal-indexing comparisons and genuine universal proper-model maps. The
actual Chapter 6 directed colimit and canonical geometric telescope give the
assembly homomorphism. No arbitrary compatible family or desired compatibility
conclusion is an extra definition input.

## Necessary hypotheses and formal scope

- Crossed-product/cutoff prerequisites hold for arbitrary discrete groups unless
  countability is stated. KK descent retains countability and the separable
  coefficient assumptions required by the existing cycle, quotient and product
  APIs. Coefficients may be nonunital and original representations degenerate.
  No amenability, exactness or additional nondegeneracy assumption replaces the
  proved reduced-norm bound.
- Cutoff existence requires a continuous proper discrete action on a locally
  compact Hausdorff space with compact orbit quotient. CocompactPiece alone does
  not imply properness. Assembly retains second countability where C₀
  separability is required. Ambient model comparison maps need not be globally
  proper: their actual restrictions to the indicated pieces are proved proper.
- Ambient-space comparison uses Chapter 6's common space universe, with an
  independent group universe. Its fixed-point universal-model API uses one
  common group/space universe.
- Native product comparison has independent Γ/A/B/C universes and the common
  original module universe `W = max(u,uΓ,uA,uB,uC)`. The ordinary target acting
  group is Unit at universe zero. Different arbitrary module-universe packaging
  is not silently asserted or obtained by shrinking actual carriers.
- Indexing independence requires monotonicity and upper-bound cofinality
  `∀ S, ∃ j, S ≤ φ(j)`, and the analogous hypothesis for ψ. Pointwise
  coverage of the ambient space cannot replace cofinality.

## Actual native evidence

The uncapped module-origin audit contains **105 Chapter 7 modules**,
**2,491 declarations** including private/generated constants,
**117 exact blueprint links**, and **117 unique mathematical
endpoints**. All five original targets and 20 supporting
milestones are ready. Their actual combined axiom closure is `Classical.choice`, `Quot.sound`, `propext`.

The strict build covers **930 library modules plus the aggregate**,
preserving the frozen Chapter 6 import prefix. All 106 actual build
invocations returned zero. Sources were unchanged and the full chapter build
source map agrees with the actual audit and current source. The final aggregate
command was `lake --wfail --no-cache build BC4lean`. The final aggregate log reports 4,328 Lake jobs.

The actual verification subprocess commands were:

- `/Library/Frameworks/Python.framework/Versions/3.14/bin/python3 -B scripts/check_project_imports.py` — exit 0.
- `lake --wfail --no-build --no-cache build BC4lean` — exit 0.
- `lake env lean -j1 -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false /private/tmp/BC4lean-chapter7-descent-native-20261018/docs/audits/chapter7/ExpectedTypes.lean` — exit 0.
- `lake env lean -j1 -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false /private/tmp/BC4lean-chapter7-descent-native-20261018/docs/audits/chapter7/audit.lean` — exit 0.

The retained strict raw-process verifier reparsed the uncapped kernel log and
validated command/log hashes, source bindings, independent expected types,
private/generated coverage and actual allowed axiom dependencies. Audited
sources and compiled objects remained unchanged through this record's gate.
The completed-chapter CI policy invokes `--require-complete`.

Chapter 7 library proofs use the pinned compiler's ordinary elaboration budgets. The
generated metadata-census query uses the unchanged inherited audit-only
`maxHeartbeats 0` setting to enumerate already compiled declarations and their
axiom closures; it supplies no replacement mathematical proof.

| Evidence | SHA-256 |
| --- | --- |
| `docs/audits/chapter7/audit.json` | `63a595a1c1a10cc8ad4dc31cdf72b856975ab238a952c631bd0c9e633b9dd1b6` |
| `docs/audits/chapter7/build.json` | `396d60f2dc763f9605356c7f3d8cb318bedacd71c6c264388e0a196e611976ee` |
| Actual generated kernel query | `a524200920ae1bcc87f1ad48aa0d1a084fb55a7863dd55196c62cb00ec3e4e4e` |
| Actual ExpectedTypes.lean | `230068162961c97c380060b69ed3aa93e5ed1887bf13bb7065072e3f6c2cc83d` |
| Actual combined build log | `f427d4591d0b596d2d014f4a90a049b70943e3b1be7598d3b2b9b5a55baf6b62` |

Raw queries, logs and subprocess records accompany these audit/build files.
Synthetic Python safeguard fixtures are not mathematical proof evidence.

## Publication acceptance is separate

This native record does not assert future CI or deployment success. Final
publication commit Q differs from mathematical source S above. After the
authorized push, a separate dated `chapter7.postpush.acceptance.v1` receipt
must confirm remote head Q, these five required workflows at exact Q, and
independently fetched actual live content:

- Build BC4lean
- Check blueprint
- Publish blueprint
- Verify Chapter 6
- Verify Chapter 7 milestones

Live acceptance includes the homepage, chapter, both graphs, finder, version
manifest and immutable source files/lines at S. Its audit/build hashes must
match this native record. A successful publisher alone is insufficient.

Keep the post-push receipt in durable task evidence outside Q. Committing Q's
own hash inside Q would create a self-reference. Do not rewrite this committed
native record merely to insert its own final publication hash. Report the
separate exact-Q CI/live receipt with the final publication acceptance.

## Historical foundation checkpoint

The earlier foundation publication was
[`d3a357136bbcf5eb88926deb9fa069666d217c51`](https://github.com/ylsong1024/BC4lean/commit/d3a357136bbcf5eb88926deb9fa069666d217c51),
with proof source
[`7af944529243b198d584891762959a954973bb4b`](https://github.com/ylsong1024/BC4lean/commit/7af944529243b198d584891762959a954973bb4b).
Its [immutable verification record](https://github.com/ylsong1024/BC4lean/blob/d3a357136bbcf5eb88926deb9fa069666d217c51/docs/CHAPTER7_VERIFICATION.md)
describes 16 modules, 535 declarations, 65 links and one ready original target
at that checkpoint. Those historical counts and pending statements do not
describe this later native completion record. Chapters 4–6 and their frozen
evidence remain preserved.
