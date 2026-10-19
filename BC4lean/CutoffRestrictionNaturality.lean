import BC4lean.ReducedCrossedProductMap
import BC4lean.ReducedCutoffProjection
import BC4lean.CocompactPieceCutoff
import BC4lean.CZeroPullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine restriction of cutoff projections and their operator K0 classes

The construction imports the concrete reduced crossed-product map.


An actual cutoff on a larger closed invariant cocompact piece restricts
along the actual proper inclusion. Proper pullback retains compact support,
and the invariant inclusion preserves nonnegativity and the orbitwise
normalization. The finite coefficient formula then proves naturality of the
algebraic cutoff element and its actual reduced projection. Entrywise
unitization and projection-class functoriality give the corresponding
operator K0 equality. Cutoff independence compares this restricted cutoff
with any actual cutoff on the smaller piece.

No restriction formula, compactness assertion, K-theory naturality field,
or transition compatibility is assumed.
-/

noncomputable section
open scoped CompactlySupported ZeroAtInfty ComplexOrder

namespace BC4lean.OperatorKTheory

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

private theorem nonunitalProjectionK0_congr {p q : A}
    {hp : IsStarProjection p} {hq : IsStarProjection q} (h : p = q) :
    nonunitalProjectionK0 p hp = nonunitalProjectionK0 q hq := by
  cases h
  rfl

/-- The genuine singleton projection class is functorial for arbitrary
nonunital star homomorphisms, including degenerate and zero homomorphisms. -/
theorem nonunitalProjectionK0_map (f : A →⋆ₙₐ[ℂ] B)
    (p : A) (hp : IsStarProjection p) :
    operatorK0Map f (nonunitalProjectionK0 p hp) =
      nonunitalProjectionK0 (f p) (hp.map f) := by
  let : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
  apply Subtype.ext
  change k0Map (Unitization.starMap f)
      (k0Projection (nonunitalFiniteProjection p hp)) =
    k0Projection (nonunitalFiniteProjection (f p) (hp.map f))
  rw [k0Map_projection]
  apply congrArg k0Projection
  apply congrArg (FiniteProjection.ofProjection
    (A := Unitization ℂ B) (ι := PUnit.{1}))
  apply Subtype.ext
  apply CStarMatrix.ext
  intro i j
  change Unitization.starMap f (Unitization.inr p) = Unitization.inr (f p)
  exact Unitization.starMap_inr f p

end BC4lean.OperatorKTheory

namespace BC4lean.ProperActions.Cutoff
open KKTheory OperatorKTheory

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]

/-- Restrict the actual cutoff along the genuine proper closed-piece inclusion.
Compact support is supplied by the proper map, not by a pointwise assumption. -/
def restrictedCutoff {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : CutoffFunction Γ T.toInvariantSubset) :
    CutoffFunction Γ S.toInvariantSubset where
  toCompactlySupportedContinuousMap := cT.toCompactlySupportedContinuousMap.comp
    (CZero.cocompactMapOfProper (CocompactPiece.inclusionMap h)
      (CocompactPiece.inclusionMap_isProperMap h))
  nonneg x := cT.nonneg (CocompactPiece.inclusionMap h x)
  normalized x := by
    change (∑ᶠ g : Γ, cT (CocompactPiece.inclusionMap h (g⁻¹ • x)) ^ 2) = 1
    calc
      (∑ᶠ g : Γ, cT (CocompactPiece.inclusionMap h (g⁻¹ • x)) ^ 2) =
          ∑ᶠ g : Γ, cT (g⁻¹ • CocompactPiece.inclusionMap h x) ^ 2 := by
        apply finsum_congr
        intro g
        rw [(CocompactPiece.inclusionMap h).map_smul]
      _ = 1 := cT.normalized (CocompactPiece.inclusionMap h x)

@[simp] theorem restrictedCutoff_apply {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : CutoffFunction Γ T.toInvariantSubset) (x : S.toInvariantSubset) :
    restrictedCutoff h cT x = cT (CocompactPiece.inclusionMap h x) := rfl

variable [TopologicalSpace Γ] [DiscreteTopology Γ]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X] [ProperSMul Γ X]

local instance restriction_piece_locallyCompact (S : CocompactPiece Γ X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

/-- The actual finite cutoff coefficients restrict pointwise along the
invariant inclusion, including every translated second factor. -/
theorem algebraicProjection_pieceRestriction {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : CutoffFunction Γ T.toInvariantSubset) :
    AlgebraicCrossedProduct.map
        (CZero.action Γ (X := T.toInvariantSubset))
        (CZero.action Γ (X := S.toInvariantSubset))
        (CZero.pieceRestriction h) (CZero.pieceRestriction_equivariant h)
        (algebraicProjection cT) =
      algebraicProjection (restrictedCutoff h cT) := by
  apply AlgebraicCrossedProduct.ext (CZero.action Γ (X := S.toInvariantSubset))
  intro g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp only [AlgebraicCrossedProduct.coeff_map, algebraicProjection,
    coeff_mixedAlgebraic, CZero.pieceRestriction_apply, mixedCZeroCoefficient_apply,
    restrictedCutoff_apply, (CocompactPiece.inclusionMap h).map_smul]

/-- The concrete completed crossed map takes the actual cutoff projection
to the actual projection of the genuinely restricted cutoff. -/
theorem reducedCutoffProjection_pieceRestriction {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : CutoffFunction Γ T.toInvariantSubset) :
    reducedCrossedMap
        (CZero.action Γ (X := T.toInvariantSubset))
        (CZero.action Γ (X := S.toInvariantSubset))
        (CZero.pieceRestriction h) (CZero.pieceRestriction_equivariant h)
        (reducedCutoffProjection cT) =
      reducedCutoffProjection (restrictedCutoff h cT) := by
  unfold reducedCutoffProjection
  rw [reducedCrossedMap_algebraic, algebraicProjection_pieceRestriction h cT]

/-- Projection-class functoriality identifies the actual K0 image with the
class of the genuinely restricted cutoff. -/
theorem cutoffK0_pieceRestriction_restricted {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : CutoffFunction Γ T.toInvariantSubset) :
    operatorK0Map
        (reducedCrossedMap
          (CZero.action Γ (X := T.toInvariantSubset))
          (CZero.action Γ (X := S.toInvariantSubset))
          (CZero.pieceRestriction h) (CZero.pieceRestriction_equivariant h))
        (cutoffK0 cT) =
      cutoffK0 (restrictedCutoff h cT) := by
  unfold cutoffK0
  rw [nonunitalProjectionK0_map]
  exact nonunitalProjectionK0_congr (reducedCutoffProjection_pieceRestriction h cT)

/-- The actual cutoff K0 class is natural for every Chapter 6 piece inclusion.
The target cutoff is arbitrary, by the genuine mixed-cutoff partial isometry. -/
theorem cutoffK0_pieceRestriction {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : CutoffFunction Γ T.toInvariantSubset)
    (cS : CutoffFunction Γ S.toInvariantSubset) :
    operatorK0Map
        (reducedCrossedMap
          (CZero.action Γ (X := T.toInvariantSubset))
          (CZero.action Γ (X := S.toInvariantSubset))
          (CZero.pieceRestriction h) (CZero.pieceRestriction_equivariant h))
        (cutoffK0 cT) = cutoffK0 cS :=
  (cutoffK0_pieceRestriction_restricted h cT).trans
    (cutoffK0_independent (restrictedCutoff h cT) cS)

end BC4lean.ProperActions.Cutoff
