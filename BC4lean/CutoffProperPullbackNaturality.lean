import BC4lean.CutoffRestrictionNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine proper equivariant pullback of cutoff classes

The construction imports the concrete reduced crossed-product map.


An actual proper equivariant map pulls back compactly supported continuous
cutoffs, preserving their nonnegativity and inverse-orbit normalization.
The finite coefficient formula proves that the actual reduced crossed map
takes the genuine cutoff projection to this pulled-back cutoff projection.
Projection-class functoriality and cutoff independence then identify its
operator K0 class with that of any actual cutoff on the source space.

No surjectivity, injectivity, assumed crossed-product map, or assumed
K-theory naturality is used.
-/

noncomputable section
open Topology
open scoped CompactlySupported ZeroAtInfty ComplexOrder

namespace BC4lean.ProperActions.Cutoff
open KKTheory OperatorKTheory

private theorem cutoffProjectionK0_congr {D : Type*} [NonUnitalCStarAlgebra D]
    {p q : D} {hp : IsStarProjection p} {hq : IsStarProjection q} (h : p = q) :
    nonunitalProjectionK0 p hp = nonunitalProjectionK0 q hq := by
  cases h
  rfl

variable {Γ X Y : Type*} [Group Γ]
  [TopologicalSpace X] [TopologicalSpace Y] [MulAction Γ X] [MulAction Γ Y]

/-- Pull back the actual cutoff along a genuine proper equivariant map.
Compact support is supplied by properness of the original map. -/
def properPullbackCutoff (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : CutoffFunction Γ Y) : CutoffFunction Γ X where
  toCompactlySupportedContinuousMap := cY.toCompactlySupportedContinuousMap.comp
    (CZero.cocompactMapOfProper f hf)
  nonneg x := cY.nonneg (f x)
  normalized x := by
    change (∑ᶠ g : Γ, cY (f (g⁻¹ • x)) ^ 2) = 1
    calc
      (∑ᶠ g : Γ, cY (f (g⁻¹ • x)) ^ 2) =
          ∑ᶠ g : Γ, cY (g⁻¹ • f x) ^ 2 := by
        apply finsum_congr
        intro g
        rw [f.map_smul]
      _ = 1 := cY.normalized (f x)

@[simp] theorem properPullbackCutoff_apply
    (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : CutoffFunction Γ Y) (x : X) :
    properPullbackCutoff f hf cY x = cY (f x) := rfl

variable [TopologicalSpace Γ] [DiscreteTopology Γ]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y]
  [ProperSMul Γ X] [ProperSMul Γ Y]

omit [LocallyCompactSpace X] [LocallyCompactSpace Y] in
/-- The actual finite cutoff coefficients commute with proper pullback,
including the inverse group translate in the second cutoff factor. -/
theorem algebraicProjection_properPullback
    (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : CutoffFunction Γ Y) :
    AlgebraicCrossedProduct.map
        (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
        (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf)
        (algebraicProjection cY) =
      algebraicProjection (properPullbackCutoff f hf cY) := by
  apply AlgebraicCrossedProduct.ext (CZero.action Γ (X := X))
  intro g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp only [AlgebraicCrossedProduct.coeff_map, algebraicProjection,
    coeff_mixedAlgebraic, CZero.properPullback_apply, mixedCZeroCoefficient_apply,
    properPullbackCutoff_apply, f.map_smul]

omit [LocallyCompactSpace X] [LocallyCompactSpace Y] in
/-- The actual completed crossed map takes the genuine cutoff projection
to the genuine projection of the properly pulled-back cutoff. -/
theorem reducedCutoffProjection_properPullback
    (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : CutoffFunction Γ Y) :
    reducedCrossedMap
        (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
        (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf)
        (reducedCutoffProjection cY) =
      reducedCutoffProjection (properPullbackCutoff f hf cY) := by
  unfold reducedCutoffProjection
  rw [reducedCrossedMap_algebraic, algebraicProjection_properPullback f hf cY]

/-- Genuine projection-class functoriality for the properly pulled-back
cutoff, before using independence from the choice of source cutoff. -/
theorem cutoffK0_properPullback_pulled
    (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : CutoffFunction Γ Y) :
    operatorK0Map
        (reducedCrossedMap
          (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
          (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf))
        (cutoffK0 cY) =
      cutoffK0 (properPullbackCutoff f hf cY) := by
  unfold cutoffK0
  rw [nonunitalProjectionK0_map]
  exact cutoffProjectionK0_congr (reducedCutoffProjection_properPullback f hf cY)

/-- The actual cutoff operator K0 class is natural under every proper
equivariant map; the source cutoff is arbitrary by cutoff independence. -/
theorem cutoffK0_properPullback
    (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : CutoffFunction Γ Y) (cX : CutoffFunction Γ X) :
    operatorK0Map
        (reducedCrossedMap
          (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
          (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf))
        (cutoffK0 cY) = cutoffK0 cX :=
  (cutoffK0_properPullback_pulled f hf cY).trans
    (cutoffK0_independent (properPullbackCutoff f hf cY) cX)

end BC4lean.ProperActions.Cutoff
