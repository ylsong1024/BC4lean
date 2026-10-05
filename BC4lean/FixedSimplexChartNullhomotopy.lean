import BC4lean.FixedSimplexAffineContraction
import BC4lean.LabeledOrbitRealizationAction
import BC4lean.ProperFixedPoints
import Mathlib.Topology.Homotopy.Basic

/-! # Nullhomotopy of a fixed finite chart in the subgroup fixed-point space

This packages the affine chart construction in the actual fixed-point subtype.
It does not assert contractibility of the entire fixed-point space.
-/
noncomputable section
open scoped Classical unitInterval

namespace BC4lean.ProperActions.LabeledOrbitSimplex
variable {Γ : Type*} [Group Γ]

/-- A subgroup-fixed simplex chart lands in the actual subgroup fixed-point set. -/
theorem chart_mem_fixedPoints (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ)
    (hs : ∀ h : H, (h : Γ) • s = s) (w : LabeledSimplexCoordinates Γ s) :
    LabeledOrbitRealization.chart s w ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ) := by
  intro h
  change (h : Γ) • LabeledOrbitRealization.chart s w = LabeledOrbitRealization.chart s w
  apply Subtype.ext
  funext v
  rw [LabeledOrbitRealization.smul_coordinate]
  exact s.fixed_coordinates_invariant H hs w h⁻¹ v

/-- The original chart inclusion into the subgroup fixed-point space. -/
def fixedChartMap (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ)
    (hs : ∀ h : H, (h : Γ) • s = s) :
    C(LabeledSimplexCoordinates Γ s, FixedPointSpace H (LabeledOrbitRealization Γ)) where
  toFun w := ⟨LabeledOrbitRealization.chart s w, s.chart_mem_fixedPoints H hs w⟩
  continuous_toFun := (LabeledOrbitRealization.continuous_chart s).subtype_mk _

/-- The fresh vertex determines a genuine point of the subgroup fixed-point space. -/
def fixedFreshPoint (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ) :
    FixedPointSpace H (LabeledOrbitRealization Γ) := by
  refine ⟨LabeledOrbitRealization.chart (s.fixedExtension H) (s.freshVertexCoordinates H), ?_⟩
  apply (LabeledOrbitRealization.fixed_iff_support_fixed H _).mpr
  intro v hv h
  change (if v = s.freshFixedVertex H then (1 : ℝ) else 0) ≠ 0 at hv
  by_cases he : v = s.freshFixedVertex H
  · rw [he]
    exact s.freshFixedVertex_fixed H h
  · simp [he] at hv

/-- The terminal constant map is continuous in the fixed-point subspace topology. -/
def fixedFreshMap (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ) :
    C(LabeledSimplexCoordinates Γ s, FixedPointSpace H (LabeledOrbitRealization Γ)) :=
  ContinuousMap.const _ (s.fixedFreshPoint H)

/-- The affine chart map takes values in the actual subgroup fixed-point space. -/
def fixedAffineFixedPointMap (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ)
    (hs : ∀ h : H, (h : Γ) • s = s) :
    C(I × LabeledSimplexCoordinates Γ s, FixedPointSpace H (LabeledOrbitRealization Γ)) where
  toFun p := ⟨LabeledOrbitRealization.chart (s.fixedExtension H) (s.fixedAffineChart H p),
    (s.fixedExtension H).chart_mem_fixedPoints H (s.fixedExtension_fixed H hs)
      (s.fixedAffineChart H p)⟩
  continuous_toFun := ((LabeledOrbitRealization.continuous_chart (s.fixedExtension H)).comp
    (s.continuous_fixedAffineChart H)).subtype_mk _

/-- The fixed chart inclusion is nullhomotopic within the subgroup fixed-point space. -/
def fixedChartNullhomotopy (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ)
    (hs : ∀ h : H, (h : Γ) • s = s) :
    ContinuousMap.Homotopy (s.fixedChartMap H hs) (s.fixedFreshMap H) where
  toContinuousMap := s.fixedAffineFixedPointMap H hs
  map_zero_left w := by
    apply Subtype.ext
    exact s.chart_fixedAffineChart_zero H w
  map_one_left w := by
    apply Subtype.ext
    change LabeledOrbitRealization.chart (s.fixedExtension H) (s.fixedAffineChart H (1, w)) =
      LabeledOrbitRealization.chart (s.fixedExtension H) (s.freshVertexCoordinates H)
    exact congrArg (LabeledOrbitRealization.chart (s.fixedExtension H))
      (s.fixedAffineChart_one_eq H w)

end BC4lean.ProperActions.LabeledOrbitSimplex
