import BC4lean.GlobalJoinShift
import BC4lean.FullShiftCone
import BC4lean.JoinShiftInvariance
import BC4lean.ProperFixedPoints
import BC4lean.LabeledOrbitRealizationProper
import BC4lean.FixedPointCriterion
import Mathlib.Topology.Homotopy.Contractible

/-! # Contractibility of the finite-subgroup fixed realization

First shift all join factors continuously, then cone to the fixed vertex in
factor zero. Both homotopies take values in the original fixed-point subtype.
-/
noncomputable section
open scoped Classical unitInterval
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

theorem coordinates_invariant_of_fixed {g : Γ} {x : LabeledOrbitRealization Γ}
    (hx : g • x = x) (v : LabeledOrbitVertex Γ) : x.val (g • v) = x.val v := by
  have he := congrArg (fun y : LabeledOrbitRealization Γ => y.val (g • v)) hx
  simpa using he.symm

theorem globalShift_fixed (H : Subgroup Γ) (x : FixedPointSpace H (LabeledOrbitRealization Γ))
    (t : I) : globalShift (x.val, t) ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ) := by
  intro h
  change (h : Γ) • globalShift (x.val, t) = globalShift (x.val, t)
  apply Subtype.ext
  funext v
  rw [smul_coordinate]
  exact finiteShiftHomotopy_invariant _ _ (h⁻¹ : Γ)
    (coordinates_invariant_of_fixed (g := (h⁻¹ : Γ)) (x := x.val) (x.property h⁻¹)) v

theorem partialShift_fixed (H : Subgroup Γ) (x : FixedPointSpace H (LabeledOrbitRealization Γ)) :
    partialShift 0 x.val ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ) := by
  intro h
  change (h : Γ) • partialShift 0 x.val = partialShift 0 x.val
  apply Subtype.ext
  funext v
  rw [smul_coordinate]
  exact partialShift_invariant 0 x.val (h⁻¹ : Γ)
    (coordinates_invariant_of_fixed (g := (h⁻¹ : Γ)) (x := x.val) (x.property h⁻¹)) v

theorem fullShiftCone_fixed (H : Subgroup Γ) [Finite H]
    (x : FixedPointSpace H (LabeledOrbitRealization Γ)) (t : I) :
    fullShiftCone H (x.val, t) ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ) := by
  intro h
  change (h : Γ) • fullShiftCone H (x.val, t) = fullShiftCone H (x.val, t)
  apply Subtype.ext
  funext v
  rw [smul_coordinate]
  have he : (h⁻¹ : Γ) • v = fixedOrbitVertex Γ H 0 ↔ v = fixedOrbitVertex Γ H 0 := by
    constructor
    · intro hv
      apply (MulAction.injective (h⁻¹ : Γ))
      exact hv.trans (fixedOrbitVertex_fixed Γ H 0 h⁻¹).symm
    · rintro rfl
      exact fixedOrbitVertex_fixed Γ H 0 h⁻¹
  let w : LabeledOrbitVertex Γ → ℝ := coordinates x.val
  change (1 - (t : ℝ)) * shiftedWeights 0 w ((h⁻¹ : Γ) • v) +
    (t : ℝ) * (if (h⁻¹ : Γ) • v = fixedOrbitVertex Γ H 0 then 1 else 0) =
    (1 - (t : ℝ)) * shiftedWeights 0 w v +
    (t : ℝ) * (if v = fixedOrbitVertex Γ H 0 then 1 else 0)
  rw [shiftedWeights_invariant 0 w (h⁻¹ : Γ)
    (coordinates_invariant_of_fixed (g := (h⁻¹ : Γ)) (x := x.val) (x.property h⁻¹)) v]
  rw [if_congr he rfl rfl]

def emptySimplex : LabeledOrbitSimplex Γ := ⟨∅, by simp [Set.InjOn]⟩

def fixedZeroPoint (H : Subgroup Γ) [Finite H] : FixedPointSpace H (LabeledOrbitRealization Γ) := by
  let s := emptySimplex (Γ := Γ)
  let y := chart (s.fullShiftCone H) (s.fullShiftConeVertex H)
  refine ⟨y, ?_⟩
  apply (fixed_iff_support_fixed H y).mpr
  intro v hv h
  change (if v = fixedOrbitVertex Γ H 0 then (1 : ℝ) else 0) ≠ 0 at hv
  by_cases he : v = fixedOrbitVertex Γ H 0
  · rw [he]
    exact fixedOrbitVertex_fixed Γ H 0 h
  · simp [he] at hv

def fixedFullShiftMap (H : Subgroup Γ) :
    C(FixedPointSpace H (LabeledOrbitRealization Γ), FixedPointSpace H (LabeledOrbitRealization Γ)) where
  toFun x := ⟨partialShift 0 x.val, partialShift_fixed H x⟩
  continuous_toFun := ((continuous_partialShift 0).comp continuous_subtype_val).subtype_mk _

def fixedGlobalShiftHomotopy (H : Subgroup Γ) :
    ContinuousMap.Homotopy (ContinuousMap.id (FixedPointSpace H (LabeledOrbitRealization Γ)))
      (fixedFullShiftMap H) where
  toFun p := ⟨globalShift (p.2.val, p.1), globalShift_fixed H p.2 p.1⟩
  continuous_toFun := (continuous_globalShift.comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)).subtype_mk _
  map_zero_left x := Subtype.ext (globalShift_zero x.val)
  map_one_left x := Subtype.ext (globalShift_one x.val)

def fixedConeHomotopy (H : Subgroup Γ) [Finite H] :
    ContinuousMap.Homotopy (fixedFullShiftMap H)
      (ContinuousMap.const _ (fixedZeroPoint H)) where
  toFun p := ⟨fullShiftCone H (p.2.val, p.1), fullShiftCone_fixed H p.2 p.1⟩
  continuous_toFun := ((continuous_fullShiftCone H).comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)).subtype_mk _
  map_zero_left x := Subtype.ext (fullShiftCone_zero H x.val)
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    exact fullShiftCone_one_coordinates H x.val

/-- The actual finite-subgroup fixed-point space of the weak realization is contractible. -/
theorem fixedPoints_contractible (H : Subgroup Γ) [Finite H] :
    ContractibleSpace (FixedPointSpace H (LabeledOrbitRealization Γ)) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨fixedZeroPoint H, ⟨(fixedGlobalShiftHomotopy H).trans (fixedConeHomotopy H)⟩⟩

/-- The concrete weak realization has the full fixed-point criterion. A CW
structure is supplied separately by the orbit-disk attachment construction. -/
theorem fixedPointCriterion [TopologicalSpace Γ] [DiscreteTopology Γ] :
    FixedPointCriterion Γ (LabeledOrbitRealization Γ) := by
  constructor
  · intro H hH
    let := hH
    exact fixedPoints_contractible H
  · intro H hH
    let := hH
    exact infinite_fixedPoints_empty H

end BC4lean.ProperActions.LabeledOrbitRealization
