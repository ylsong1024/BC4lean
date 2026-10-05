import BC4lean.LabeledShiftInterpolation
import BC4lean.LabeledOrbitRealizationAction

/-! # Coning the full shift to a fixed vertex in the vacated factor -/
noncomputable section
open scoped Classical unitInterval
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]
namespace LabeledOrbitSimplex

def fullShiftCone (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ) :
    LabeledOrbitSimplex Γ :=
  (s.partialShift 0).adjoinVertex (fixedOrbitVertex Γ H 0)
    (fun _ hv => s.partialShift_zero_label hv)

def fullShiftConeVertex (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ) :
    LabeledSimplexCoordinates Γ (s.fullShiftCone H) := by
  refine ⟨fun v => if v = fixedOrbitVertex Γ H 0 then 1 else 0, ?_, ?_, ?_⟩
  · intro v
    dsimp only
    split_ifs <;> norm_num
  · intro v hv
    have hne : v ≠ fixedOrbitVertex Γ H 0 := by
      intro h
      apply hv
      change v ∈ insert (fixedOrbitVertex Γ H 0) (s.partialShift 0).vertices
      simp [h]
    simp [hne]
  · change ∑ v ∈ insert (fixedOrbitVertex Γ H 0) (s.partialShift 0).vertices,
      (if v = fixedOrbitVertex Γ H 0 then (1 : ℝ) else 0) = 1
    simp

def fullShiftConeCoordinates (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ)
    (p : LabeledSimplexCoordinates Γ s × I) :
    LabeledSimplexCoordinates Γ (s.fullShiftCone H) :=
  (s.fullShiftCone H).coordinateInterpolation
    (p.2, ((s.partialShift 0).coordinateInclusion (s.fullShiftCone H)
      (Finset.subset_insert _ _) (s.shiftedCoordinates 0 p.1), s.fullShiftConeVertex H))

theorem continuous_fullShiftConeCoordinates (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) : Continuous (s.fullShiftConeCoordinates H) :=
  (s.fullShiftCone H).continuous_coordinateInterpolation.comp
    (continuous_snd.prodMk
      ((((s.partialShift 0).continuous_coordinateInclusion (s.fullShiftCone H)
        (Finset.subset_insert _ _)).comp ((s.continuous_shiftedCoordinates 0).comp
          continuous_fst)).prodMk continuous_const))

end LabeledOrbitSimplex
namespace LabeledOrbitRealization

def fullShiftCone (H : Subgroup Γ) [Finite H] (p : LabeledOrbitRealization Γ × I) :
    LabeledOrbitRealization Γ := by
  refine ⟨fun v => (1 - (p.2 : ℝ)) * shiftedWeights 0 p.1.val v +
    (p.2 : ℝ) * (if v = fixedOrbitVertex Γ H 0 then 1 else 0), ?_⟩
  obtain ⟨s, hs⟩ := p.1.property
  exact ⟨s.fullShiftCone H, (s.fullShiftConeCoordinates H (⟨p.1.val, hs⟩, p.2)).property⟩

theorem continuous_fullShiftCone (H : Subgroup Γ) [Finite H] :
    Continuous (fullShiftCone (Γ := Γ) H) := by
  apply (continuous_product_iff _).mpr
  intro s
  exact (continuous_chart (s.fullShiftCone H)).comp (s.continuous_fullShiftConeCoordinates H)

@[simp] theorem fullShiftCone_zero (H : Subgroup Γ) [Finite H]
    (x : LabeledOrbitRealization Γ) : fullShiftCone H (x, 0) = partialShift 0 x := by
  apply Subtype.ext
  funext v
  simp [fullShiftCone, partialShift]

theorem fullShiftCone_one_coordinates (H : Subgroup Γ) [Finite H]
    (x : LabeledOrbitRealization Γ) :
    (fullShiftCone H (x, 1)).val = (fun v => if v = fixedOrbitVertex Γ H 0 then 1 else 0) := by
  funext v
  simp [fullShiftCone]

end LabeledOrbitRealization
end BC4lean.ProperActions
