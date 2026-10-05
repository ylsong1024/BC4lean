import BC4lean.LabeledRealizationShift
import BC4lean.SimplexCoordinateInterpolation
import BC4lean.LabeledRealizationProducts
import Mathlib.Tactic.Ring

noncomputable section
open scoped Classical unitInterval
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]

namespace LabeledOrbitSimplex

def shiftedCoordinates (s : LabeledOrbitSimplex Γ) (k : ℕ)
    (w : LabeledSimplexCoordinates Γ s) : LabeledSimplexCoordinates Γ (s.partialShift k) :=
  ⟨shiftedWeights k w.val, shiftedWeights_mem k s w.property⟩

theorem continuous_shiftedCoordinates (s : LabeledOrbitSimplex Γ) (k : ℕ) :
    Continuous (s.shiftedCoordinates k) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  by_cases hv : v.1 = k
  · simpa [shiftedCoordinates, shiftedWeights, hv, Function.comp_def] using
      (continuous_const : Continuous (fun _ : LabeledSimplexCoordinates Γ s => (0 : ℝ)))
  · simpa [shiftedCoordinates, shiftedWeights, hv, Function.comp_def] using
      (continuous_apply (partialUnshiftVertex k v)).comp continuous_subtype_val

def consecutiveShiftChart (s : LabeledOrbitSimplex Γ) (k : ℕ)
    (p : LabeledSimplexCoordinates Γ s × I) :
    LabeledSimplexCoordinates Γ (s.shiftCarrier k) :=
  (s.shiftCarrier k).coordinateInterpolation
    (p.2, ((s.partialShift (k+1)).coordinateInclusion (s.shiftCarrier k)
        Finset.subset_union_left (s.shiftedCoordinates (k+1) p.1),
      (s.partialShift k).coordinateInclusion (s.shiftCarrier k)
        Finset.subset_union_right (s.shiftedCoordinates k p.1)))

theorem continuous_consecutiveShiftChart (s : LabeledOrbitSimplex Γ) (k : ℕ) :
    Continuous (s.consecutiveShiftChart k) := by
  apply (s.shiftCarrier k).continuous_coordinateInterpolation.comp
  apply continuous_snd.prodMk
  apply Continuous.prodMk
  · exact ((s.partialShift (k+1)).continuous_coordinateInclusion (s.shiftCarrier k)
      Finset.subset_union_left).comp ((s.continuous_shiftedCoordinates (k+1)).comp continuous_fst)
  · exact ((s.partialShift k).continuous_coordinateInclusion (s.shiftCarrier k)
      Finset.subset_union_right).comp ((s.continuous_shiftedCoordinates k).comp continuous_fst)

end LabeledOrbitSimplex

namespace LabeledOrbitRealization

def consecutiveShift (k : ℕ) (p : LabeledOrbitRealization Γ × I) :
    LabeledOrbitRealization Γ := by
  refine ⟨fun v => (1 - (p.2 : ℝ)) * shiftedWeights (k+1) p.1.val v +
    (p.2 : ℝ) * shiftedWeights k p.1.val v, ?_⟩
  obtain ⟨s, hs⟩ := p.1.property
  exact ⟨s.shiftCarrier k, (s.consecutiveShiftChart k (⟨p.1.val, hs⟩, p.2)).property⟩

theorem continuous_consecutiveShift (k : ℕ) :
    Continuous (consecutiveShift (Γ := Γ) k) := by
  apply (continuous_product_iff _).mpr
  intro s
  exact (continuous_chart (s.shiftCarrier k)).comp (s.continuous_consecutiveShiftChart k)

@[simp] theorem consecutiveShift_zero (k : ℕ) (x : LabeledOrbitRealization Γ) :
    consecutiveShift k (x, 0) = partialShift (k+1) x := by
  apply Subtype.ext
  funext v
  simp [consecutiveShift, partialShift]

@[simp] theorem consecutiveShift_one (k : ℕ) (x : LabeledOrbitRealization Γ) :
    consecutiveShift k (x, 1) = partialShift k x := by
  apply Subtype.ext
  funext v
  simp [consecutiveShift, partialShift]

/-- All sufficiently high interpolation stages are stationary on a given finite chart. -/
theorem consecutiveShift_chart_eq (k : ℕ) (s : LabeledOrbitSimplex Γ)
    (hk : ∀ v ∈ s.vertices, v.1 < k) (w : LabeledSimplexCoordinates Γ s) (t : I) :
    consecutiveShift k (chart s w, t) = chart s w := by
  have h₀ := partialShift_chart_eq k s hk w
  have h₁ := partialShift_chart_eq (k+1) s (fun v hv => Nat.lt_trans (hk v hv)
    (Nat.lt_succ_self k)) w
  have hw₀ : shiftedWeights k w.val = w.val := congrArg Subtype.val h₀
  have hw₁ : shiftedWeights (k+1) w.val = w.val := congrArg Subtype.val h₁
  apply Subtype.ext
  funext v
  change (1 - (t : ℝ)) * shiftedWeights (k+1) w.val v +
    (t : ℝ) * shiftedWeights k w.val v = w.val v
  rw [hw₀, hw₁]
  ring

end LabeledOrbitRealization
end BC4lean.ProperActions
