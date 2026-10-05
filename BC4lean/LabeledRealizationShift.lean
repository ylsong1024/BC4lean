import BC4lean.LabeledOrbitRealization
import BC4lean.LabeledOrbitShift

noncomputable section
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]

def shiftedWeights (k : ℕ) (w : LabeledOrbitVertex Γ → ℝ) :
    LabeledOrbitVertex Γ → ℝ :=
  fun v => if v.1 = k then 0 else w (partialUnshiftVertex k v)

@[simp] theorem shiftedWeights_shift (k : ℕ) (w : LabeledOrbitVertex Γ → ℝ)
    (v : LabeledOrbitVertex Γ) :
    shiftedWeights k w (partialShiftVertex k v) = w v := by
  simp [shiftedWeights, partialShift_not_gap]

theorem shiftedWeights_mem (k : ℕ) (s : LabeledOrbitSimplex Γ)
    {w : LabeledOrbitVertex Γ → ℝ} (hw : w ∈ LabeledSimplexCoordinates Γ s) :
    shiftedWeights k w ∈ LabeledSimplexCoordinates Γ (s.partialShift k) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro v
    unfold shiftedWeights
    split_ifs
    · exact le_rfl
    · exact hw.1 _
  · intro v hv
    unfold shiftedWeights
    split_ifs with hg
    · rfl
    · apply hw.2.1
      intro hm
      apply hv
      exact Finset.mem_image.mpr ⟨partialUnshiftVertex k v, hm,
        partialShift_unshift k v hg⟩
  · change ∑ v ∈ s.vertices.image (partialShiftVertex k), shiftedWeights k w v = 1
    rw [Finset.sum_image]
    · simpa using hw.2.2
    · intro a _ b _ h
      exact partialShiftVertex_injective k h

/-- Partial shifts preserve invariance under any subgroup action. -/
theorem shiftedWeights_invariant (k : ℕ) (w : LabeledOrbitVertex Γ → ℝ)
    (g : Γ) (hw : ∀ v, w (g • v) = w v) (v : LabeledOrbitVertex Γ) :
    shiftedWeights k w (g • v) = shiftedWeights k w v := by
  have hlabel : (g • v).1 = v.1 := rfl
  have hunshift : partialUnshiftVertex k (g • v) = g • partialUnshiftVertex k v := rfl
  simp only [shiftedWeights, hlabel, hunshift, hw]

namespace LabeledOrbitRealization

def partialShift (k : ℕ) (x : LabeledOrbitRealization Γ) : LabeledOrbitRealization Γ := by
  refine ⟨shiftedWeights k x.val, ?_⟩
  obtain ⟨s, hs⟩ := x.property
  exact ⟨s.partialShift k, shiftedWeights_mem k s hs⟩

/-- Relabeling finite barycentric vectors is continuous in the weak topology. -/
theorem continuous_partialShift (k : ℕ) :
    Continuous (partialShift (Γ := Γ) k) := by
  apply (continuous_iff _).mpr
  intro s
  let f : LabeledSimplexCoordinates Γ s → LabeledSimplexCoordinates Γ (s.partialShift k) :=
    fun w => ⟨shiftedWeights k w.val, shiftedWeights_mem k s w.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    by_cases hv : v.1 = k
    · simpa [f, shiftedWeights, hv, Function.comp_def] using
        (continuous_const : Continuous (fun _ : LabeledSimplexCoordinates Γ s => (0 : ℝ)))
    · simpa [f, shiftedWeights, hv, Function.comp_def] using
        (continuous_apply (partialUnshiftVertex k v)).comp continuous_subtype_val
  exact (continuous_chart (s.partialShift k)).comp hf

/-- On a finite chart every sufficiently high partial shift is exactly the identity. -/
theorem partialShift_chart_eq (k : ℕ) (s : LabeledOrbitSimplex Γ)
    (hk : ∀ v ∈ s.vertices, v.1 < k) (w : LabeledSimplexCoordinates Γ s) :
    partialShift k (chart s w) = chart s w := by
  apply Subtype.ext
  funext v
  change shiftedWeights k w.val v = w.val v
  by_cases hv : v.1 < k
  · simp [shiftedWeights, partialUnshiftVertex, hv, ne_of_lt hv]
  · have hz : w.val v = 0 := w.property.2.1 v (fun hm => hv (hk v hm))
    by_cases he : v.1 = k
    · simp [shiftedWeights, he, hz]
    · have hi : ¬ (partialUnshiftVertex k v).1 < k := by
        simp only [partialUnshiftVertex, if_neg hv]
        omega
      have hiz := w.property.2.1 (partialUnshiftVertex k v) (fun hm => hi (hk _ hm))
      simp [shiftedWeights, he, hiz, hz]

end LabeledOrbitRealization
end BC4lean.ProperActions
