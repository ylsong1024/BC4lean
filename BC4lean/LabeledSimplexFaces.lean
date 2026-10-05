import BC4lean.LabeledOrbitRealization

/-! # Faces and closed skeletal filtration of the weak realization -/
noncomputable section
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]
namespace LabeledOrbitRealization
local instance : DecidableEq (LabeledOrbitVertex Γ) := Classical.decEq _

/-- A chart consists precisely of points supported on its vertex set. -/
theorem mem_range_chart_iff (s : LabeledOrbitSimplex Γ) (x : LabeledOrbitRealization Γ) :
    x ∈ Set.range (chart s) ↔ x.val ∈ LabeledSimplexCoordinates Γ s := by
  constructor
  · rintro ⟨w, rfl⟩
    exact w.property
  · intro h
    exact ⟨⟨x.val, h⟩, Subtype.ext rfl⟩

/-- Every face chart maps continuously into its containing simplex chart. -/
def faceCoordinates (s : LabeledOrbitSimplex Γ) (t : Finset (LabeledOrbitVertex Γ))
    (ht : t ⊆ s.vertices) (w : LabeledSimplexCoordinates Γ (s.ofSubset t ht)) :
    LabeledSimplexCoordinates Γ s := by
  classical
  refine ⟨w.val, w.property.1, ?_, ?_⟩
  · intro v hv
    exact w.property.2.1 v (fun h => hv (ht h))
  · calc
      ∑ v ∈ s.vertices, w.val v = ∑ v ∈ t, w.val v :=
        (Finset.sum_subset ht (fun v _ hv => w.property.2.1 v hv)).symm
      _ = 1 := w.property.2.2

theorem continuous_faceCoordinates (s : LabeledOrbitSimplex Γ)
    (t : Finset (LabeledOrbitVertex Γ)) (ht : t ⊆ s.vertices) :
    Continuous (faceCoordinates s t ht) :=
  Continuous.subtype_mk continuous_subtype_val _

@[simp] theorem chart_faceCoordinates (s : LabeledOrbitSimplex Γ)
    (t : Finset (LabeledOrbitVertex Γ)) (ht : t ⊆ s.vertices)
    (w : LabeledSimplexCoordinates Γ (s.ofSubset t ht)) :
    chart s (faceCoordinates s t ht w) = chart (s.ofSubset t ht) w := rfl

/-- The boundary of a finite chart is where at least one vertex coordinate vanishes. -/
def chartBoundary (s : LabeledOrbitSimplex Γ) : Set (LabeledSimplexCoordinates Γ s) :=
  {w | ∃ v ∈ s.vertices, w.val v = 0}

theorem isClosed_chartBoundary (s : LabeledOrbitSimplex Γ) :
    IsClosed (chartBoundary s) := by
  have he : chartBoundary s = ⋃ v ∈ s.vertices,
      {w : LabeledSimplexCoordinates Γ s | w.val v = 0} := by
    ext w
    simp [chartBoundary]
  rw [he]
  exact s.vertices.finite_toSet.isClosed_biUnion (fun v _ =>
    isClosed_eq ((continuous_apply v).comp continuous_subtype_val) continuous_const)

/-- A zero vertex coordinate permits restriction to the corresponding proper face. -/
theorem mem_erased_face (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (v : LabeledOrbitVertex Γ)
    (hv : w.val v = 0) :
    w.val ∈ LabeledSimplexCoordinates Γ (s.ofSubset (s.vertices.erase v)
      (Finset.erase_subset _ _)) := by
  classical
  refine ⟨w.property.1, ?_, ?_⟩
  · intro u hu
    by_cases he : u = v
    · simpa [he] using hv
    · exact w.property.2.1 u (fun hm => hu (Finset.mem_erase.mpr ⟨he,hm⟩))
  · change ∑ u ∈ s.vertices.erase v, w.val u = 1
    by_cases hm : v ∈ s.vertices
    · rw [Finset.sum_erase_eq_sub hm]
      simp [w.property.2.2, hv]
    · rw [Finset.erase_eq_of_notMem hm]
      exact w.property.2.2

/-- The chart boundary is exactly the union of its codimension-one faces. -/
theorem chartBoundary_eq_faces (s : LabeledOrbitSimplex Γ) :
    chartBoundary s = ⋃ v ∈ s.vertices,
      (chart s) ⁻¹' Set.range (chart (s.ofSubset (s.vertices.erase v)
        (Finset.erase_subset _ _))) := by
  classical
  ext w
  simp only [chartBoundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage,
    mem_range_chart_iff]
  constructor
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, hv, mem_erased_face s w v hz⟩
  · rintro ⟨v, hv, hw⟩
    exact ⟨v, hv, hw.2.1 v (Finset.notMem_erase v s.vertices)⟩

/-- Overlapping charts identify exactly their common face. -/
theorem range_chart_inter (s t : LabeledOrbitSimplex Γ) :
    Set.range (chart s) ∩ Set.range (chart t) =
      Set.range (chart (s.ofSubset (s.vertices ∩ t.vertices)
        (Finset.inter_subset_left))) := by
  classical
  ext x
  simp only [Set.mem_inter_iff, mem_range_chart_iff]
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨hs.1, ?_, ?_⟩
    · intro v hv
      by_cases hvs : v ∈ s.vertices
      · exact ht.2.1 v (fun hvt => hv (Finset.mem_inter.mpr ⟨hvs, hvt⟩))
      · exact hs.2.1 v hvs
    · calc
        ∑ v ∈ s.vertices ∩ t.vertices, x.val v = ∑ v ∈ s.vertices, x.val v :=
          Finset.sum_subset Finset.inter_subset_left (fun v hvs hv =>
            ht.2.1 v (fun hvt => hv (Finset.mem_inter.mpr ⟨hvs, hvt⟩)))
        _ = 1 := hs.2.2
  · intro h
    constructor
    · exact (faceCoordinates s (s.vertices ∩ t.vertices) Finset.inter_subset_left
        ⟨x.val,h⟩).property
    · refine ⟨h.1, ?_, ?_⟩
      · intro v hv
        exact h.2.1 v (fun hm => hv (Finset.mem_inter.mp hm).2)
      · calc
          ∑ v ∈ t.vertices, x.val v = ∑ v ∈ s.vertices ∩ t.vertices, x.val v :=
            (Finset.sum_subset Finset.inter_subset_right (fun v _ hv => h.2.1 v hv)).symm
          _ = 1 := h.2.2

end LabeledOrbitRealization
end BC4lean.ProperActions
