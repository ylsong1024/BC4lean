import BC4lean.SimplexDisk
import BC4lean.LabeledSimplexCharts
import BC4lean.LabeledSimplexFaces

/-! # Disk-pair witnesses for finite labeled simplex charts -/
noncomputable section
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]

/-- Every nonempty chart is a disk in its affine dimension; its complete face
boundary corresponds to the Euclidean sphere. -/
theorem exists_labeledSimplexDiskHomeomorph (s : LabeledOrbitSimplex Γ)
    (hne : s.vertices.Nonempty) :
    ∃ e : LabeledSimplexCoordinates Γ s ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (s.vertices.card - 1))) 1,
      ∀ w, w ∈ LabeledOrbitRealization.chartBoundary s ↔
        (e w).val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (s.vertices.card - 1))) 1 := by
  obtain ⟨v, hv⟩ := hne
  have h : ∃ q : stdSimplex ℝ s.vertices ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (s.vertices.card - 1))) 1,
      ∀ x, (∃ i, x.val i = 0) ↔
        (q x).val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (s.vertices.card - 1))) 1 := by
    have hc : Fintype.card s.vertices = s.vertices.card := Fintype.card_coe _
    have hraw := exists_finiteSimplexDiskHomeomorph s.vertices (⟨v,hv⟩ : s.vertices)
    rw [hc] at hraw
    exact hraw
  obtain ⟨q, hq⟩ := h
  refine ⟨(labeledCoordinatesHomeomorph s).trans q, ?_⟩
  intro w
  change w ∈ LabeledOrbitRealization.chartBoundary s ↔
    (q (labeledCoordinatesHomeomorph s w)).val ∈ Metric.sphere _ 1
  rw [← hq]
  change (∃ v ∈ s.vertices, w.val v = 0) ↔
    ∃ v : s.vertices, w.val v.val = 0
  constructor
  · rintro ⟨v,hv,hz⟩
    exact ⟨⟨v,hv⟩,hz⟩
  · rintro ⟨v,hz⟩
    exact ⟨v.val,v.property,hz⟩

end BC4lean.ProperActions
