import BC4lean.LabeledOrbitRealization

/-! # Finite charts are standard simplices -/
noncomputable section
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]

/-- Restrict a barycentric chart to its finite vertex set. -/
def restrictLabeledCoordinates (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) : stdSimplex ℝ s.vertices := by
  refine ⟨fun v => w.val v.val, fun v => w.property.1 v.val, ?_⟩
  rw [Finset.sum_coe_sort]
  exact w.property.2.2

/-- Extend finite simplex coordinates by zero outside its vertices. -/
def extendLabeledCoordinates (s : LabeledOrbitSimplex Γ)
    (w : stdSimplex ℝ s.vertices) : LabeledSimplexCoordinates Γ s := by
  classical
  refine ⟨fun v => if hv : v ∈ s.vertices then w.val ⟨v,hv⟩ else 0, ?_, ?_, ?_⟩
  · intro v
    dsimp only
    split_ifs with hv
    · exact w.property.1 _
    · exact le_rfl
  · intro v hv
    simp [hv]
  · rw [← Finset.sum_coe_sort]
    simpa using w.property.2

/-- The chart has exactly the usual topology of a finite standard simplex. -/
def labeledCoordinatesHomeomorph (s : LabeledOrbitSimplex Γ) :
    LabeledSimplexCoordinates Γ s ≃ₜ stdSimplex ℝ s.vertices where
  toFun := restrictLabeledCoordinates s
  invFun := extendLabeledCoordinates s
  left_inv w := by
    classical
    apply Subtype.ext
    funext v
    change (if hv : v ∈ s.vertices then w.val v else 0) = w.val v
    split_ifs with hv
    · rfl
    · exact (w.property.2.1 v hv).symm
  right_inv w := by
    classical
    apply Subtype.ext
    funext v
    simp [restrictLabeledCoordinates, extendLabeledCoordinates]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact (continuous_apply v.val).comp continuous_subtype_val
  continuous_invFun := by
    classical
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    by_cases hv : v ∈ s.vertices
    · change Continuous (fun w : stdSimplex ℝ s.vertices =>
        if h : v ∈ s.vertices then w.val ⟨v,h⟩ else 0)
      simp only [dif_pos hv]
      exact (continuous_apply (⟨v,hv⟩ : s.vertices)).comp continuous_subtype_val
    · change Continuous (fun w : stdSimplex ℝ s.vertices =>
        if h : v ∈ s.vertices then w.val ⟨v,h⟩ else 0)
      simp only [dif_neg hv]
      exact continuous_const

end BC4lean.ProperActions
