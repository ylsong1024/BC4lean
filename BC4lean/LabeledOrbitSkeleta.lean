import BC4lean.LabeledOrbitRealizationAction

/-! # Closed dimension filtration of the labeled realization

The n-th carrier below consists of points using at most n vertices. This is
the (n-1)-dimensional skeletal carrier; it does not yet supply cell attachments.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- The canonical active support translates with the point. -/
theorem supportSimplex_smul (g : Γ) (x : LabeledOrbitRealization Γ) :
    supportSimplex (g • x) = g • supportSimplex x := by
  classical
  apply LabeledOrbitSimplex.ext
  apply Finset.ext
  intro v
  change v ∈ (supportSimplex (g • x)).vertices ↔
    v ∈ (supportSimplex x).vertices.image (fun w => g • w)
  rw [mem_supportSimplex, smul_coordinate]
  constructor
  · intro hv
    exact Finset.mem_image.mpr ⟨g⁻¹ • v, (mem_supportSimplex x _).mpr hv, by simp⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    simpa using (mem_supportSimplex x w).mp hw

/-- Stage zero is empty; stage n contains simplices of dimension at most n-1. -/
def skeletalCarrier (n : ℕ) : Set (LabeledOrbitRealization Γ) :=
  {x | (supportSimplex x).vertices.card ≤ n}

theorem skeletalCarrier_smul (n : ℕ) (g : Γ) {x : LabeledOrbitRealization Γ}
    (hx : x ∈ skeletalCarrier n) : g • x ∈ skeletalCarrier n := by
  classical
  change (supportSimplex (g • x)).vertices.card ≤ n
  rw [supportSimplex_smul]
  change ((supportSimplex x).vertices.image (fun v => g • v)).card ≤ n
  rw [Finset.card_image_of_injective _ (MulAction.injective g)]
  exact hx

theorem skeletalCarrier_mono : Monotone (skeletalCarrier (Γ := Γ)) :=
  fun _ _ h _ hx => hx.trans h

theorem mem_skeletalCarrier_iff (n : ℕ) (x : LabeledOrbitRealization Γ) :
    x ∈ skeletalCarrier n ↔ ∃ s : LabeledOrbitSimplex Γ,
      s.vertices.card ≤ n ∧ x.val ∈ LabeledSimplexCoordinates Γ s := by
  constructor
  · intro hx
    exact ⟨supportSimplex x, hx, mem_coordinates_supportSimplex x⟩
  · rintro ⟨s, hs, hw⟩
    apply le_trans (Finset.card_le_card ?_) hs
    intro v hv
    by_contra h
    exact ((mem_supportSimplex x v).mp hv) (hw.2.1 v h)

theorem skeletalCarrier_zero : skeletalCarrier (Γ := Γ) 0 = ∅ := by
  ext x
  simp only [skeletalCarrier, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  have he : (supportSimplex x).vertices = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)
  obtain ⟨v, hv⟩ := exists_nonzero x
  have hm := (mem_supportSimplex x v).mpr hv
  simp [he] at hm

theorem iUnion_skeletalCarrier : (⋃ n, skeletalCarrier (Γ := Γ) n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨(supportSimplex x).vertices.card, by
    change (supportSimplex x).vertices.card ≤ (supportSimplex x).vertices.card
    exact le_rfl⟩

/-- Requiring too many active coordinates gives an open complement. -/
theorem isClosed_skeletalCarrier (n : ℕ) : IsClosed (skeletalCarrier (Γ := Γ) n) := by
  classical
  have he : (skeletalCarrier (Γ := Γ) n)ᶜ =
      ⋃ t : Finset (LabeledOrbitVertex Γ), ⋃ (_ : n < t.card),
        ⋂ v ∈ t, {x : LabeledOrbitRealization Γ | x.val v ≠ 0} := by
    ext x
    simp only [skeletalCarrier, Set.mem_compl_iff, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_iInter, not_le]
    constructor
    · intro hx
      exact ⟨(supportSimplex x).vertices, hx, fun v hv => (mem_supportSimplex x v).mp hv⟩
    · rintro ⟨t, ht, htx⟩
      exact lt_of_lt_of_le ht (Finset.card_le_card (fun v hv =>
        (mem_supportSimplex x v).mpr (htx v hv)))
  rw [← isOpen_compl_iff, he]
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro _
  exact t.finite_toSet.isOpen_biInter (fun v _ =>
    isOpen_ne.preimage (continuous_coordinate v))

end BC4lean.ProperActions.LabeledOrbitRealization
