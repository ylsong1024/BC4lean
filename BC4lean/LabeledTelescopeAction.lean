import BC4lean.LabeledOrbitTelescope

/-! # Fixed points of the finite-orbit telescope
The group fixes height, so fixed points are exactly fixed barycentric points
at admissible heights. Projection remains surjective after restriction.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitTelescope
variable (Γ : Type*) [Group Γ] [Countable Γ]

/-- The fixed-point condition is precisely the condition on the first coordinate. -/
theorem fixed_iff (H : Subgroup Γ) (p : Model Γ) :
    p ∈ MulAction.fixedPoints H (Model Γ) ↔
      p.val.1 ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ) := by
  constructor
  · intro h g
    exact congrArg (fun q : Model Γ => q.val.1) (h g)
  · intro h g
    exact Subtype.ext (Prod.ext (h g) rfl)

/-- Projection onto the fixed realization is onto, without choosing a continuous
section or asserting any homotopy equivalence. -/
theorem fixed_projection_surjective (H : Subgroup Γ) :
    Function.Surjective ((projection Γ).fixedPointsMap H) := by
  intro x
  obtain ⟨p, hp⟩ := projection_surjective Γ x.val
  have hpf : p ∈ MulAction.fixedPoints H (Model Γ) := by
    apply (fixed_iff Γ H p).mpr
    change p.val.1 = x.val at hp
    rw [hp]
    exact x.property
  exact ⟨⟨p, hpf⟩, Subtype.ext hp⟩

/-- The fixed telescope is literally the telescope of the fixed stages. -/
def fixedHomeomorph (H : Subgroup Γ) :
    FixedPointSpace H (Model Γ) ≃ₜ ClosedStageTelescope.Telescope
      (fun n => {x : FixedPointSpace H (LabeledOrbitRealization Γ) | x.val ∈ stage Γ n}) where
  toFun p := ⟨(⟨p.val.val.1, (fixed_iff Γ H p.val).mp p.property⟩, p.val.val.2), by
    obtain ⟨n, hn, ht⟩ := p.val.property
    exact ⟨n, hn, ht⟩⟩
  invFun p := ⟨⟨(p.val.1.val, p.val.2), by
    obtain ⟨n, hn, ht⟩ := p.property
    exact ⟨n, hn, ht⟩⟩, (fixed_iff Γ H _).mpr p.val.1.property⟩
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
    · exact continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

/-- Each fixed barycentric point has an admissible height. -/
theorem fixed_nonempty (H : Subgroup Γ)
    [Nonempty (FixedPointSpace H (LabeledOrbitRealization Γ))] :
    Nonempty (FixedPointSpace H (Model Γ)) := by
  obtain ⟨x⟩ := ‹Nonempty (FixedPointSpace H (LabeledOrbitRealization Γ))›
  obtain ⟨p, _⟩ := fixed_projection_surjective Γ H x
  exact ⟨p⟩

end BC4lean.ProperActions.LabeledOrbitTelescope
