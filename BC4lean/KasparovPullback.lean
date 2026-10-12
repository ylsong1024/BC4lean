import BC4lean.KasparovOperatorHomotopy

/-! # Contravariant transport of raw equivariant Kasparov cycles

Precomposition with an actual equivariant complex star homomorphism preserves
all four localized compact defects, degeneracy and fixed-module operator
homotopies. This supplies raw cycle functoriality without asserting a KK quotient.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A A₁ A₂ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {α₁ : CStarAlgebraAction Γ A₁}
  {α₂ : CStarAlgebraAction Γ A₂} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- Pull a raw cycle back along an equivariant source-algebra homomorphism. -/
def pullback (c : KasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    KasparovCycle α₁ β E where
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := c.groupAction
  grading_preserved := c.grading_preserved
  representation := c.representation.comp ρ
  representation_even a := c.representation_even (ρ a)
  representation_equivariant := by
    intro g a
    change c.groupAction.conjugateOperator g (c.representation (ρ a)) =
      c.representation (ρ (α₁.automorphism g a))
    rw [hρ]
    exact c.representation_equivariant g (ρ a)
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact a := c.selfadjoint_mod_compact (ρ a)
  square_mod_compact a := c.square_mod_compact (ρ a)
  commutator_compact a := c.commutator_compact (ρ a)
  equivariance_mod_compact g a := c.equivariance_mod_compact g (ρ a)

@[simp] theorem pullback_operator (c : KasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (c.pullback ρ hρ).operator = c.operator := rfl

@[simp] theorem pullback_representation (c : KasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) (a : A₁) :
    (c.pullback ρ hρ).representation a = c.representation (ρ a) := rfl

@[simp] theorem pullback_grading (c : KasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (c.pullback ρ hρ).grading = c.grading := rfl

@[simp] theorem pullback_groupAction (c : KasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (c.pullback ρ hρ).groupAction = c.groupAction := rfl

/-- Identity pullback is the original cycle, with all module data retained. -/
@[simp] theorem pullback_id (c : KasparovCycle α β E) :
    c.pullback (NonUnitalStarAlgHom.id ℂ A) (fun _ _ => rfl) = c := by
  cases c
  rfl

/-- Successive precompositions agree with precomposition by the composite. -/
theorem pullback_comp (c : KasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a))
    (σ : A₂ →⋆ₙₐ[ℂ] A₁)
    (hσ : ∀ g a, σ (α₂.automorphism g a) = α₁.automorphism g (σ a)) :
    (c.pullback ρ hρ).pullback σ hσ =
      c.pullback (ρ.comp σ) (fun g a => by
        change ρ (σ (α₂.automorphism g a)) = α.automorphism g (ρ (σ a))
        rw [hσ, hρ]) := rfl

/-- Degenerate cycles stay degenerate under source precomposition. -/
theorem pullback_isDegenerate (c : KasparovCycle α β E) (hc : c.IsDegenerate)
    (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (c.pullback ρ hρ).IsDegenerate :=
  ⟨fun a => hc.1 (ρ a), fun a => hc.2.1 (ρ a),
    fun a => hc.2.2.1 (ρ a), fun g a => hc.2.2.2 g (ρ a)⟩

/-- Every admissible operator remains admissible after restricting the representation. -/
theorem OperatorConditions.pullback {c : KasparovCycle α β E}
    {T : AdjointableMap B E E} (hT : c.OperatorConditions T)
    (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (c.pullback ρ hρ).OperatorConditions T where
  operator_odd := hT.operator_odd
  selfadjoint_mod_compact a := hT.selfadjoint_mod_compact (ρ a)
  square_mod_compact a := hT.square_mod_compact (ρ a)
  commutator_compact a := hT.commutator_compact (ρ a)
  equivariance_mod_compact g a := hT.equivariance_mod_compact g (ρ a)

end KasparovCycle

namespace OddKasparovCycle

/-- Precompose an odd raw cycle with an actual equivariant source homomorphism. -/
def pullback (c : OddKasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    OddKasparovCycle α₁ β E where
  countablyGenerated := c.countablyGenerated
  groupAction := c.groupAction
  representation := c.representation.comp ρ
  representation_equivariant := by
    intro g a
    change c.groupAction.conjugateOperator g (c.representation (ρ a)) =
      c.representation (ρ (α₁.automorphism g a))
    rw [hρ]
    exact c.representation_equivariant g (ρ a)
  operator := c.operator
  selfadjoint_mod_compact a := c.selfadjoint_mod_compact (ρ a)
  square_mod_compact a := c.square_mod_compact (ρ a)
  commutator_compact a := c.commutator_compact (ρ a)
  equivariance_mod_compact g a := c.equivariance_mod_compact g (ρ a)

@[simp] theorem pullback_operator (c : OddKasparovCycle α β E) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (c.pullback ρ hρ).operator = c.operator := rfl

@[simp] theorem pullback_representation (c : OddKasparovCycle α β E)
    (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) (a : A₁) :
    (c.pullback ρ hρ).representation a = c.representation (ρ a) := rfl

@[simp] theorem pullback_id (c : OddKasparovCycle α β E) :
    c.pullback (NonUnitalStarAlgHom.id ℂ A) (fun _ _ => rfl) = c := by
  cases c
  rfl

/-- Exact degeneracy is preserved in the odd picture too. -/
theorem pullback_isDegenerate (c : OddKasparovCycle α β E) (hc : c.IsDegenerate)
    (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (c.pullback ρ hρ).IsDegenerate :=
  ⟨fun a => hc.1 (ρ a), fun a => hc.2.1 (ρ a),
    fun a => hc.2.2.1 (ρ a), fun g a => hc.2.2.2 g (ρ a)⟩

end OddKasparovCycle

namespace KasparovOperatorHomotopy

/-- Pullback preserves the actual continuous operator path and every parameter's cycle conditions. -/
def pullback {c : KasparovCycle α β E} {T₀ T₁ : AdjointableMap B E E}
    (h : KasparovOperatorHomotopy c T₀ T₁) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    KasparovOperatorHomotopy (c.pullback ρ hρ) T₀ T₁ where
  path := h.path
  conditions t := (h.conditions t).pullback ρ hρ

@[simp] theorem pullback_path {c : KasparovCycle α β E} {T₀ T₁ : AdjointableMap B E E}
    (h : KasparovOperatorHomotopy c T₀ T₁) (ρ : A₁ →⋆ₙₐ[ℂ] A)
    (hρ : ∀ g a, ρ (α₁.automorphism g a) = α.automorphism g (ρ a)) :
    (h.pullback ρ hρ).path = h.path := rfl

end KasparovOperatorHomotopy
end BC4lean.KKTheory
