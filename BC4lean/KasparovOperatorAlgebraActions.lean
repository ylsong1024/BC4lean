import BC4lean.KasparovCountableClosureControls

/-! # Genuine action restrictions for the augmented coefficient algebras

Ambient action invariance gives actual restricted star automorphisms.
The compact algebra's two-sided ideal property and its grading/action
stability are the proved module-operator properties. Grading images of
normalizers still normalize a grading-stable augmented algebra.
-/

noncomputable section
namespace BC4lean.KKTheory

section Restriction
variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Restrict an actual ambient star automorphism to an invariant star
subalgebra, with the actual inverse restriction. -/
def restrictStarAlgEquiv (S : NonUnitalStarSubalgebra ℂ A) (ρ : A ≃⋆ₐ[ℂ] A)
    (hρ : ∀ a ∈ S, ρ a ∈ S) (hρinv : ∀ a ∈ S, ρ.symm a ∈ S) : S ≃⋆ₐ[ℂ] S where
  toFun := fun a => ⟨ρ a, hρ a a.property⟩
  invFun := fun a => ⟨ρ.symm a, hρinv a a.property⟩
  left_inv := fun a => Subtype.ext (ρ.symm_apply_apply a)
  right_inv := fun a => Subtype.ext (ρ.apply_symm_apply a)
  map_mul' := fun a b => Subtype.ext (map_mul ρ (a : A) (b : A))
  map_add' := fun a b => Subtype.ext (map_add ρ (a : A) (b : A))
  map_star' := fun a => Subtype.ext (map_star ρ (a : A))
  map_smul' := fun c a => Subtype.ext (map_smul ρ c (a : A))

@[simp] theorem restrictStarAlgEquiv_apply (S : NonUnitalStarSubalgebra ℂ A)
    (ρ : A ≃⋆ₐ[ℂ] A) (hρ : ∀ a ∈ S, ρ a ∈ S) (hρinv : ∀ a ∈ S, ρ.symm a ∈ S) (a : S) :
    (restrictStarAlgEquiv S ρ hρ hρinv a : A) = ρ a := rfl

/-- The actual grading-image normalizer is obtained by conjugating the
normalizer identity, using grading stability of the algebra. -/
theorem gradingImage_normalizes
    (S : NonUnitalStarSubalgebra ℂ A) (σ : A ≃⋆ₐ[ℂ] A)
    (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (d : A)
    (hd : ∀ a ∈ S, d * a - a * d ∈ S) :
    ∀ a ∈ S, σ d * a - a * σ d ∈ S := by
  intro a ha
  have h := hS _ (hd (σ a) (hS a ha))
  simpa only [map_sub, map_mul, hσ] using h

end Restriction

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The actual compact endomorphism algebra satisfies every ideal
property used in the generated-algebra augmentation. -/
theorem compactModuleOperatorAlgebra_isClosedTwoSidedStarIdeal :
    IsClosedTwoSidedStarIdeal (compactModuleOperatorAlgebra (B := B) (E := E)) where
  closed := moduleCompact_isClosed
  left_mul := fun a {_k} hk => comp_mem_moduleCompact a hk
  right_mul := fun a {_k} hk => mem_moduleCompact_comp hk a

section Grading
variable {β : CStarGrading B}

theorem grading_preserves_compactModuleOperatorAlgebra (γ : GradedHilbertModule β E) :
    ∀ a ∈ compactModuleOperatorAlgebra (B := B) (E := E),
      γ.conjugateOperatorStarAlgEquiv a ∈ compactModuleOperatorAlgebra (B := B) (E := E) :=
  fun _ ha => γ.conjugateOperator_mem_moduleCompact ha

theorem grading_preserves_augmentedOperatorAlgebra
    (γ : GradedHilbertModule β E)
    (S : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    (hS : ∀ a ∈ S, γ.conjugateOperator a ∈ S) :
    ∀ a ∈ generatedClosedStarAlgebra S (compactModuleOperatorAlgebra (B := B) (E := E)),
      γ.conjugateOperator a ∈
        generatedClosedStarAlgebra S (compactModuleOperatorAlgebra (B := B) (E := E)) :=
  maps_generatedClosedStarAlgebra S (compactModuleOperatorAlgebra (B := B) (E := E))
    γ.conjugateOperatorStarAlgEquiv hS (grading_preserves_compactModuleOperatorAlgebra γ)

end Grading

section ActualAction
variable {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ B}

theorem action_preserves_augmentedOperatorAlgebra
    (U : EquivariantHilbertModule α E) (g : Γ)
    (S : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    (hS : ∀ a ∈ S, U.conjugateOperator g a ∈ S) :
    ∀ a ∈ generatedClosedStarAlgebra S (compactModuleOperatorAlgebra (B := B) (E := E)),
      U.conjugateOperator g a ∈
        generatedClosedStarAlgebra S (compactModuleOperatorAlgebra (B := B) (E := E)) :=
  maps_generatedClosedStarAlgebra S (compactModuleOperatorAlgebra (B := B) (E := E))
    (U.conjugateOperatorStarAlgEquiv g) hS (fun _ ha => U.conjugateOperator_mem_moduleCompact g ha)

end ActualAction
end BC4lean.KKTheory
