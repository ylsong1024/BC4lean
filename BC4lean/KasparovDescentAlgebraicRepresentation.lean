import BC4lean.KasparovDescentAction
import BC4lean.CovariantAlgebraicRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Finite integration on the actual descended module

The generic finite integration theorem is specialized to the constructed
balanced group action and coefficient representation. Its equivariance
hypothesis is discharged by the proved concrete covariance. No reduced norm
bound or completed source representation is assumed here.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
variable (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

theorem sourceGenerator_mul (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (a b : A) (g h : Γ) :
    sourceGenerator β E U π a g * sourceGenerator β E U π b h =
      sourceGenerator β E U π (a * α.automorphism g b) (g * h) := by
  simpa only [covariantGenerator, sourceGenerator, groupOperator] using
    covariantGenerator_mul (groupAction β E U) (sourceRepresentation β E π) α
      (sourceRepresentation_equivariant β E α U π hπ) a b g h

theorem sourceGenerator_star (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (a : A) (g : Γ) :
    star (sourceGenerator β E U π a g) =
      sourceGenerator β E U π (α.automorphism g⁻¹ (star a)) g⁻¹ := by
  simpa only [covariantGenerator, sourceGenerator, groupOperator] using
    covariantGenerator_star (groupAction β E U) (sourceRepresentation β E π) α
      (sourceRepresentation_equivariant β E α U π hπ) a g

def algebraicSourceOperatorLinear (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    AlgebraicCrossedProduct α →ₗ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
  covariantAlgebraicLinear (groupAction β E U) (sourceRepresentation β E π) α

@[simp] theorem algebraicSourceOperatorLinear_single (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (g : Γ) (a : A) :
    algebraicSourceOperatorLinear β E α U π (AlgebraicCrossedProduct.single α g a) =
      sourceGenerator β E U π a g :=
  covariantAlgebraicLinear_single (groupAction β E U) (sourceRepresentation β E π) α g a

theorem algebraicSourceOperatorLinear_mul (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (f h : AlgebraicCrossedProduct α) :
    algebraicSourceOperatorLinear β E α U π (f * h) =
      algebraicSourceOperatorLinear β E α U π f * algebraicSourceOperatorLinear β E α U π h :=
  covariantAlgebraicLinear_mul (groupAction β E U) (sourceRepresentation β E π) α
    (sourceRepresentation_equivariant β E α U π hπ) f h

theorem algebraicSourceOperatorLinear_star (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (f : AlgebraicCrossedProduct α) :
    algebraicSourceOperatorLinear β E α U π (star f) = star (algebraicSourceOperatorLinear β E α U π f) :=
  covariantAlgebraicLinear_star (groupAction β E U) (sourceRepresentation β E π) α
    (sourceRepresentation_equivariant β E α U π hπ) f

/-- The genuine finite integrated nonunital star homomorphism. -/
def algebraicSourceOperatorHom (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a)) :
    AlgebraicCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
  covariantAlgebraicRepresentation (groupAction β E U) (sourceRepresentation β E π) α
    (sourceRepresentation_equivariant β E α U π hπ)

@[simp] theorem algebraicSourceOperatorHom_single (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a)) (g : Γ) (a : A) :
    algebraicSourceOperatorHom β E α U π hπ (AlgebraicCrossedProduct.single α g a) =
      sourceGenerator β E U π a g :=
  covariantAlgebraicRepresentation_single (groupAction β E U) (sourceRepresentation β E π) α
    (sourceRepresentation_equivariant β E α U π hπ) g a

theorem algebraicSourceOperatorHom_eq_sum (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (f : AlgebraicCrossedProduct α) :
    algebraicSourceOperatorHom β E α U π hπ f =
      ∑ g ∈ (AlgebraicCrossedProduct.coeff α f).support,
        sourceGenerator β E U π (AlgebraicCrossedProduct.coeff α f g) g := rfl

end BC4lean.KKTheory.KasparovDescent
