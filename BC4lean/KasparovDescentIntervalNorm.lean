import BC4lean.KasparovDescentIntervalModule
import BC4lean.KasparovDescentReducedRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The interval reduced-source bound from genuine ordinary fibre bounds

The construction uses the imported concrete reducedSourceRepresentation on
each actual evaluated fibre; it does not assume an arbitrary crossed
representation or a norm-bound field.


The direct interval module norm is determined by evaluation of its actual
continuous coefficient inner product. Thus the ordinary reduced bound at
each fibre yields the global reduced bound, without a crossed path-algebra
isomorphism. No full KK descent map is defined here.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]

variable (β : CStarAlgebraAction Γ B) (M : Type*)
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

theorem intervalAlgebraicSourceOperatorHom_reducedNorm_le
    (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (f : AlgebraicCrossedProduct α) :
    ‖intervalAlgebraicSourceOperatorHom β M α U π hπ f‖ ≤ algebraicCrossedReducedNorm α f := by
  change ‖(intervalAlgebraicSourceOperatorHom β M α U π hπ f).toCLM‖ ≤ _
  have hK : 0 ≤ algebraicCrossedReducedNorm α f := norm_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro u
  apply intervalNorm_le_of_evaluations β M _ _ (mul_nonneg hK (norm_nonneg u))
  intro t
  rw [intervalEvaluation_algebraic]
  have ht :
      ‖algebraicSourceOperatorHom β (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation M π t)
        (fibreSourceRepresentation_equivariant β M α U π hπ t) f‖ ≤
      algebraicCrossedReducedNorm α f := by
    rw [← reducedSourceRepresentation_algebraic]
    change ‖reducedSourceRepresentation β (HilbertModuleFibre B M t) α (U.fibre t)
      (fibreSourceRepresentation M π t)
      (fibreSourceRepresentation_equivariant β M α U π hπ t)
        (algebraicToReducedCrossed α f)‖ ≤ ‖algebraicToReducedCrossed α f‖
    exact NonUnitalStarAlgHom.norm_apply_le _ _
  calc
    _ ≤ ‖algebraicSourceOperatorHom β (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation M π t)
        (fibreSourceRepresentation_equivariant β M α U π hπ t) f‖ *
        ‖intervalEvaluation β M t u‖ := AdjointableMap.norm_apply_le _ _
    _ ≤ algebraicCrossedReducedNorm α f * ‖u‖ :=
      mul_le_mul ht
        (GradedMatrixMoritaFibreTensor.evaluation_norm_le (coefficientRepresentation β) t u)
        (norm_nonneg _) hK

end BC4lean.KKTheory.KasparovDescent
