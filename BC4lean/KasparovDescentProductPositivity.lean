import BC4lean.KasparovDescentReducedRepresentation
import BC4lean.ReducedCrossedCoefficientApproximateUnit
import BC4lean.EssentialModulePositivityClosed

/-! # Full quadratic positivity after genuine reduced descent



The original positivity condition is retained for every original source
coefficient. Its actual compact-preserving tensor image is compressed by an
arbitrary element of the completed crossed source representation. The proved
two-sided coefficient approximate unit makes those localizers converge in
operator norm to the arbitrary crossed localizer. Closedness of the actual
positive-lift condition proves the full quadratic crossed-source condition.

This argument does not replace positivity for sums by generatorwise
positivity. No invariance of the operator P under the group is required.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open Filter
open scoped Topology KasparovDescent

variable {Γ A B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (α : CStarAlgebraAction Γ A) (U : EquivariantHilbertModule β E)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
  (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))

/-- Right localization by the actual represented source coefficient
approximate unit converges in norm, even if π is degenerate. -/
theorem reducedSourceRepresentation_mul_coefficient_tendsto (z : ReducedCrossedProduct α) :
    Tendsto (fun e : A => reducedSourceRepresentation β E α U π hπ z *
      operatorHom β E (π e))
      (CStarAlgebra.approximateUnit A)
      (𝓝 (reducedSourceRepresentation β E α U π hπ z)) := by
  have h := ((continuous_reducedSourceRepresentation β E α U π hπ).tendsto z).comp
    (tendsto_mul_coefficientToReducedCrossed_approximateUnit α z)
  simpa only [Function.comp_def, map_mul, reducedSourceRepresentation_coefficient, sourceRepresentation_apply]
    using h

/-- The left represented coefficient localizations likewise converge in
norm. This uses the actual crossed-algebra approximate unit. -/
theorem reducedSourceRepresentation_coefficient_mul_tendsto (z : ReducedCrossedProduct α) :
    Tendsto (fun e : A => operatorHom β E (π e) *
      reducedSourceRepresentation β E α U π hπ z)
      (CStarAlgebra.approximateUnit A)
      (𝓝 (reducedSourceRepresentation β E α U π hπ z)) := by
  have h := ((continuous_reducedSourceRepresentation β E α U π hπ).tendsto z).comp
    (tendsto_coefficientToReducedCrossed_approximateUnit_mul α z)
  simpa only [Function.comp_def, map_mul, reducedSourceRepresentation_coefficient, sourceRepresentation_apply]
    using h

/-- The actual tensor operator homomorphism transports original positive
lifts because its preservation of module compacts is already proved. -/
theorem operatorHom_positiveModulo {P : AdjointableMap B E E}
    (hP : IsPositiveModuloModuleCompact P) :
    IsPositiveModuloModuleCompact (operatorHom β E P) :=
  IsPositiveModuloModuleCompact.map_of_compact (operatorHom β E)
    (fun _ hK => operatorHom_compact β E hK) hP

/-- FULL quadratic source positivity survives actual reduced descent.
The conclusion quantifies over every element of the completed source
crossed product; no source equivariance of P is assumed. -/
theorem reducedSourceRepresentation_quadratic_positive
    (P : AdjointableMap B E E)
    (hP : ∀ a : A, IsPositiveModuloModuleCompact (π a * P * star (π a)))
    (z : ReducedCrossedProduct α) :
    IsPositiveModuloModuleCompact
      (reducedSourceRepresentation β E α U π hπ z * operatorHom β E P *
        star (reducedSourceRepresentation β E α U π hπ z)) := by
  have hlocalized (e : A) : IsPositiveModuloModuleCompact
      ((reducedSourceRepresentation β E α U π hπ z * operatorHom β E (π e)) *
        operatorHom β E P *
        star (reducedSourceRepresentation β E α U π hπ z * operatorHom β E (π e))) := by
    have htransport : IsPositiveModuloModuleCompact
        (operatorHom β E (π e) * operatorHom β E P * star (operatorHom β E (π e))) := by
      simpa only [map_mul, map_star] using operatorHom_positiveModulo β E (hP e)
    simpa only [star_mul, mul_assoc] using
      htransport.star_right_conjugate (reducedSourceRepresentation β E α U π hπ z)
  have hlocalizer := reducedSourceRepresentation_mul_coefficient_tendsto β E α U π hπ z
  have hlimit := (hlocalizer.mul
      (tendsto_const_nhds : Tendsto (fun _ : A => operatorHom β E P)
        (CStarAlgebra.approximateUnit A) (𝓝 (operatorHom β E P)))).mul hlocalizer.star
  exact IsPositiveModuloModuleCompact.of_tendsto hlimit (Eventually.of_forall hlocalized)

/-- In particular, the full anticommutator positivity condition required by
the Kasparov product is preserved before applying the genuine product-module
comparison unitary. -/
theorem reducedSourceRepresentation_anticommutator_positive
    (S T : AdjointableMap B E E)
    (hST : ∀ a : A, IsPositiveModuloModuleCompact
      (π a * (S * T + T * S) * star (π a)))
    (z : ReducedCrossedProduct α) :
    IsPositiveModuloModuleCompact
      (reducedSourceRepresentation β E α U π hπ z *
        (operatorHom β E S * operatorHom β E T + operatorHom β E T * operatorHom β E S) *
        star (reducedSourceRepresentation β E α U π hπ z)) := by
  simpa only [map_add, map_mul] using
    reducedSourceRepresentation_quadratic_positive β E α U π hπ (S * T + T * S) hST z

end BC4lean.KKTheory.KasparovDescent
