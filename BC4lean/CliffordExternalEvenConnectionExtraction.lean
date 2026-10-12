import BC4lean.CliffordExternalEvenBalancedCompatibility
import BC4lean.CliffordPairFirstCorner
import BC4lean.GradedKasparovProductCriterion

/-! # Actual connection and positivity after odd-by-even coefficient extraction

The diagonal homogeneous vector (x,x) has actual whole creator (Tₓ,Tₓ)
under the balanced unitary. Genuine rectangular first-range restriction
therefore supplies both ordinary creator errors. Localized positive lifts
restrict through the actual first-corner star homomorphism. The resulting
positivity test uses the genuine Koszul first operator AK, not A alone.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenBalancedTensor

variable {B C H F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)
  (hφ : ∀ b, J.toAdjointable * φ b = φ b * J.toAdjointable)

theorem coordinateCreation_diagonal (x : H) :
    coordinateCreation φ J (cliffordPairMk x x) =
      cliffordPairMap (moduleCreationMap φ x) (moduleCreationMap φ x) := by
  have hp : (moduleCreationMap φ x).comp (plus J) +
      (moduleCreationMap φ x).comp (minus J) = moduleCreationMap φ x := by
    ext y
    change interiorModuleTensorMk φ x (plus J y) + interiorModuleTensorMk φ x (minus J y) =
      interiorModuleTensorMk φ x y
    rw [← map_add, plus_add_minus_apply]
  have hm : (moduleCreationMap φ x).comp (minus J) +
      (moduleCreationMap φ x).comp (plus J) = moduleCreationMap φ x := by
    rw [add_comm]
    exact hp
  change cliffordPairMap
      ((moduleCreationMap φ x).comp (plus J) + (moduleCreationMap φ x).comp (minus J))
      ((moduleCreationMap φ x).comp (minus J) + (moduleCreationMap φ x).comp (plus J)) =
    cliffordPairMap (moduleCreationMap φ x) (moduleCreationMap φ x)
  rw [hp, hm]

theorem firstCorner_connection
    (R : AdjointableMap (C × C) (SourceTensor (H := H) φ J hφ) (SourceTensor (H := H) φ J hφ))
    (D : AdjointableMap C F F) (x : H)
    (hc : IsModuleCompact
      ((moduleCreationMap (CliffordExternalEvenRepresentation.representation φ J hφ)
          (cliffordPairMk x x)).comp (cliffordPairMap D D) -
        R.comp (moduleCreationMap (CliffordExternalEvenRepresentation.representation φ J hφ)
          (cliffordPairMk x x)))) :
    IsModuleCompact ((moduleCreationMap φ x).comp D -
      (cliffordPairFirstCorner ((hilbertEquiv φ J hφ).transport R)).comp (moduleCreationMap φ x)) := by
  have h := cliffordPairFirstCorner_isModuleCompact
    (compact_creator_even φ J hφ R (cliffordPairMap D D) (cliffordPairMk x x) hc)
  simpa only [coordinateCreation_diagonal, cliffordPairFirstCorner_sub,
    cliffordPairFirstCorner_comp, cliffordPairFirstCorner_pair] using h

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (c : OddKasparovCycle α β H)
  (d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F)

theorem extracted_product_connection
    (R : AdjointableMap (C × C)
      (SourceTensor (H := H) d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d))
      (SourceTensor (H := H) d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d)))
    (hR : IsGradedKasparovProductOperator c.cliffordExpansion (CliffordExternalEvenCycle.cycle d) R)
    (x : H) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp d.operator -
      (cliffordPairFirstCorner ((hilbertEquiv d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)).transport R)).comp
          (moduleCreationMap d.representation x)) :=
  firstCorner_connection d.representation d.grading
    (CliffordExternalEvenCycle.representation_commutes_grading d) R d.operator x
    (hR.connection.even (cliffordPairMk x x) rfl)

theorem extracted_product_adjoint_connection
    (R : AdjointableMap (C × C)
      (SourceTensor (H := H) d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d))
      (SourceTensor (H := H) d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d)))
    (hR : IsGradedKasparovProductOperator c.cliffordExpansion (CliffordExternalEvenCycle.cycle d) R)
    (x : H) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp (star d.operator) -
      (star (cliffordPairFirstCorner ((hilbertEquiv d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)).transport R))).comp
          (moduleCreationMap d.representation x)) := by
  have hc := hR.connection.even_adjoint (cliffordPairMk x x) rfl
  change IsModuleCompact
    ((moduleCreationMap (CliffordExternalEvenRepresentation.representation d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)) (cliffordPairMk x x)).comp
      (star (cliffordPairMap d.operator d.operator)) -
      (star R).comp (moduleCreationMap
        (CliffordExternalEvenRepresentation.representation d.representation d.grading
          (CliffordExternalEvenCycle.representation_commutes_grading d)) (cliffordPairMk x x))) at hc
  rw [← cliffordPairMap_star] at hc
  simpa only [HilbertModuleEquiv.transport_star, cliffordPairFirstCorner_star] using
    firstCorner_connection d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d) (star R) (star d.operator) x hc

theorem extracted_product_positivity
    (R : AdjointableMap (C × C)
      (SourceTensor (H := H) d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d))
      (SourceTensor (H := H) d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d)))
    (hR : IsGradedKasparovProductOperator c.cliffordExpansion (CliffordExternalEvenCycle.cycle d) R)
    (a : A) :
    let p := interiorModuleTensorOperator d.representation (c.representation a)
    let AK := interiorModuleTensorOperator d.representation c.operator *
      (tensorGrading (H := H) d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)).toAdjointable
    let G := cliffordPairFirstCorner ((hilbertEquiv d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d)).transport R)
    IsPositiveModuloModuleCompact (p * (AK * G + G * AK) * star p) := by
  have ht := (hR.positivity a).transport
    (hilbertEquiv d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d))
  have h := ht.cliffordPairFirstCorner
  let ψ := CliffordExternalEvenRepresentation.representation d.representation d.grading
    (CliffordExternalEvenCycle.representation_commutes_grading d)
  let U := hilbertEquiv (H := H) d.representation d.grading
    (CliffordExternalEvenCycle.representation_commutes_grading d)
  let P := interiorModuleTensorOperator ψ
    (cliffordPairMap (c.representation a) (c.representation a))
  let T := interiorModuleTensorOperator ψ (cliffordPairMap c.operator (-c.operator))
  change IsPositiveModuloModuleCompact
    (cliffordPairFirstCornerHom (U.transport (P * (T * R + R * T) * star P))) at h
  simpa only [P, T, ψ, U,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_star,
    transport_diagonal_operator, transport_signed_operator, map_mul, map_add, map_star,
    cliffordPairFirstCornerHom_apply, cliffordPairFirstCorner_pair] using h

end BC4lean.KKTheory.CliffordExternalEvenBalancedTensor
