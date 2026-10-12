import BC4lean.CompactFirstModuleConnection

/-! # Actual coefficient commutators of a connection anticommutator

The compact graded coefficient error of the first operator is not assumed
compact after tensoring. The true signed connection transfers its graded
intertwining error through the actual first compact ideal. This proves that
the even anticommutator commutes with the induced coefficient representation
modulo actual module compacts, as needed for localized positive-part CFC.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {A B C E F : Type*}
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {δA : CStarGrading A} {δB : CStarGrading B}

theorem gradedTensorAnticommutator_commutator_isModuleCompact
    (J : GradedHilbertModule δB E)
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hρ : ∀ a x, J.grading (ρ a x) = ρ (δA.automorphism a) (J.grading x))
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (S : AdjointableMap B E E) (hSodd : J.IsOdd J S)
    (U : AdjointableMap C F F)
    (T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hT : IsSignedModuleConnection J φ U T)
    (hScomm : ∀ a, IsModuleCompact (S * ρ a - ρ (δA.automorphism a) * S))
    (hTcomm : ∀ a, IsModuleCompact (T * interiorModuleTensorOperator φ (ρ a) -
      interiorModuleTensorOperator φ (ρ (δA.automorphism a)) * T))
    (a : A) :
    IsModuleCompact ((interiorModuleTensorOperator φ S * T + T * interiorModuleTensorOperator φ S) *
      interiorModuleTensorOperator φ (ρ a) - interiorModuleTensorOperator φ (ρ a) *
        (interiorModuleTensorOperator φ S * T + T * interiorModuleTensorOperator φ S)) := by
  let k := fun b : A => S * ρ b - ρ (δA.automorphism b) * S
  have hσ : J.conjugateOperator (k a) = -k (δA.automorphism a) := by
    apply AdjointableMap.ext
    intro x
    simp only [k, GradedHilbertModule.conjugateOperator_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, map_sub,
      AdjointableMap.coe_neg_apply]
    rw [hSodd (ρ a (J.grading x)), hρ a (J.grading x), J.grading_sq,
      hρ (δA.automorphism a) (S (J.grading x)), hSodd (J.grading x), J.grading_sq]
    simp only [CStarGrading.automorphism_sq]
    rw [(ρ a).toCLM.map_neg]
    abel
  have hk := hT.graded_commutator_compact (hScomm a)
  have hσtensor : interiorModuleTensorOperator φ (J.conjugateOperator (k a)) =
      -interiorModuleTensorOperator φ (k (δA.automorphism a)) := by
    rw [hσ]
    exact map_neg (interiorModuleTensorOperatorHom φ) _
  change IsModuleCompact (T * interiorModuleTensorOperator φ (k a) -
    interiorModuleTensorOperator φ (J.conjugateOperator (k a)) * T) at hk
  rw [hσtensor] at hk
  have h := (((hTcomm a).comp_left (interiorModuleTensorOperator φ S)).add
    ((hTcomm (δA.automorphism a)).comp_right (interiorModuleTensorOperator φ S))).add hk
  convert h using 1
  rw [CStarGrading.automorphism_sq]
  change _ = interiorModuleTensorOperator φ S *
      (T * interiorModuleTensorOperator φ (ρ a) -
        interiorModuleTensorOperator φ (ρ (δA.automorphism a)) * T) +
    (T * interiorModuleTensorOperator φ (ρ (δA.automorphism a)) -
        interiorModuleTensorOperator φ (ρ a) * T) * interiorModuleTensorOperator φ S +
    (T * interiorModuleTensorOperator φ (k a) -
      (-interiorModuleTensorOperator φ (k (δA.automorphism a))) * T)
  have hl (b : A) : interiorModuleTensorOperator φ (k b) =
      interiorModuleTensorOperator φ S * interiorModuleTensorOperator φ (ρ b) -
        interiorModuleTensorOperator φ (ρ (δA.automorphism b)) * interiorModuleTensorOperator φ S := by
    change interiorModuleTensorOperatorHom φ (S * ρ b - ρ (δA.automorphism b) * S) = _
    simp only [map_sub, map_mul, interiorModuleTensorOperatorHom_apply]
  rw [hl, hl, CStarGrading.automorphism_sq]
  noncomm_ring

end BC4lean.KKTheory
