import BC4lean.KasparovTripleSandwichAlgebra
import BC4lean.SignedConnectionMultiplierAlgebra

/-! # Ordinary triple normalizers derived from the original connections

The two genuine signed connection laws put the right product times each
original compact-AU term in the right sandwich family. The first-pair
connection does the same in the middle-tensored sandwich family. Their
independent adjoint laws supply the reverse products. The actual common
approximate unit then proves ordinary normalization of the whole enlarged
algebra. No cross-normalizer assumption or associativity is used.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open InteriorModuleTensorAssociator
open TopologicalSpace

variable {B C D E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [SeparableSpace B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  {δB : CStarGrading B}
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)
  (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
  (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
  (hE : IsCountablyGeneratedModule B E)

include hE in
/-- Every actual bounded first-factor operator normalizes the entire
triple algebra through compactness of its products with the first AU. -/
theorem doubleTensorOperator_normalizes_normalizerFirstAlgebra (O : AdjointableMap B E E) :
    ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      doubleTensorOperator φ ψ O * T - T * doubleTensorOperator φ ψ O ∈
        normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  apply normalizes_normalizerFirstAlgebra_of_compact_products φ ψ S₂ S₃ S₂₃ hE
  · intro k hk
    have h := firstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
      (doubleTensorCompact_mem_firstAlgebra φ ψ (mul_mem_moduleCompact_left O hk))
    simpa only [doubleTensorOperator, interiorModuleTensorOperator_mul] using h
  · intro k hk
    have h := firstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
      (doubleTensorCompact_mem_firstAlgebra φ ψ (mul_mem_moduleCompact_right hk O))
    simpa only [doubleTensorOperator, interiorModuleTensorOperator_mul] using h

include hE in
/-- The actual first-pair connection is an ordinary normalizer; the
necessary F₂-middle sandwich family is included explicitly. -/
theorem pairTensorConnection_normalizes_normalizerFirstAlgebra
    (J : GradedHilbertModule δB E)
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hQ : IsSignedModuleConnection J φ S₂ Q) (hS₂ : IsSelfAdjoint S₂) :
    ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      interiorModuleTensorOperator ψ Q * T - T * interiorModuleTensorOperator ψ Q ∈
        normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  apply normalizes_normalizerFirstAlgebra_of_compact_products φ ψ S₂ S₃ S₂₃ hE
  · intro k hk
    have h := middleTensorSandwichAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
      (tensorFirstPairSandwich_mem_middleTensorSandwichAlgebra φ ψ S₂
        (hQ.mul_tensorCompact_mem_firstProductAlgebra hk))
    simpa only [doubleTensorOperator, interiorModuleTensorOperator_mul] using h
  · intro k hk
    have h := middleTensorSandwichAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
      (tensorFirstPairSandwich_mem_middleTensorSandwichAlgebra φ ψ S₂
        (hQ.tensorCompact_mul_mem_firstProductAlgebra_of_selfadjoint_second hS₂ hk))
    simpa only [doubleTensorOperator, interiorModuleTensorOperator_mul] using h

include hE in
/-- The arbitrary right iterated product's actual signed connection
makes its associator pullback an ordinary normalizer of the full algebra. -/
theorem rightConnection_normalizes_normalizerFirstAlgebra
    (J : GradedHilbertModule δB E)
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (hR : IsSignedModuleConnection J (rightRepresentation φ ψ) S₂₃ R)
    (hS₂₃ : IsSelfAdjoint S₂₃) :
    ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      (hilbertEquiv φ ψ).symm.transport R * T - T * (hilbertEquiv φ ψ).symm.transport R ∈
        normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  apply normalizes_normalizerFirstAlgebra_of_compact_products φ ψ S₂ S₃ S₂₃ hE
  · intro k hk
    apply enlargedFirstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
    apply rightSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
    change (hilbertEquiv φ ψ).transport
      ((hilbertEquiv φ ψ).symm.transport R * doubleTensorOperator φ ψ k) ∈
      firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃
    rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_symm_symm,
      doubleTensorOperator, hilbertEquiv_transport_operator]
    exact hR.mul_tensorCompact_mem_firstProductAlgebra hk
  · intro k hk
    apply enlargedFirstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
    apply rightSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
    change (hilbertEquiv φ ψ).transport
      (doubleTensorOperator φ ψ k * (hilbertEquiv φ ψ).symm.transport R) ∈
      firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃
    rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_symm_symm,
      doubleTensorOperator, hilbertEquiv_transport_operator]
    exact hR.tensorCompact_mul_mem_firstProductAlgebra_of_selfadjoint_second hS₂₃ hk

end BC4lean.KKTheory.KasparovTriple
