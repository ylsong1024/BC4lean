import BC4lean.KasparovTripleResidualLocality
import BC4lean.KasparovProductAlgebras
import BC4lean.KasparovTripleSandwichAlgebra

/-! # The concrete two-creation local algebra of the triple tensor

The associativity residual has genuine compact tests on both the original
first-module creation ranges and the first-pair creation ranges. Their closed
star-algebra intersection annihilates every middle-tensored sandwich family,
as well as both direct sandwich families. This establishes the compact ideal
product needed for the enlarged first technical algebra.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open InteriorModuleTensorAssociator
open GradedTripleAnticommutatorConnection
open RectangularInteriorModuleTensorOperator
open scoped CStarAlgebra

variable {B C D E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)

def bothCreationLocalAlgebra : NonUnitalStarSubalgebra ℂ
    (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  (creationLocallyCompactAlgebra (E := E) (rightRepresentation φ ψ)).comap
    (hilbertEquiv (E := E) φ ψ).transportStarAlgEquiv.toNonUnitalStarAlgHom ⊓
    creationLocallyCompactAlgebra (E := InteriorModuleTensor (E := E) φ) ψ

theorem bothCreationLocalAlgebra_isClosed :
    IsClosed (bothCreationLocalAlgebra (E := E) φ ψ :
      Set (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
  ((creationLocallyCompactAlgebra_isClosed (rightRepresentation φ ψ)).preimage
    (StarAlgEquiv.isometry
      (hilbertEquiv (E := E) φ ψ).transportStarAlgEquiv).continuous).inter
      (creationLocallyCompactAlgebra_isClosed ψ)

/-- The actual associator sends a middle-tensored sandwich to a sandwich
with the actual middle tensor operator. -/
theorem transport_tensor_creationSandwich (S : AdjointableMap C F F) (x y : E) :
    (hilbertEquiv (E := E) φ ψ).transport (interiorModuleTensorOperator ψ (creationSandwich φ S x y)) =
      creationSandwich (rightRepresentation φ ψ) (interiorModuleTensorOperator ψ S) x y := by
  let Ω := hilbertEquiv (E := E) φ ψ
  have hx := associator_tensor_creation φ ψ x
  have hy := congrArg AdjointableMap.adjoint (associator_tensor_creation φ ψ y)
  simp only [AdjointableMap.adjoint_comp, HilbertModuleEquiv.toAdjointable_adjoint,
    tensor_adjoint] at hy
  change Ω.toAdjointable.comp ((tensor ψ (creationSandwich φ S x y)).comp Ω.symm.toAdjointable) = _
  rw [creationSandwich, tensor_comp, tensor_comp, tensor_endo]
  rw [← AdjointableMap.comp_assoc, ← AdjointableMap.comp_assoc]
  rw [← AdjointableMap.comp_assoc Ω.toAdjointable
    (tensor ψ (moduleCreationMap φ x)) (interiorModuleTensorOperator ψ S), hx]
  rw [AdjointableMap.comp_assoc, AdjointableMap.comp_assoc, hy]
  rfl

theorem tensor_creationSandwich_products_compact
    (S : AdjointableMap C F F)
    {T : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)}
    (hT : T ∈ bothCreationLocalAlgebra φ ψ) (x y : E) :
    IsModuleCompact (interiorModuleTensorOperator ψ (creationSandwich φ S x y) * T) ∧
    IsModuleCompact (T * interiorModuleTensorOperator ψ (creationSandwich φ S x y)) := by
  let Ω := hilbertEquiv (E := E) φ ψ
  have h := creationSandwich_products_compact (rightRepresentation φ ψ)
    (interiorModuleTensorOperator ψ S) hT.1 x y
  constructor
  · apply (Ω.transport_isModuleCompact_iff _).mp
    rw [HilbertModuleEquiv.transport_mul, transport_tensor_creationSandwich]
    exact h.1
  · apply (Ω.transport_isModuleCompact_iff _).mp
    rw [HilbertModuleEquiv.transport_mul, transport_tensor_creationSandwich]
    exact h.2

/-- Every middle-tensored first-pair sandwich algebra annihilates the
actual intersection local algebra into the genuine triple compact ideal. -/
theorem middleTensor_firstProductAlgebra_products_compact
    (S : AdjointableMap C F F)
    {K : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}
    {T : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)}
    (hK : K ∈ firstProductAlgebra φ S) (hT : T ∈ bothCreationLocalAlgebra φ ψ) :
    IsModuleCompact (interiorModuleTensorOperator ψ K * T) ∧
    IsModuleCompact (T * interiorModuleTensorOperator ψ K) := by
  let localAlg := bothCreationLocalAlgebra (E := E) φ ψ
  let hKtr := compactTensorIdeal_isClosedTwoSided (E := InteriorModuleTensor (E := E) φ) ψ
  let P : NonUnitalStarSubalgebra ℂ
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
    hKtr.testMultiplierAlgebra
      (localAlg : Set (AdjointableMap D (LeftTensor (E := E) φ ψ)
        (LeftTensor (E := E) φ ψ))) (fun _ h => localAlg.star_mem' h)
  let Q := P.comap
    (interiorModuleTensorOperatorHom (E := InteriorModuleTensor (E := E) φ) ψ).toNonUnitalStarAlgHom
  have hP : IsClosed (P : Set (AdjointableMap D (LeftTensor (E := E) φ ψ)
      (LeftTensor (E := E) φ ψ))) :=
    hKtr.testMultiplierAlgebra_isClosed
      (localAlg : Set (AdjointableMap D (LeftTensor (E := E) φ ψ)
        (LeftTensor (E := E) φ ψ))) (fun _ h => localAlg.star_mem' h)
  have hQ : IsClosed (Q : Set (AdjointableMap C (InteriorModuleTensor (E := E) φ)
      (InteriorModuleTensor (E := E) φ))) := by
    change IsClosed
      ((interiorModuleTensorOperatorCLM (E := InteriorModuleTensor (E := E) φ) ψ) ⁻¹'
        (P : Set (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))))
    exact hP.preimage
      (interiorModuleTensorOperatorCLM (E := InteriorModuleTensor (E := E) φ) ψ).continuous
  have hle : firstProductAlgebra φ S ≤ Q := by
    apply closedNonUnitalStarAdjoin_le _ Q hQ
    intro L hL V hV
    rcases hL with (hL | hL) | hL
    · obtain ⟨⟨x, y⟩, rfl⟩ := hL
      exact tensor_creationSandwich_products_compact φ ψ 1 hV x y
    · obtain ⟨⟨x, y⟩, rfl⟩ := hL
      exact tensor_creationSandwich_products_compact φ ψ S hV x y
    · exact ⟨IsCreationLocallyCompact.tensorCompact_mul hV.2 hL,
        IsCreationLocallyCompact.mul_tensorCompact hV.2 hL⟩
  exact hle hK T hT

set_option maxHeartbeats 1200000 in
/-- All three concrete sandwich families, and their generated closure,
annihilate the two-creation local algebra into actual triple compacts. -/
theorem normalizerFirstAlgebra_products_compact
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    {L T : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)}
    (hL : L ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃)
    (hT : T ∈ bothCreationLocalAlgebra φ ψ) :
    IsModuleCompact (L * T) ∧ IsModuleCompact (T * L) := by
  let Ω := hilbertEquiv (E := E) φ ψ
  let localAlg := bothCreationLocalAlgebra (E := E) φ ψ
  let hK := compactTensorIdeal_isClosedTwoSided (E := InteriorModuleTensor (E := E) φ) ψ
  let P : NonUnitalStarSubalgebra ℂ
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
    hK.testMultiplierAlgebra
      (localAlg : Set (AdjointableMap D (LeftTensor (E := E) φ ψ)
        (LeftTensor (E := E) φ ψ))) (fun _ h => localAlg.star_mem' h)
  have hP : IsClosed (P : Set (AdjointableMap D (LeftTensor (E := E) φ ψ)
      (LeftTensor (E := E) φ ψ))) :=
    hK.testMultiplierAlgebra_isClosed
      (localAlg : Set (AdjointableMap D (LeftTensor (E := E) φ ψ)
        (LeftTensor (E := E) φ ψ))) (fun _ h => localAlg.star_mem' h)
  have hleft : leftSandwichAlgebra φ ψ S₃ ≤ P := by
    intro a ha V hV
    exact firstProductAlgebra_products_compact ψ S₃ ha hV.2
  have hright : rightSandwichAlgebra φ ψ S₂₃ ≤ P := by
    intro a ha V hV
    have ha' : Ω.transport a ∈
        firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃ := ha
    have hV' : IsCreationLocallyCompact (E := E) (rightRepresentation φ ψ)
        (Ω.transport V) := hV.1
    have h := firstProductAlgebra_products_compact (E := E)
      (rightRepresentation φ ψ) S₂₃ (a := Ω.transport a) (T := Ω.transport V) ha' hV'
    constructor
    · apply (Ω.transport_isModuleCompact_iff _).mp
      rw [HilbertModuleEquiv.transport_mul]
      exact h.1
    · apply (Ω.transport_isModuleCompact_iff _).mp
      rw [HilbertModuleEquiv.transport_mul]
      exact h.2
  have hbase : enlargedFirstAlgebra φ ψ S₃ S₂₃ ≤ P :=
    generatedClosedStarAlgebra_le _ _ P hP hleft hright
  have hmiddle : middleTensorSandwichAlgebra φ ψ S₂ ≤ P := by
    apply NonUnitalStarSubalgebra.topologicalClosure_minimal _ _ hP
    intro a ha V hV
    obtain ⟨K, hKmem, rfl⟩ := NonUnitalStarSubalgebra.mem_map.mp ha
    exact middleTensor_firstProductAlgebra_products_compact φ ψ S₂ hKmem hV
  have hle : normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ ≤ P :=
    generatedClosedStarAlgebra_le _ _ P hP hbase hmiddle
  exact hle hL T hT

end BC4lean.KKTheory.KasparovTriple
