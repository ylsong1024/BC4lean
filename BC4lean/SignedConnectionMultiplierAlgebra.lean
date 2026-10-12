import BC4lean.CompactFirstModuleConnection
import BC4lean.KasparovProductAlgebras

/-! # Actual signed connections multiply first compact tensors into the sandwich algebra

The rank-one calculation puts a connection times a first compact tensor
in the genuine first-product algebra, using the actual compact creation
error and the second-operator sandwich. The norm-closed rectangular compact
span gives every first compact. The independent adjoint connection law gives
the other multiplication side. These are concrete memberships, not assumed
normalizer hypotheses.
-/

noncomputable section
namespace BC4lean.KKTheory.IsSignedModuleConnection

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {δB : CStarGrading B} {J : GradedHilbertModule δB E}
  {φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F} {S : AdjointableMap C F F}
  {R : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}

theorem mul_tensorCompact_mem_firstProductAlgebra
    (hR : IsSignedModuleConnection J φ S R) {K : AdjointableMap B E E} (hK : IsModuleCompact K) :
    R * interiorModuleTensorOperator φ K ∈ firstProductAlgebra φ S := by
  let L := (AdjointableMap.compLeftContinuousLinearMap R).comp (interiorModuleTensorOperatorCLM φ)
  let P := (firstProductAlgebra φ S).toSubmodule.comap L.toLinearMap
  have hP : IsClosed (P : Set (AdjointableMap B E E)) :=
    (firstProductAlgebra_isClosed φ S).preimage L.continuous
  have hθ (x y : E) : moduleRankOne (B := B) x y ∈ P := by
    change R * interiorModuleTensorOperator φ (moduleRankOne (B := B) x y) ∈ firstProductAlgebra φ S
    rw [interiorModuleTensorOperator_rankOne]
    have hcompact := (hR.creation x).comp_right (moduleCreationMap φ y).adjoint
    have hmem := (firstProductAlgebra φ S).add_mem
      (moduleCompact_le_firstProductAlgebra φ S hcompact)
      (creationSandwich_mem_firstProductAlgebra φ S (J.grading x) y)
    have heq : R * (moduleCreationMap φ x).comp (moduleCreationMap φ y).adjoint =
        (R.comp (moduleCreationMap φ x) - (moduleCreationMap φ (J.grading x)).comp S).comp
          (moduleCreationMap φ y).adjoint + creationSandwich φ S (J.grading x) y := by
      apply AdjointableMap.ext
      intro z
      simp only [creationSandwich, AdjointableMap.mul_apply, AdjointableMap.comp_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply]
      abel
    rw [heq]
    exact hmem
  exact moduleCompact_le_of_isClosed P hP hθ hK

theorem tensorCompact_mul_mem_firstProductAlgebra_of_selfadjoint_second
    (hR : IsSignedModuleConnection J φ S R) (hS : IsSelfAdjoint S)
    {K : AdjointableMap B E E} (hK : IsModuleCompact K) :
    interiorModuleTensorOperator φ K * R ∈ firstProductAlgebra φ S := by
  have hRstar : IsSignedModuleConnection J φ S (star R) :=
    ⟨by simpa only [hS.star_eq] using hR.creation_adjoint,
      by simpa only [star_star, hS.star_eq] using hR.creation⟩
  have h := star_mem (s := firstProductAlgebra φ S)
    (hRstar.mul_tensorCompact_mem_firstProductAlgebra hK.adjoint)
  have hstar : star (interiorModuleTensorOperator φ K.adjoint) =
      interiorModuleTensorOperator φ K := by
    rw [AdjointableMap.star_eq_adjoint, interiorModuleTensorOperator_adjoint,
      AdjointableMap.adjoint_adjoint]
  simpa only [star_mul, hstar, star_star] using h

end BC4lean.KKTheory.IsSignedModuleConnection
