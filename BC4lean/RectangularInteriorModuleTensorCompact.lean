import BC4lean.RectangularInteriorModuleTensorOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Compact rectangular maps under an actual compact coefficient extension

This extends the existing
actual rectangular tensor functor's rank-one formula to the norm-closed
rank-one span. It does not assert compactness without a compact left action.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C E E' F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]

/-- Actual compact rectangular maps remain compact after tensoring by a
representation whose original coefficients act compactly. -/
theorem IsModuleCompact.rectangularInteriorModuleTensor
    {T : AdjointableMap B E E'} (hT : IsModuleCompact T)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (hφ : ∀ b, IsModuleCompact (φ b)) :
    IsModuleCompact (RectangularInteriorModuleTensorOperator.tensor φ T) := by
  let L := RectangularInteriorModuleTensorOperator.tensorCLM (E := E) (E' := E') φ
  let S := (moduleCompact C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E') φ)).comap L.toLinearMap
  have hS : IsClosed (S : Set (AdjointableMap B E E')) :=
    moduleCompact_isClosed.preimage L.continuous
  have hθ : ∀ (x : E') (y : E), moduleRankOne (B := B) x y ∈ S := by
    intro x y
    change IsModuleCompact (RectangularInteriorModuleTensorOperator.tensor φ
      (moduleRankOne (B := B) x y))
    rw [RectangularInteriorModuleTensorOperator.tensor_rankOne]
    exact (moduleCreationMap_isModuleCompact_of_compact_left_action φ hφ x).comp_right _
  exact moduleCompact_le_of_isClosed S hS hθ hT

end BC4lean.KKTheory
