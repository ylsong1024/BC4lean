import BC4lean.ModuleCreationMap
import BC4lean.InteriorModuleTensorIsometry

/-! # Compact first-factor operators for a compact left action

The actual tensor of a rank-one module operator is the composition of its
two actual creation maps. If the second module's left action is compact,
the proved creation compactness criterion makes this composition compact.
The operator norm bound then extends compactness to the closed rank-one
span by the closed preimage of the genuine compact-operator submodule.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- Tensoring an actual rank-one operator gives the composition of actual
creation maps, on the constructed completion. -/
theorem interiorModuleTensorOperator_rankOne
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x y : E) :
    interiorModuleTensorOperator φ (moduleRankOne (B := B) x y) =
      (moduleCreationMap φ x).comp (moduleCreationMap φ y).adjoint := by
  have heq : (interiorModuleTensorOperator φ (moduleRankOne (B := B) x y)).toCLM =
      ((moduleCreationMap φ x).comp (moduleCreationMap φ y).adjoint).toCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro z w
    change interiorModuleTensorOperator φ (moduleRankOne (B := B) x y)
      (interiorModuleTensorMk φ z w) =
        (moduleCreationMap φ x) ((moduleCreationMap φ y).adjoint
          (interiorModuleTensorMk φ z w))
    rw [interiorModuleTensorOperator_mk]
    change interiorModuleTensorMk φ (moduleRankOne (B := B) x y z) w =
      interiorModuleTensorMk φ x ((moduleCreationMap φ y).adjoint
        (preModuleTensorMk φ z w : InteriorModuleTensor (E := E) φ))
    rw [moduleCreationMap_adjoint_mk, moduleRankOne_apply]
    change interiorModuleTensorMk φ
      (MulOpposite.op (MulOpposite.unop ⟪y, z⟫_(Bᵐᵒᵖ)) • x) w = _
    rw [interiorModuleTensorMk_balance]
  exact AdjointableMap.toCLM_injective heq

/-- The first-factor operator map is actually continuous in operator norm. -/
def interiorModuleTensorOperatorCLM (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    AdjointableMap B E E →L[ℂ]
      AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) :=
  LinearMap.mkContinuous
    { toFun := interiorModuleTensorOperator φ
      map_add' := map_add (interiorModuleTensorOperatorHom φ)
      map_smul' := map_smul (interiorModuleTensorOperatorHom φ) }
    1 (fun T => by
      change ‖interiorModuleTensorOperator φ T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using interiorModuleTensorOperator_norm_le φ T)

@[simp] theorem interiorModuleTensorOperatorCLM_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) :
    interiorModuleTensorOperatorCLM φ T = interiorModuleTensorOperator φ T := rfl

/-- With a compact second left action, the actual induced first-factor
operator preserves compactness. -/
theorem IsModuleCompact.interiorModuleTensorOperator
    {T : AdjointableMap B E E} (hT : IsModuleCompact T)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (hφ : ∀ b, IsModuleCompact (φ b)) :
    IsModuleCompact (interiorModuleTensorOperator φ T) := by
  let L := interiorModuleTensorOperatorCLM (E := E) φ
  let S := (moduleCompact C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) φ)).comap L.toLinearMap
  have hS : IsClosed (S : Set (AdjointableMap B E E)) :=
    moduleCompact_isClosed.preimage L.continuous
  have hθ : ∀ x y : E, moduleRankOne (B := B) x y ∈ S := by
    intro x y
    change IsModuleCompact (BC4lean.KKTheory.interiorModuleTensorOperator φ
      (moduleRankOne (B := B) x y))
    rw [interiorModuleTensorOperator_rankOne]
    exact (moduleCreationMap_isModuleCompact_of_compact_left_action φ hφ x).comp_right _
  exact moduleCompact_le_of_isClosed S hS hθ hT

end BC4lean.KKTheory
