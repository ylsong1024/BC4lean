import BC4lean.PreHilbertModuleTensor
import BC4lean.ModuleTensorOperator
import BC4lean.HilbertModuleCompletion
import BC4lean.CompactModuleOperatorCriterion
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Creation maps into the actual completed interior tensor

Creation is first constructed on the proved separated pre-Hilbert tensor. Its
adjoint formula descends through the actual balance and null relations; the
Hilbert-module Cauchy–Schwarz bound makes it continuous. It then extends to
the genuine norm completion. Compactness is proved only under its exact
criterion, not built into creation or assumed without a left-action condition.
-/

noncomputable section
namespace BC4lean.KKTheory

open UniformSpace
open scoped InnerProductSpace
open CStarModule

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The expected adjoint formula as an actual balanced complex bilinear map. -/
def moduleCreationAdjointPure (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    E →ₗ[ℂ] F →ₗ[ℂ] F where
  toFun x := (φ (MulOpposite.unop ⟪ξ, x⟫_(Bᵐᵒᵖ))).toCLM.toLinearMap
  map_add' x y := by
    ext z
    change φ (MulOpposite.unop ⟪ξ, x + y⟫_(Bᵐᵒᵖ)) z =
      φ (MulOpposite.unop ⟪ξ, x⟫_(Bᵐᵒᵖ)) z +
        φ (MulOpposite.unop ⟪ξ, y⟫_(Bᵐᵒᵖ)) z
    rw [CStarModule.inner_add_right, MulOpposite.unop_add, map_add]
    rfl
  map_smul' c x := by
    ext z
    change φ (MulOpposite.unop ⟪ξ, c • x⟫_(Bᵐᵒᵖ)) z =
      c • φ (MulOpposite.unop ⟪ξ, x⟫_(Bᵐᵒᵖ)) z
    rw [inner_smul_right_complex, MulOpposite.unop_smul, map_smul]
    rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- The adjoint formula respects the defining B-balance relation. -/
theorem moduleCreationAdjointPure_balance
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) (b : B) (x : E) (y : F) :
    moduleCreationAdjointPure φ ξ (MulOpposite.op b • x) y =
      moduleCreationAdjointPure φ ξ x (φ b y) := by
  change φ (MulOpposite.unop ⟪ξ, MulOpposite.op b • x⟫_(Bᵐᵒᵖ)) y =
    φ (MulOpposite.unop ⟪ξ, x⟫_(Bᵐᵒᵖ)) (φ b y)
  simp only [inner_op_smul_right, MulOpposite.unop_mul, MulOpposite.unop_op,
    map_mul, AdjointableMap.mul_apply]

/-- The adjoint formula genuinely descends to the balanced tensor. -/
def moduleCreationAdjointBalanced (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    BalancedModuleTensor (E := E) φ →ₗ[ℂ] F :=
  moduleTensorLift φ (moduleCreationAdjointPure φ ξ) (moduleCreationAdjointPure_balance φ ξ)

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem moduleCreationAdjointBalanced_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ x : E) (y : F) :
    moduleCreationAdjointBalanced φ ξ (moduleTensorMk φ x y) =
      φ (MulOpposite.unop ⟪ξ, x⟫_(Bᵐᵒᵖ)) y := rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- The true adjoint identity holds on every balanced tensor, not just pure tensors. -/
theorem moduleCreationAdjointBalanced_identity
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) (z : F)
    (u : BalancedModuleTensor (E := E) φ) :
    moduleTensorInner φ (moduleTensorMk φ ξ z) u =
      ⟪z, moduleCreationAdjointBalanced φ ξ u⟫_(Cᵐᵒᵖ) := by
  induction u using moduleTensor_induction φ with
  | h0 => simp
  | hθ x y => rfl
  | hadd u v hu hv =>
    simp only [map_add, CStarModule.inner_add_right, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- The formula annihilates the actual null space by coefficient-inner separation. -/
theorem moduleCreationAdjointBalanced_null
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E)
    {u : BalancedModuleTensor (E := E) φ} (hu : u ∈ moduleTensorNull φ) :
    moduleCreationAdjointBalanced φ ξ u = 0 := by
  apply module_inner_ext_right (B := C)
  intro z
  rw [CStarModule.inner_zero_right, ← moduleCreationAdjointBalanced_identity]
  exact moduleTensorInner_null_right φ _ hu

/-- The adjoint formula on the actual separated pre-Hilbert tensor. -/
def moduleCreationAdjointPre (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] F :=
  (moduleTensorNull φ).liftQ (moduleCreationAdjointBalanced φ ξ) (by
    intro u hu
    exact moduleCreationAdjointBalanced_null φ ξ hu)

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem moduleCreationAdjointPre_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ x : E) (y : F) :
    moduleCreationAdjointPre φ ξ (preModuleTensorMk φ x y) =
      φ (MulOpposite.unop ⟪ξ, x⟫_(Bᵐᵒᵖ)) y := rfl

/-- The separated tensor retains the true adjoint identity. -/
theorem moduleCreationAdjointPre_identity
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) (z : F)
    (u : PreHilbertModuleTensor (E := E) φ) :
    ⟪preModuleTensorMk φ ξ z, u⟫_(Cᵐᵒᵖ) =
      ⟪z, moduleCreationAdjointPre φ ξ u⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u => exact moduleCreationAdjointBalanced_identity φ ξ z u

/-- The adjoint formula is bounded in the genuine induced tensor norm. -/
theorem moduleCreationAdjointPre_norm_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E)
    (u : PreHilbertModuleTensor (E := E) φ) :
    ‖moduleCreationAdjointPre φ ξ u‖ ≤ ‖ξ‖ * ‖u‖ := by
  rw [CStarModule.norm_eq_csSup (A := Cᵐᵒᵖ) (moduleCreationAdjointPre φ ξ u)]
  apply csSup_le
  · exact ⟨0, 0, by simp, by simp⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [← moduleCreationAdjointPre_identity]
    calc
      ‖⟪preModuleTensorMk φ ξ z, u⟫_(Cᵐᵒᵖ)‖ ≤ ‖preModuleTensorMk φ ξ z‖ * ‖u‖ :=
        CStarModule.norm_inner_le _
      _ ≤ (‖ξ‖ * ‖z‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (preModuleTensorMk_norm_le φ ξ z) (norm_nonneg _)
      _ = (‖ξ‖ * ‖u‖) * ‖z‖ := by ring
      _ ≤ ‖ξ‖ * ‖u‖ :=
        mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hz

/-- The actual bounded creation map into the separated pre-Hilbert tensor. -/
def moduleCreationPreCLM (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    F →L[ℂ] PreHilbertModuleTensor (E := E) φ :=
  (preModuleTensorMk φ ξ).mkContinuous ‖ξ‖ (preModuleTensorMk_norm_le φ ξ)

/-- The bounded pre-Hilbert adjoint formula. -/
def moduleCreationAdjointPreCLM (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    PreHilbertModuleTensor (E := E) φ →L[ℂ] F :=
  (moduleCreationAdjointPre φ ξ).mkContinuous ‖ξ‖ (moduleCreationAdjointPre_norm_le φ ξ)

/-- The genuine creation map into the completed interior tensor, with its actual adjoint. -/
def moduleCreationMap (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    AdjointableMap C F (Completion (PreHilbertModuleTensor (E := E) φ)) where
  toCLM := Completion.toComplL.comp (moduleCreationPreCLM φ ξ)
  adjointCLM := (moduleCreationAdjointPreCLM φ ξ).fromCompletion
  adjoint_identity z u := by
    refine Completion.induction_on u ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk continuous_id))
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk (moduleCreationAdjointPreCLM φ ξ).fromCompletion.continuous))
    · intro u
      change ⟪(preModuleTensorMk φ ξ z : Completion (PreHilbertModuleTensor (E := E) φ)),
        (u : Completion (PreHilbertModuleTensor (E := E) φ))⟫_(Cᵐᵒᵖ) =
        ⟪z, (moduleCreationAdjointPreCLM φ ξ).fromCompletion
          (u : Completion (PreHilbertModuleTensor (E := E) φ))⟫_(Cᵐᵒᵖ)
      rw [completionInner_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      exact moduleCreationAdjointPre_identity φ ξ z u

@[simp] theorem moduleCreationMap_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) (y : F) :
    moduleCreationMap φ ξ y =
      (preModuleTensorMk φ ξ y : Completion (PreHilbertModuleTensor (E := E) φ)) := rfl

@[simp] theorem moduleCreationMap_adjoint_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ x : E) (y : F) :
    (moduleCreationMap φ ξ).adjoint
        (preModuleTensorMk φ x y : Completion (PreHilbertModuleTensor (E := E) φ)) =
      φ (MulOpposite.unop ⟪ξ, x⟫_(Bᵐᵒᵖ)) y := by
  exact ContinuousLinearMap.fromCompletion_apply_coe (moduleCreationAdjointPreCLM φ ξ)
    (preModuleTensorMk φ x y)

/-- The creation norm bound is proved using the actual completion inclusion. -/
theorem moduleCreationMap_norm_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) : ‖moduleCreationMap φ ξ‖ ≤ ‖ξ‖ := by
  apply (moduleCreationMap φ ξ).toCLM.opNorm_le_bound (norm_nonneg _)
  intro y
  rw [moduleCreationMap_apply, Completion.norm_coe]
  exact preModuleTensorMk_norm_le φ ξ y

/-- Creation depends complex-linearly on the first module vector. -/
theorem moduleCreationMap_add
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ ζ : E) :
    moduleCreationMap φ (ξ + ζ) = moduleCreationMap φ ξ + moduleCreationMap φ ζ := by
  apply AdjointableMap.ext
  intro y
  simp only [AdjointableMap.coe_add_apply, moduleCreationMap_apply, map_add,
    LinearMap.add_apply, Completion.coe_add]

@[simp] theorem moduleCreationMap_smul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (c : ℂ) (ξ : E) :
    moduleCreationMap φ (c • ξ) = c • moduleCreationMap φ ξ := by
  apply AdjointableMap.ext
  intro y
  simp only [AdjointableMap.coe_smul_apply, moduleCreationMap_apply, map_smul,
    LinearMap.smul_apply, Completion.coe_smul]

@[simp] theorem moduleCreationMap_neg
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    moduleCreationMap φ (-ξ) = -moduleCreationMap φ ξ := by
  rw [← neg_one_smul ℂ ξ, moduleCreationMap_smul, neg_one_smul]

/-- The actual creation map is a bounded complex-linear function of its vector. -/
def moduleCreationLinearMap (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    E →ₗ[ℂ] AdjointableMap C F (InteriorModuleTensor (E := E) φ) where
  toFun := moduleCreationMap φ
  map_add' := moduleCreationMap_add φ
  map_smul' := moduleCreationMap_smul φ

@[simp] theorem moduleCreationMap_zero
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) : moduleCreationMap (E := E) φ 0 = 0 :=
  (moduleCreationLinearMap φ).map_zero

def moduleCreationContinuousLinearMap (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    E →L[ℂ] AdjointableMap C F (InteriorModuleTensor (E := E) φ) :=
  (moduleCreationLinearMap φ).mkContinuous 1 (fun ξ => by
    change ‖moduleCreationMap φ ξ‖ ≤ 1 * ‖ξ‖
    simpa only [one_mul] using moduleCreationMap_norm_le φ ξ)

@[simp] theorem moduleCreationContinuousLinearMap_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    moduleCreationContinuousLinearMap φ ξ = moduleCreationMap φ ξ := rfl

/-- The actual first-factor tensor operator sends creation by ξ to creation by Tξ. -/
theorem moduleCreationMap_tensorOperator
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) (ξ : E) :
    (interiorModuleTensorOperator φ T).comp (moduleCreationMap φ ξ) =
      moduleCreationMap φ (T ξ) := by
  apply AdjointableMap.ext
  intro y
  change interiorModuleTensorOperator φ T (interiorModuleTensorMk φ ξ y) =
    interiorModuleTensorMk φ (T ξ) y
  exact interiorModuleTensorOperator_mk φ T ξ y

/-- Actual coefficient balancing expresses creation by ξb as θξ composed
with the left representation of b. -/
theorem moduleCreationMap_balance
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (ξ : E) :
    moduleCreationMap φ (MulOpposite.op b • ξ) = (moduleCreationMap φ ξ).comp (φ b) := by
  apply AdjointableMap.ext
  intro y
  change (preModuleTensorMk φ (MulOpposite.op b • ξ) y :
      Completion (PreHilbertModuleTensor (E := E) φ)) =
    (preModuleTensorMk φ ξ (φ b y) : Completion (PreHilbertModuleTensor (E := E) φ))
  exact congrArg (fun u : PreHilbertModuleTensor (E := E) φ =>
    (u : Completion (PreHilbertModuleTensor (E := E) φ))) (preModuleTensorMk_balance φ b ξ y)

/-- The corrected general creation composition identity on the actual interior tensor. -/
theorem moduleCreationMap_adjoint_comp
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ ζ : E) :
    (moduleCreationMap φ ξ).adjoint.comp (moduleCreationMap φ ζ) =
      φ (MulOpposite.unop ⟪ξ, ζ⟫_(Bᵐᵒᵖ)) := by
  ext y
  simp only [AdjointableMap.comp_apply, moduleCreationMap_apply, moduleCreationMap_adjoint_mk]

/-- Exact compactness criterion; creation need not be compact for a general left action. -/
theorem moduleCreationMap_isModuleCompact_iff
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ξ : E) :
    IsModuleCompact (moduleCreationMap φ ξ) ↔
      IsModuleCompact (φ (MulOpposite.unop ⟪ξ, ξ⟫_(Bᵐᵒᵖ))) := by
  rw [isModuleCompact_iff_adjoint_comp_self, moduleCreationMap_adjoint_comp]

/-- A compact left action supplies compact creation maps, with a proved hypothesis. -/
theorem moduleCreationMap_isModuleCompact_of_compact_left_action
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (hφ : ∀ b, IsModuleCompact (φ b)) (ξ : E) :
    IsModuleCompact (moduleCreationMap φ ξ) :=
  (moduleCreationMap_isModuleCompact_iff φ ξ).mpr (hφ _)

end BC4lean.KKTheory
