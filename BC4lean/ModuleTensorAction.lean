import BC4lean.ModuleTensorInner

/-! # The actual right coefficient action on the balanced tensor

The right C-action is obtained by applying the second-module action in the
ordinary tensor product and descending through the balancing relations. The
coefficient-linearity of adjointable maps proves that this descent is valid.
The resulting action satisfies the required coefficient inner-product law.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped TensorProduct InnerProductSpace
open CStarModule

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [PartialOrder C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]

/-- The coefficient action commutes with the complex scalar action. -/
theorem moduleCoefficient_smul_complex (a : Cᵐᵒᵖ) (c : ℂ) (y : F) :
    a • (c • y) = c • (a • y) := by
  apply module_inner_ext_right (B := C)
  intro z
  simp only [inner_op_smul_right, inner_smul_right_complex, mul_smul_comm]

/-- A fixed right coefficient acts complex-linearly on the second module. -/
def moduleCoefficientActionLinear (a : Cᵐᵒᵖ) : F →ₗ[ℂ] F where
  toFun y := a • y
  map_add' := module_smul_add a
  map_smul' c y := moduleCoefficient_smul_complex a c y

/-- Apply a fixed right coefficient in the second factor of the ordinary tensor. -/
def moduleUnbalancedTensorAction (a : Cᵐᵒᵖ) : (E ⊗[ℂ] F) →ₗ[ℂ] E ⊗[ℂ] F :=
  TensorProduct.map LinearMap.id (moduleCoefficientActionLinear a)

omit [PartialOrder B] [CStarModule Bᵐᵒᵖ E] in
/-- The genuine balancing submodule is invariant under the second-factor action. -/
theorem moduleTensorRelations_action_invariant
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) :
    moduleTensorRelations (E := E) φ ≤
      (moduleTensorRelations (E := E) φ).comap (moduleUnbalancedTensorAction a) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨b, x, y⟩, rfl⟩
  change moduleUnbalancedTensorAction a
    ((MulOpposite.op b • x) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (φ b y)) ∈
      moduleTensorRelations (E := E) φ
  simp only [map_sub, moduleUnbalancedTensorAction, TensorProduct.map_tmul,
    LinearMap.id_apply, moduleCoefficientActionLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← AdjointableMap.map_op_smul]
  exact Submodule.subset_span ⟨(b, x, a • y), rfl⟩

/-- The fixed-coefficient action descended to the actual balanced quotient. -/
def moduleTensorActionLinear (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) :
    BalancedModuleTensor (E := E) φ →ₗ[ℂ] BalancedModuleTensor (E := E) φ :=
  (moduleTensorRelations (E := E) φ).mapQ (moduleTensorRelations (E := E) φ)
    (moduleUnbalancedTensorAction a) (moduleTensorRelations_action_invariant φ a)

omit [PartialOrder B] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem moduleTensorActionLinear_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) (x : E) (y : F) :
    moduleTensorActionLinear φ a (moduleTensorMk φ x y) = moduleTensorMk φ x (a • y) := rfl

/-- The right C-action on the actual algebraic balanced tensor quotient. -/
instance moduleTensorSMul (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    SMul Cᵐᵒᵖ (BalancedModuleTensor (E := E) φ) where
  smul a u := moduleTensorActionLinear φ a u

omit [PartialOrder B] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem moduleTensor_smul_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) (x : E) (y : F) :
    a • moduleTensorMk φ x y = moduleTensorMk φ x (a • y) := rfl

/-- The descended coefficient form satisfies the actual second-variable action law. -/
theorem moduleTensorInner_op_smul_right
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ)
    (u v : BalancedModuleTensor (E := E) φ) :
    moduleTensorInner φ u (a • v) = a * moduleTensorInner φ u v := by
  revert v
  refine moduleTensor_induction φ u ?_ ?_ ?_
  · intro v
    simp
  · intro x y v
    refine moduleTensor_induction φ v ?_ ?_ ?_
    · have hzero : a • (0 : BalancedModuleTensor (E := E) φ) = 0 :=
        (moduleTensorActionLinear φ a).map_zero
      rw [hzero, map_zero, mul_zero]
    · intro x' y'
      simp only [moduleTensor_smul_mk, moduleTensorInner_mk_mk, moduleTensorPureInner,
        AdjointableMap.map_op_smul, inner_op_smul_right]
    · intro v w hv hw
      have hadd : a • (v + w) = a • v + a • w :=
        (moduleTensorActionLinear φ a).map_add v w
      rw [hadd]
      simp only [map_add, hv, hw, mul_add]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, hu, hw, mul_add]

/-- The first-variable action law follows from genuine Hermitian symmetry. -/
theorem moduleTensorInner_op_smul_left
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ)
    (u v : BalancedModuleTensor (E := E) φ) :
    moduleTensorInner φ (a • u) v = moduleTensorInner φ u v * star a := by
  apply star_injective
  simp only [moduleTensorInner_star, moduleTensorInner_op_smul_right,
    star_mul, star_star]

end BC4lean.KKTheory
