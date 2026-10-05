import BC4lean.ModuleTensorPureInner

/-! # The coefficient-valued form on the balanced algebraic tensor

The elementary interior-tensor pairing is extended by sesquilinearity to the
genuine complex tensor product and descended through both variables of the
coefficient-balance quotient.  The resulting form is Hermitian and positive on
elementary tensors.  General positivity, the null-space quotient, its induced
norm, and completion remain separate constructions.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped TensorProduct

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [PartialOrder C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]

/-- Bundle the last two linear variables of the elementary pairing. -/
def moduleTensorPureInnerLinear (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (x : E) (y : F) : E →ₗ[ℂ] F →ₗ[ℂ] Cᵐᵒᵖ where
  toFun x' :=
    { toFun := moduleTensorPureInner φ x y x'
      map_add' := fun y' v' => moduleTensorPureInner_add_fourth φ x x' y y' v'
      map_smul' := fun c y' => moduleTensorPureInner_smul_fourth φ c x x' y y' }
  map_add' x' u' := by
    ext y'
    exact moduleTensorPureInner_add_third φ x x' u' y y'
  map_smul' c x' := by
    ext y'
    exact moduleTensorPureInner_smul_third φ c x x' y y'

/-- Bundle the two conjugate-linear variables after lifting the linear
variables to the ordinary complex tensor product. -/
def moduleTensorPureInnerSesquilinear (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    E →ₗ⋆[ℂ] F →ₗ⋆[ℂ] ((E ⊗[ℂ] F) →ₗ[ℂ] Cᵐᵒᵖ) where
  toFun x :=
    { toFun := fun y => TensorProduct.lift (moduleTensorPureInnerLinear φ x y)
      map_add' := fun y v => by
        apply TensorProduct.ext'
        intro x' y'
        exact moduleTensorPureInner_add_second φ x x' y v y'
      map_smul' := fun c y => by
        apply TensorProduct.ext'
        intro x' y'
        exact moduleTensorPureInner_smul_second φ c x x' y y' }
  map_add' x u := by
    apply LinearMap.ext
    intro y
    apply TensorProduct.ext'
    intro x' y'
    exact moduleTensorPureInner_add_first φ x u x' y y'
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply TensorProduct.ext'
    intro x' y'
    exact moduleTensorPureInner_smul_first φ c x x' y y'

/-- The sesquilinear C-valued form on the unbalanced complex tensor product. -/
def moduleUnbalancedTensorInner (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    (E ⊗[ℂ] F) →ₗ⋆[ℂ] (E ⊗[ℂ] F) →ₗ[ℂ] Cᵐᵒᵖ :=
  TensorProduct.lift (moduleTensorPureInnerSesquilinear φ)

@[simp] theorem moduleUnbalancedTensorInner_tmul_tmul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y y' : F) :
    moduleUnbalancedTensorInner φ (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') =
      moduleTensorPureInner φ x y x' y' := rfl

/-- Hermitian symmetry holds for arbitrary unbalanced tensors. -/
theorem moduleUnbalancedTensorInner_star
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (u v : E ⊗[ℂ] F) :
    star (moduleUnbalancedTensorInner φ u v) = moduleUnbalancedTensorInner φ v u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' => exact moduleTensorPureInner_star φ x x' y y'
    | add v w hv hw =>
      simp only [map_add, LinearMap.add_apply, star_add, hv, hw]
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, star_add, hu, hw]

/-- The unbalanced form respects each relation in the second variable. -/
theorem moduleUnbalancedTensorInner_balance_right
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (u : E ⊗[ℂ] F) (x : E) (y : F) :
    moduleUnbalancedTensorInner φ u ((MulOpposite.op b • x) ⊗ₜ[ℂ] y) =
      moduleUnbalancedTensorInner φ u (x ⊗ₜ[ℂ] (φ b y)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x' y' => exact moduleTensorPureInner_balance_right φ b x' x y' y
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

/-- The unbalanced form respects each relation in the first variable. -/
theorem moduleUnbalancedTensorInner_balance_left
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (x : E) (y : F) (v : E ⊗[ℂ] F) :
    moduleUnbalancedTensorInner φ ((MulOpposite.op b • x) ⊗ₜ[ℂ] y) v =
      moduleUnbalancedTensorInner φ (x ⊗ₜ[ℂ] (φ b y)) v := by
  apply star_injective
  rw [moduleUnbalancedTensorInner_star, moduleUnbalancedTensorInner_star]
  exact moduleUnbalancedTensorInner_balance_right φ b v x y

/-- The full relation submodule is annihilated in the second variable. -/
theorem moduleTensorRelations_le_ker_inner_right
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (u : E ⊗[ℂ] F) :
    moduleTensorRelations (E := E) φ ≤ LinearMap.ker (moduleUnbalancedTensorInner φ u) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨b, x, y⟩, rfl⟩
  change moduleUnbalancedTensorInner φ u
    ((MulOpposite.op b • x) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (φ b y)) = 0
  rw [map_sub, moduleUnbalancedTensorInner_balance_right, sub_self]

/-- Descend the form through the second variable, retaining conjugate
linearity in the first unbalanced variable. -/
def moduleTensorInnerRightLift (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    (E ⊗[ℂ] F) →ₗ⋆[ℂ] BalancedModuleTensor (E := E) φ →ₗ[ℂ] Cᵐᵒᵖ where
  toFun u := (moduleTensorRelations (E := E) φ).liftQ (moduleUnbalancedTensorInner φ u)
    (moduleTensorRelations_le_ker_inner_right φ u)
  map_add' u v := by
    apply moduleTensor_ext φ
    intro x y
    change moduleUnbalancedTensorInner φ (u + v) (x ⊗ₜ[ℂ] y) =
      moduleUnbalancedTensorInner φ u (x ⊗ₜ[ℂ] y) +
        moduleUnbalancedTensorInner φ v (x ⊗ₜ[ℂ] y)
    rw [map_add, LinearMap.add_apply]
  map_smul' c u := by
    apply moduleTensor_ext φ
    intro x y
    change moduleUnbalancedTensorInner φ (c • u) (x ⊗ₜ[ℂ] y) =
      star c • moduleUnbalancedTensorInner φ u (x ⊗ₜ[ℂ] y)
    rw [map_smulₛₗ, LinearMap.smul_apply]
    rfl

/-- The full relation submodule is also annihilated in the first variable. -/
theorem moduleTensorRelations_le_ker_inner_left
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    moduleTensorRelations (E := E) φ ≤ LinearMap.ker (moduleTensorInnerRightLift φ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨b, x, y⟩, rfl⟩
  change moduleTensorInnerRightLift φ
    ((MulOpposite.op b • x) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (φ b y)) = 0
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply moduleTensor_ext φ
  intro x' y'
  change moduleUnbalancedTensorInner φ ((MulOpposite.op b • x) ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') =
    moduleUnbalancedTensorInner φ (x ⊗ₜ[ℂ] (φ b y)) (x' ⊗ₜ[ℂ] y')
  exact moduleUnbalancedTensorInner_balance_left φ b x y (x' ⊗ₜ[ℂ] y')

/-- The genuine coefficient-valued sesquilinear form on the constructed
balanced algebraic tensor quotient. -/
def moduleTensorInner (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    BalancedModuleTensor (E := E) φ →ₗ⋆[ℂ]
      BalancedModuleTensor (E := E) φ →ₗ[ℂ] Cᵐᵒᵖ :=
  (moduleTensorRelations (E := E) φ).liftQ (moduleTensorInnerRightLift φ)
    (moduleTensorRelations_le_ker_inner_left φ)

@[simp] theorem moduleTensorInner_mk_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y y' : F) :
    moduleTensorInner φ (moduleTensorMk φ x y) (moduleTensorMk φ x' y') =
      moduleTensorPureInner φ x y x' y' := rfl

/-- The form descended to the balance quotient is Hermitian. -/
theorem moduleTensorInner_star (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u v : BalancedModuleTensor (E := E) φ) :
    star (moduleTensorInner φ u v) = moduleTensorInner φ v u := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact moduleUnbalancedTensorInner_star φ u v

/-- Elementary-vector positivity in the actual balanced quotient. -/
theorem moduleTensorInner_mk_self_nonneg [StarOrderedRing B]
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (y : F) :
    0 ≤ moduleTensorInner φ (moduleTensorMk φ x y) (moduleTensorMk φ x y) :=
  moduleTensorPureInner_self_nonneg φ x y

end BC4lean.KKTheory
