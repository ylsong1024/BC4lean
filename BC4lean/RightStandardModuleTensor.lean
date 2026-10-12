import BC4lean.StandardModuleOperator
import BC4lean.ModuleTensorOperator
import BC4lean.HilbertModuleEquiv
import BC4lean.HilbertModuleCoefficientApproximateUnit

/-! # The actual right standard-module tensor unit

The evaluation `x ⊗ b ↦ xb` descends through the genuine balanced tensor
and its null radical, and extends isometrically to the completed interior
tensor. The actual coefficient approximate unit proves that evaluation is
onto E, also for nonunital B. No unit in B or extra essentiality hypothesis
is used. This is the tensor unitary; Kasparov product unit laws remain separate.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule Filter

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The bilinear coefficient-action evaluation. -/
def rightStandardModuleTensorEvaluationBilinear : E →ₗ[ℂ] Bᵐᵒᵖ →ₗ[ℂ] E where
  toFun x :=
    { toFun b := b • x
      map_add' b d := module_add_smul b d x
      map_smul' c b := module_complex_smul c b x }
  map_add' x y := by
    ext b
    exact module_smul_add b x y
  map_smul' c x := by
    ext b
    exact moduleCoefficient_smul_complex b c x

theorem rightStandardModuleTensorEvaluationBilinear_balance (b : B) (x : E) (y : Bᵐᵒᵖ) :
    rightStandardModuleTensorEvaluationBilinear (MulOpposite.op b • x) y =
      rightStandardModuleTensorEvaluationBilinear x (standardLeftMul b y) := by
  change y • (MulOpposite.op b • x) = (y * MulOpposite.op b) • x
  exact (module_mul_smul y (MulOpposite.op b) x).symm

/-- Evaluation on the constructed algebraic balancing quotient. -/
def rightStandardModuleTensorEvaluation :
    BalancedModuleTensor (E := E) (standardLeftMul (B := B)) →ₗ[ℂ] E :=
  moduleTensorLift standardLeftMul rightStandardModuleTensorEvaluationBilinear
    rightStandardModuleTensorEvaluationBilinear_balance

@[simp] theorem rightStandardModuleTensorEvaluation_mk (x : E) (b : Bᵐᵒᵖ) :
    rightStandardModuleTensorEvaluation (moduleTensorMk standardLeftMul x b) = b • x := rfl

/-- The entire tensor form is the pullback of the existing module inner product. -/
theorem moduleTensorInner_right_standard_eq
    (u v : BalancedModuleTensor (E := E) (standardLeftMul (B := B))) :
    moduleTensorInner standardLeftMul u v =
      ⟪rightStandardModuleTensorEvaluation u,
        rightStandardModuleTensorEvaluation v⟫_(Bᵐᵒᵖ) := by
  revert v
  refine moduleTensor_induction standardLeftMul u ?_ ?_ ?_
  · intro v
    simp
  · intro x b v
    refine moduleTensor_induction standardLeftMul v ?_ ?_ ?_
    · simp
    · intro y d
      change (d * ⟪x, y⟫_(Bᵐᵒᵖ)) * star b = ⟪b • x, d • y⟫_(Bᵐᵒᵖ)
      rw [inner_op_smul_right, inner_op_smul_left, mul_assoc]
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hw]

theorem moduleTensorInner_right_standard_self_eq_zero_iff
    (u : BalancedModuleTensor (E := E) (standardLeftMul (B := B))) :
    moduleTensorInner standardLeftMul u u = 0 ↔ rightStandardModuleTensorEvaluation u = 0 := by
  rw [moduleTensorInner_right_standard_eq]
  exact CStarModule.inner_self

variable [CompleteSpace E]

/-- Evaluation descends through precisely the actual tensor null radical. -/
def rightStandardPreModuleTensorEvaluationLinear :
    PreHilbertModuleTensor (E := E) (standardLeftMul (B := B)) →ₗ[ℂ] E :=
  (moduleTensorNull standardLeftMul).liftQ rightStandardModuleTensorEvaluation (by
    intro u hu
    exact (moduleTensorInner_right_standard_self_eq_zero_iff u).mp
      ((mem_moduleTensorNull_iff standardLeftMul u).mp hu))

@[simp] theorem rightStandardPreModuleTensorEvaluationLinear_mkQ
    (u : BalancedModuleTensor (E := E) (standardLeftMul (B := B))) :
    rightStandardPreModuleTensorEvaluationLinear ((moduleTensorNull standardLeftMul).mkQ u) =
      rightStandardModuleTensorEvaluation u := rfl

theorem rightStandardPreModuleTensorEvaluationLinear_inner
    (u v : PreHilbertModuleTensor (E := E) (standardLeftMul (B := B))) :
    ⟪rightStandardPreModuleTensorEvaluationLinear u,
      rightStandardPreModuleTensorEvaluationLinear v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (moduleTensorInner_right_standard_eq u v).symm

def rightStandardPreModuleTensorEvaluation :
    PreHilbertModuleTensor (E := E) (standardLeftMul (B := B)) →ₗᵢ[ℂ] E where
  toLinearMap := rightStandardPreModuleTensorEvaluationLinear
  norm_map' u := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
      rightStandardPreModuleTensorEvaluationLinear_inner,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]

@[simp] theorem rightStandardPreModuleTensorEvaluation_mk (x : E) (b : Bᵐᵒᵖ) :
    rightStandardPreModuleTensorEvaluation (preModuleTensorMk standardLeftMul x b) = b • x := rfl

/-- Isometric evaluation extends to the actual complete interior tensor. -/
def rightStandardInteriorModuleTensorEvaluationCLM :
    InteriorModuleTensor (E := E) (standardLeftMul (B := B)) →L[ℂ] E :=
  rightStandardPreModuleTensorEvaluation.toContinuousLinearMap.fromCompletion

@[simp] theorem rightStandardInteriorModuleTensorEvaluationCLM_coe
    (u : PreHilbertModuleTensor (E := E) (standardLeftMul (B := B))) :
    rightStandardInteriorModuleTensorEvaluationCLM (moduleTensorToCompletion standardLeftMul u) =
      rightStandardPreModuleTensorEvaluation u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem rightStandardInteriorModuleTensorEvaluationCLM_norm
    (u : InteriorModuleTensor (E := E) (standardLeftMul (B := B))) :
    ‖rightStandardInteriorModuleTensorEvaluationCLM u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    change ‖rightStandardInteriorModuleTensorEvaluationCLM
      (moduleTensorToCompletion standardLeftMul u)‖ =
      ‖moduleTensorToCompletion standardLeftMul u‖
    rw [rightStandardInteriorModuleTensorEvaluationCLM_coe,
      rightStandardPreModuleTensorEvaluation.norm_map,
      (moduleTensorToCompletion standardLeftMul).norm_map]

def rightStandardInteriorModuleTensorEvaluation :
    InteriorModuleTensor (E := E) (standardLeftMul (B := B)) →ₗᵢ[ℂ] E where
  toLinearMap := rightStandardInteriorModuleTensorEvaluationCLM.toLinearMap
  norm_map' := rightStandardInteriorModuleTensorEvaluationCLM_norm

@[simp] theorem rightStandardInteriorModuleTensorEvaluation_mk (x : E) (b : Bᵐᵒᵖ) :
    rightStandardInteriorModuleTensorEvaluation (interiorModuleTensorMk standardLeftMul x b) =
      b • x := rightStandardInteriorModuleTensorEvaluationCLM_coe _

theorem rightStandardInteriorModuleTensorEvaluation_inner
    (u v : InteriorModuleTensor (E := E) (standardLeftMul (B := B))) :
    ⟪rightStandardInteriorModuleTensorEvaluation u,
      rightStandardInteriorModuleTensorEvaluation v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    change ⟪rightStandardInteriorModuleTensorEvaluationCLM
      (moduleTensorToCompletion standardLeftMul u), rightStandardInteriorModuleTensorEvaluationCLM
      (moduleTensorToCompletion standardLeftMul v)⟫_(Bᵐᵒᵖ) =
      ⟪moduleTensorToCompletion standardLeftMul u,
        moduleTensorToCompletion standardLeftMul v⟫_(Bᵐᵒᵖ)
    rw [rightStandardInteriorModuleTensorEvaluationCLM_coe,
      rightStandardInteriorModuleTensorEvaluationCLM_coe]
    exact (rightStandardPreModuleTensorEvaluationLinear_inner u v).trans
      (hilbertModuleToCompletion_inner u v).symm

/-- The actual coefficient AU and the closed isometric range prove onto-ness. -/
theorem rightStandardInteriorModuleTensorEvaluation_surjective :
    Function.Surjective (rightStandardInteriorModuleTensorEvaluation (B := B) (E := E)) := by
  intro x
  have hclosed : IsClosed (Set.range
      (rightStandardInteriorModuleTensorEvaluation (B := B) (E := E))) :=
    rightStandardInteriorModuleTensorEvaluation.isometry.isUniformInducing.isComplete_range.isClosed
  apply hclosed.mem_of_tendsto
    (tendsto_coefficient_approximateUnit_smul (D := Bᵐᵒᵖ) x)
  exact Filter.Eventually.of_forall fun b =>
    ⟨interiorModuleTensorMk standardLeftMul x b,
      rightStandardInteriorModuleTensorEvaluation_mk x b⟩

/-- The genuine right Hilbert-module tensor unit, including nonunital B. -/
def rightStandardInteriorModuleTensorHilbertEquiv :
    HilbertModuleEquiv B (InteriorModuleTensor (E := E) (standardLeftMul (B := B))) E where
  linearIsometryEquiv :=
    LinearIsometryEquiv.ofSurjective rightStandardInteriorModuleTensorEvaluation
      rightStandardInteriorModuleTensorEvaluation_surjective
  inner_map := rightStandardInteriorModuleTensorEvaluation_inner

@[simp] theorem rightStandardInteriorModuleTensorHilbertEquiv_mk
    (x : E) (b : Bᵐᵒᵖ) :
    rightStandardInteriorModuleTensorHilbertEquiv
      (interiorModuleTensorMk standardLeftMul x b) = b • x :=
  rightStandardInteriorModuleTensorEvaluation_mk x b

/-- Evaluation intertwines the actual first-factor tensor operator with the
original coefficient-linear operator, on the entire completed tensor. -/
theorem rightStandardInteriorModuleTensorEvaluation_intertwine
    (T : AdjointableMap B E E)
    (u : InteriorModuleTensor (E := E) (standardLeftMul (B := B))) :
    rightStandardInteriorModuleTensorEvaluation
      (interiorModuleTensorOperator standardLeftMul T u) =
        T (rightStandardInteriorModuleTensorEvaluation u) := by
  have hpre (v : PreHilbertModuleTensor (E := E) (standardLeftMul (B := B))) :
      rightStandardPreModuleTensorEvaluation
        (preModuleTensorOperatorLinear standardLeftMul T v) =
          T (rightStandardPreModuleTensorEvaluation v) := by
    refine preModuleTensor_induction standardLeftMul v ?_ ?_ ?_
    · simp
    · intro x b
      simp only [preModuleTensorOperatorLinear_mk,
        rightStandardPreModuleTensorEvaluation_mk, T.map_op_smul]
    · intro v w hv hw
      simp only [map_add, hv, hw]
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    change rightStandardInteriorModuleTensorEvaluationCLM
      ((preModuleTensorOperator standardLeftMul T).completion
        (v : UniformSpace.Completion
          (PreHilbertModuleTensor (E := E) (standardLeftMul (B := B))))) =
          T (rightStandardInteriorModuleTensorEvaluationCLM
            (moduleTensorToCompletion standardLeftMul v))
    rw [AdjointableMap.completion_apply_coe]
    change rightStandardInteriorModuleTensorEvaluationCLM
      (moduleTensorToCompletion standardLeftMul
        (preModuleTensorOperatorLinear standardLeftMul T v)) =
          T (rightStandardInteriorModuleTensorEvaluationCLM
            (moduleTensorToCompletion standardLeftMul v))
    rw [rightStandardInteriorModuleTensorEvaluationCLM_coe,
      rightStandardInteriorModuleTensorEvaluationCLM_coe]
    exact hpre v

/-- The constructed right tensor unitary conjugates T ⊗ 1 to T. -/
theorem rightStandardInteriorModuleTensorHilbertEquiv_transport
    (T : AdjointableMap B E E) :
    rightStandardInteriorModuleTensorHilbertEquiv.transport
      (interiorModuleTensorOperator standardLeftMul T) = T := by
  ext x
  change rightStandardInteriorModuleTensorEvaluation
    (interiorModuleTensorOperator standardLeftMul T
      (rightStandardInteriorModuleTensorHilbertEquiv.symm x)) = T x
  rw [rightStandardInteriorModuleTensorEvaluation_intertwine]
  exact congrArg T (rightStandardInteriorModuleTensorHilbertEquiv.apply_symm_apply x)

end BC4lean.KKTheory
