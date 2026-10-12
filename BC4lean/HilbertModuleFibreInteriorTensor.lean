import BC4lean.IntervalModuleFibreNorm
import BC4lean.StandardModuleOperator
import BC4lean.InteriorModuleTensor
import BC4lean.HilbertModuleEquiv
import BC4lean.HilbertModuleCoefficientApproximateUnit

/-! # The intrinsic fibre is the actual evaluation interior tensor

For an arbitrary complete Hilbert `C(X,B)`-module and compact Hausdorff `X`,
the evaluated-inner-product fibre is unitarily equivalent to its actual
interior tensor with the standard module `B_B`, with left action
`a ↦ L_{a(t)}`. The elementary map sends `x ⊗ b` to `x(t)b`, where `x(t)`
is the intrinsic canonical fibre class, rather than a section-model value.

The full pairing identity proves descent through the actual tensor radical
and gives an isometry on its separated quotient. Extension to the genuine
completion preserves the coefficient inner product. The proved intrinsic
fibre-map surjectivity, the actual coefficient approximate unit, and the
closed isometric range prove onto-ness also for nonunital `B`. No additional
essentiality, section-model identification, or unitary conclusion is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule Filter

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M]

namespace HilbertModuleFibreInteriorTensor

/-- The actual left action used in the textbook evaluation interior tensor. -/
def leftRepresentation (t : X) :
    C(X, B) →⋆ₙₐ[ℂ] AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ where
  toFun a := standardLeftMul (a t)
  map_zero' := map_zero (standardLeftMul (B := B))
  map_add' a b := map_add standardLeftMul (a t) (b t)
  map_mul' a b := map_mul standardLeftMul (a t) (b t)
  map_smul' c a := map_smul standardLeftMul c (a t)
  map_star' a := map_star standardLeftMul (a t)

omit [CompactSpace X] in
@[simp] theorem leftRepresentation_apply (t : X) (a : C(X, B)) (b : Bᵐᵒᵖ) :
    leftRepresentation t a b = MulOpposite.op (a t * MulOpposite.unop b) := rfl

/-- Fibre evaluation followed by the actual right coefficient action. -/
def evaluationBilinear (t : X) : M →ₗ[ℂ] Bᵐᵒᵖ →ₗ[ℂ] HilbertModuleFibre B M t where
  toFun x :=
    { toFun b := b • hilbertModuleFibreMk (B := B) t x
      map_add' b d := module_add_smul b d (hilbertModuleFibreMk (B := B) t x)
      map_smul' c b := module_complex_smul c b (hilbertModuleFibreMk (B := B) t x) }
  map_add' x y := by
    ext b
    change b • hilbertModuleFibreMk (B := B) t (x + y) =
      b • hilbertModuleFibreMk (B := B) t x + b • hilbertModuleFibreMk (B := B) t y
    rw [map_add]
    exact module_smul_add b _ _
  map_smul' c x := by
    ext b
    change b • hilbertModuleFibreMk (B := B) t (c • x) =
      c • (b • hilbertModuleFibreMk (B := B) t x)
    rw [map_smul]
    exact moduleCoefficient_smul_complex b c _

/-- Variable coefficients descend to their value at `t`, which proves the
actual balancing relation for evaluation. -/
theorem evaluationBilinear_balance (t : X) (a : C(X, B)) (x : M) (b : Bᵐᵒᵖ) :
    evaluationBilinear t (MulOpposite.op a • x) b =
      evaluationBilinear t x (leftRepresentation t a b) := by
  change b • hilbertModuleFibreMk (B := B) t (MulOpposite.op a • x) =
    leftRepresentation t a b • hilbertModuleFibreMk (B := B) t x
  rw [hilbertModuleFibreMk_op_smul]
  change b • (MulOpposite.op (a t) • hilbertModuleFibreMk (B := B) t x) =
    (b * MulOpposite.op (a t)) • hilbertModuleFibreMk (B := B) t x
  exact (module_mul_smul b (MulOpposite.op (a t)) _).symm

/-- Evaluation on the genuine coefficient-balancing quotient. -/
def balancedEvaluation (t : X) :
    BalancedModuleTensor (E := M) (leftRepresentation (B := B) t) →ₗ[ℂ]
      HilbertModuleFibre B M t :=
  moduleTensorLift (leftRepresentation t) (evaluationBilinear t)
    (evaluationBilinear_balance t)

@[simp] theorem balancedEvaluation_mk (t : X) (x : M) (b : Bᵐᵒᵖ) :
    balancedEvaluation t (moduleTensorMk (leftRepresentation t) x b) =
      b • hilbertModuleFibreMk (B := B) t x := rfl

/-- The entire constructed tensor pairing is the pullback of the intrinsic
fibre pairing, proved first on elementary tensors and then by additivity. -/
theorem balancedEvaluation_inner (t : X)
    (u v : BalancedModuleTensor (E := M) (leftRepresentation (B := B) t)) :
    moduleTensorInner (leftRepresentation t) u v =
      ⟪balancedEvaluation t u, balancedEvaluation t v⟫_(Bᵐᵒᵖ) := by
  revert v
  refine moduleTensor_induction (leftRepresentation t) u ?_ ?_ ?_
  · intro v
    simp only [map_zero, LinearMap.zero_apply,
      CStarModule.inner_zero_left (A := Bᵐᵒᵖ) (E := HilbertModuleFibre B M t)]
  · intro x b v
    refine moduleTensor_induction (leftRepresentation t) v ?_ ?_ ?_
    · simp only [map_zero,
        CStarModule.inner_zero_right (A := Bᵐᵒᵖ) (E := HilbertModuleFibre B M t)]
    · intro y d
      change (d * MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t)) * star b =
        ⟪b • hilbertModuleFibreMk (B := B) t x,
          d • hilbertModuleFibreMk (B := B) t y⟫_(Bᵐᵒᵖ)
      rw [inner_op_smul_right (A := Bᵐᵒᵖ) (E := HilbertModuleFibre B M t),
        inner_op_smul_left (A := Bᵐᵒᵖ) (E := HilbertModuleFibre B M t),
        hilbertModuleFibre_inner_mk, mul_assoc]
    · intro v w hv hw
      simp only [map_add,
        CStarModule.inner_add_right (A := Bᵐᵒᵖ) (E := HilbertModuleFibre B M t), hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply,
      CStarModule.inner_add_left (A := Bᵐᵒᵖ) (E := HilbertModuleFibre B M t), hu, hw]

/-- The proved pairing identity identifies precisely the tensor null kernel. -/
theorem balancedEvaluation_self_eq_zero_iff (t : X)
    (u : BalancedModuleTensor (E := M) (leftRepresentation (B := B) t)) :
    moduleTensorInner (leftRepresentation t) u u = 0 ↔ balancedEvaluation t u = 0 := by
  rw [balancedEvaluation_inner]
  exact CStarModule.inner_self (A := Bᵐᵒᵖ) (E := HilbertModuleFibre B M t)

variable [CompleteSpace M]

/-- Descent through the actual tensor radical, without an assumed null law. -/
def preEvaluationLinear (t : X) :
    PreHilbertModuleTensor (E := M) (leftRepresentation (B := B) t) →ₗ[ℂ]
      HilbertModuleFibre B M t :=
  (moduleTensorNull (leftRepresentation t)).liftQ (balancedEvaluation t) (by
    intro u hu
    exact (balancedEvaluation_self_eq_zero_iff t u).mp
      ((mem_moduleTensorNull_iff (leftRepresentation t) u).mp hu))

@[simp] theorem preEvaluationLinear_mkQ (t : X)
    (u : BalancedModuleTensor (E := M) (leftRepresentation (B := B) t)) :
    preEvaluationLinear t ((moduleTensorNull (leftRepresentation t)).mkQ u) =
      balancedEvaluation t u := rfl

theorem preEvaluationLinear_inner (t : X)
    (u v : PreHilbertModuleTensor (E := M) (leftRepresentation (B := B) t)) :
    ⟪preEvaluationLinear t u, preEvaluationLinear t v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (balancedEvaluation_inner t u v).symm

/-- Fibre evaluation is an actual isometry on the separated tensor. -/
def preEvaluation (t : X) :
    PreHilbertModuleTensor (E := M) (leftRepresentation (B := B) t) →ₗᵢ[ℂ]
      HilbertModuleFibre B M t where
  toLinearMap := preEvaluationLinear t
  norm_map' u := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
      preEvaluationLinear_inner,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]

@[simp] theorem preEvaluation_mk (t : X) (x : M) (b : Bᵐᵒᵖ) :
    preEvaluation t (preModuleTensorMk (leftRepresentation t) x b) =
      b • hilbertModuleFibreMk (B := B) t x := rfl

/-- Extend the proved isometry to the actual norm-completed interior tensor. -/
def evaluationCLM (t : X) :
    InteriorModuleTensor (E := M) (leftRepresentation (B := B) t) →L[ℂ]
      HilbertModuleFibre B M t :=
  (preEvaluation t).toContinuousLinearMap.fromCompletion

@[simp] theorem evaluationCLM_coe (t : X)
    (u : PreHilbertModuleTensor (E := M) (leftRepresentation (B := B) t)) :
    evaluationCLM t (moduleTensorToCompletion (leftRepresentation t) u) =
      preEvaluation t u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem evaluationCLM_norm (t : X)
    (u : InteriorModuleTensor (E := M) (leftRepresentation (B := B) t)) :
    ‖evaluationCLM t u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    change ‖evaluationCLM t (moduleTensorToCompletion (leftRepresentation t) u)‖ =
      ‖moduleTensorToCompletion (leftRepresentation t) u‖
    rw [evaluationCLM_coe, (preEvaluation t).norm_map,
      (moduleTensorToCompletion (leftRepresentation t)).norm_map]

/-- The constructed isometric evaluation from the completed tensor. -/
def evaluation (t : X) :
    InteriorModuleTensor (E := M) (leftRepresentation (B := B) t) →ₗᵢ[ℂ]
      HilbertModuleFibre B M t where
  toLinearMap := (evaluationCLM t).toLinearMap
  norm_map' := evaluationCLM_norm t

@[simp] theorem evaluation_mk (t : X) (x : M) (b : Bᵐᵒᵖ) :
    evaluation t (interiorModuleTensorMk (leftRepresentation t) x b) =
      b • hilbertModuleFibreMk (B := B) t x := evaluationCLM_coe t _

/-- Inner-product preservation survives the genuine completion. -/
theorem evaluation_inner (t : X)
    (u v : InteriorModuleTensor (E := M) (leftRepresentation (B := B) t)) :
    ⟪evaluation t u, evaluation t v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    change ⟪evaluationCLM t (moduleTensorToCompletion (leftRepresentation t) u),
      evaluationCLM t (moduleTensorToCompletion (leftRepresentation t) v)⟫_(Bᵐᵒᵖ) =
      ⟪moduleTensorToCompletion (leftRepresentation t) u,
        moduleTensorToCompletion (leftRepresentation t) v⟫_(Bᵐᵒᵖ)
    rw [evaluationCLM_coe, evaluationCLM_coe]
    exact (preEvaluationLinear_inner t u v).trans
      (hilbertModuleToCompletion_inner u v).symm

variable [T2Space X]

/-- The genuine fibre-map surjectivity and the actual coefficient AU put
every fibre vector in the closed isometric range, also without a unit in B. -/
theorem evaluation_surjective (t : X) :
    Function.Surjective (evaluation (B := B) (M := M) t) := by
  intro z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  have hclosed : IsClosed (Set.range (evaluation (B := B) (M := M) t)) :=
    (evaluation t).isometry.isUniformInducing.isComplete_range.isClosed
  apply hclosed.mem_of_tendsto
    (tendsto_coefficient_approximateUnit_smul (D := Bᵐᵒᵖ)
      (hilbertModuleFibreMk (B := B) t x))
  exact Filter.Eventually.of_forall fun b =>
    ⟨interiorModuleTensorMk (leftRepresentation t) x b, evaluation_mk t x b⟩

/-- The actual Hilbert-module unitary identifying the two fibre constructors. -/
def hilbertEquiv (t : X) :
    HilbertModuleEquiv B
      (InteriorModuleTensor (E := M) (leftRepresentation (B := B) t))
      (HilbertModuleFibre B M t) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (evaluation t) (evaluation_surjective t)
  inner_map := evaluation_inner t

@[simp] theorem hilbertEquiv_mk (t : X) (x : M) (b : Bᵐᵒᵖ) :
    hilbertEquiv t (interiorModuleTensorMk (leftRepresentation t) x b) =
      b • hilbertModuleFibreMk (B := B) t x := evaluation_mk t x b

end HilbertModuleFibreInteriorTensor

variable [T2Space X] [CompleteSpace M]

/-- An arbitrary complete continuous-coefficient module's intrinsic fibre
is unitarily equivalent to its textbook interior tensor along evaluation. -/
def hilbertModuleFibreInteriorTensorEquiv (t : X) :
    HilbertModuleEquiv B
      (InteriorModuleTensor (E := M)
        (HilbertModuleFibreInteriorTensor.leftRepresentation (B := B) t))
      (HilbertModuleFibre B M t) :=
  HilbertModuleFibreInteriorTensor.hilbertEquiv t

@[simp] theorem hilbertModuleFibreInteriorTensorEquiv_mk (t : X) (x : M) (b : Bᵐᵒᵖ) :
    hilbertModuleFibreInteriorTensorEquiv t
      (interiorModuleTensorMk (HilbertModuleFibreInteriorTensor.leftRepresentation t) x b) =
      b • hilbertModuleFibreMk (B := B) t x :=
  HilbertModuleFibreInteriorTensor.hilbertEquiv_mk t x b

end BC4lean.KKTheory
