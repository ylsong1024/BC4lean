import BC4lean.ClosedStarHomKernelModule
import BC4lean.IntervalModuleFibreNorm
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Skandalis's genuine nonunital left-unit interval ideal

For U = Unitization ℂ A the module J is the actual closed two-sided ideal
{f : C(I,U) | f(1) belongs to inr A}, considered as a right Hilbert C(I,U)
module. It is the scalar-evaluation kernel, not a presumed complemented
essential submodule. Constant A left multipliers have actual rank-one
approximants with both vectors in C(I,A). The original Fredholm operator
is not asserted to define a Unitization(A)-cycle.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def leftUnitScalarQuotient : Unitization ℂ A →⋆ₐ[ℂ] ℂ :=
  { Unitization.fstHom ℂ A with map_star' := Unitization.fst_star }

def leftUnitIntervalScalarQuotient : C(unitInterval, Unitization ℂ A) →⋆ₐ[ℂ] ℂ where
  toFun f := (f 1).fst
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

abbrev LeftUnitIntervalIdeal (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  StarHomKernelModule (D := C(unitInterval, Unitization ℂ A)) (C := ℂ)
    (leftUnitIntervalScalarQuotient (A := A))

abbrev LeftUnitCoefficientIdeal (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  StarHomKernelModule (D := Unitization ℂ A) (C := ℂ)
    (leftUnitScalarQuotient (A := A))

@[simp] theorem leftUnitIntervalIdeal_scalar_one (x : LeftUnitIntervalIdeal A) :
    ((MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ)) 1).fst = 0 := x.property

omit [PartialOrder A] [StarOrderedRing A] in
theorem leftUnitUnitization_separableSpace [TopologicalSpace.SeparableSpace A] :
    TopologicalSpace.SeparableSpace (Unitization ℂ A) :=
  Unitization.uniformEquivProd.symm.surjective.denseRange.separableSpace
    Unitization.uniformEquivProd.symm.uniformContinuous.continuous

theorem leftUnitIntervalIdeal_countablyGenerated [TopologicalSpace.SeparableSpace A] :
    IsCountablyGeneratedModule C(unitInterval, Unitization ℂ A) (LeftUnitIntervalIdeal A) := by
  let := leftUnitUnitization_separableSpace (A := A)
  let : TopologicalSpace.SeparableSpace C(unitInterval, Unitization ℂ A) := inferInstance
  exact starHomKernelModule_countablyGenerated
    (D := C(unitInterval, Unitization ℂ A)) (C := ℂ)
    (leftUnitIntervalScalarQuotient (A := A))

def leftUnitIntervalCoefficientHom : A →⋆ₙₐ[ℂ] C(unitInterval, Unitization ℂ A) where
  toFun a := ContinuousMap.const unitInterval (a : Unitization ℂ A)
  map_zero' := by apply ContinuousMap.ext; intro t; exact map_zero (Unitization.inrNonUnitalStarAlgHom ℂ A)
  map_add' a b := by apply ContinuousMap.ext; intro t; exact map_add (Unitization.inrNonUnitalStarAlgHom ℂ A) a b
  map_mul' a b := by apply ContinuousMap.ext; intro t; exact map_mul (Unitization.inrNonUnitalStarAlgHom ℂ A) a b
  map_smul' c a := by apply ContinuousMap.ext; intro t; exact map_smul (Unitization.inrNonUnitalStarAlgHom ℂ A) c a
  map_star' a := by apply ContinuousMap.ext; intro t; exact map_star (Unitization.inrNonUnitalStarAlgHom ℂ A) a

def leftUnitIntervalRepresentation : A →⋆ₙₐ[ℂ]
    AdjointableMap C(unitInterval, Unitization ℂ A) (LeftUnitIntervalIdeal A) (LeftUnitIntervalIdeal A) :=
  (starHomKernelLeftMul (D := C(unitInterval, Unitization ℂ A)) (C := ℂ)
    (leftUnitIntervalScalarQuotient (A := A))).comp leftUnitIntervalCoefficientHom

@[simp] theorem leftUnitIntervalRepresentation_apply (a : A) (x : LeftUnitIntervalIdeal A)
    (t : unitInterval) :
    MulOpposite.unop (leftUnitIntervalRepresentation a x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t =
      (a : Unitization ℂ A) * MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t := rfl

def leftUnitIntervalConstant (a : A) : LeftUnitIntervalIdeal A :=
  ⟨MulOpposite.op (ContinuousMap.const unitInterval (a : Unitization ℂ A)), rfl⟩

@[simp] theorem leftUnitIntervalConstant_apply (a : A) (t : unitInterval) :
    MulOpposite.unop (leftUnitIntervalConstant a : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t =
      (a : Unitization ℂ A) := rfl

/-- These are genuine J-rank ones with both defining vectors in C(I,A). -/
theorem leftUnitIntervalRankOne_constant (a u : A) :
    moduleRankOne (B := C(unitInterval, Unitization ℂ A))
        (leftUnitIntervalConstant a) (leftUnitIntervalConstant (star u)) =
      leftUnitIntervalRepresentation (a * u) := by
  rw [starHomKernelRankOne_eq_leftMul
    (D := C(unitInterval, Unitization ℂ A)) (C := ℂ)
    (leftUnitIntervalScalarQuotient (A := A))]
  apply congrArg (starHomKernelLeftMul
    (D := C(unitInterval, Unitization ℂ A)) (C := ℂ)
    (leftUnitIntervalScalarQuotient (A := A)))
  apply ContinuousMap.ext
  intro t
  simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, leftUnitIntervalConstant_apply]
  change (a : Unitization ℂ A) * star ((star u : A) : Unitization ℂ A) =
    ((a * u : A) : Unitization ℂ A)
  simp only [← Unitization.inr_star, star_star, ← Unitization.inr_mul]

private def leftUnitIntervalRepresentationCLM : A →L[ℂ]
    AdjointableMap C(unitInterval, Unitization ℂ A)
      (LeftUnitIntervalIdeal A) (LeftUnitIntervalIdeal A) := by
  let ι : A →L[ℂ] Unitization ℂ A :=
    { Unitization.inrHom ℂ ℂ A with cont := Unitization.continuous_inr }
  let κ : A →L[ℂ] C(unitInterval, Unitization ℂ A) :=
    (ContinuousLinearMap.const (R := ℂ) (M := Unitization ℂ A) unitInterval).comp ι
  exact
    (starHomKernelLeftMulContinuous (D := C(unitInterval, Unitization ℂ A)) (C := ℂ)
      (leftUnitIntervalScalarQuotient (A := A))).comp κ

private theorem leftUnitIntervalRepresentationCLM_apply (a : A) :
    leftUnitIntervalRepresentationCLM a = leftUnitIntervalRepresentation a := rfl

/-- Constant left A multiplication is genuinely compact on J. The proof
uses actual rank-one operators and the coefficient approximate unit in A. -/
theorem leftUnitIntervalRepresentation_isModuleCompact (a : A) :
    IsModuleCompact (leftUnitIntervalRepresentation a) := by
  have hlim := ((leftUnitIntervalRepresentationCLM (A := A)).continuous.tendsto a).comp
    ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left a)
  rw [← leftUnitIntervalRepresentationCLM_apply a]
  apply (moduleCompact_isClosed (B := C(unitInterval, Unitization ℂ A))
    (E := LeftUnitIntervalIdeal A) (F := LeftUnitIntervalIdeal A)).mem_of_tendsto hlim
  exact Eventually.of_forall fun u => by
    rw [Function.comp_apply, leftUnitIntervalRepresentationCLM_apply,
      ← leftUnitIntervalRankOne_constant a u]
    exact moduleRankOne_mem_moduleCompact _ _

/-- Left A localization puts every coefficient of a frame rank approximation
in C(I,A), even though unlocalized J inner coefficients can have scalar part. -/
theorem leftUnitIntervalLocalizedInner_scalar_zero (a : A)
    (x y : LeftUnitIntervalIdeal A) (t : unitInterval) :
    (MulOpposite.unop ⟪x, leftUnitIntervalRepresentation a y⟫_
      (C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t).fst = 0 := by
  change (star (MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t) *
    ((a : Unitization ℂ A) * MulOpposite.unop (y : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t)).fst = 0
  simp only [Unitization.fst_mul, Unitization.fst_inr, zero_mul, mul_zero]

def leftUnitIntervalLocalizedInner (a : A) (x y : LeftUnitIntervalIdeal A) : C(unitInterval, A) :=
  ⟨fun t => (MulOpposite.unop ⟪x, leftUnitIntervalRepresentation a y⟫_
      (C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t).snd,
    Unitization.continuous_snd.comp
      (MulOpposite.unop ⟪x, leftUnitIntervalRepresentation a y⟫_
        (C(unitInterval, Unitization ℂ A)ᵐᵒᵖ)).continuous⟩

theorem leftUnitIntervalLocalizedInner_inr (a : A) (x y : LeftUnitIntervalIdeal A)
    (t : unitInterval) :
    (leftUnitIntervalLocalizedInner a x y t : Unitization ℂ A) =
      MulOpposite.unop ⟪x, leftUnitIntervalRepresentation a y⟫_
        (C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t := by
  apply Unitization.ext
  · exact (leftUnitIntervalLocalizedInner_scalar_zero a x y t).symm
  · rfl

def leftUnitIntervalEvaluation (t : unitInterval) :
    LeftUnitIntervalIdeal A →L[ℂ] (Unitization ℂ A)ᵐᵒᵖ :=
  ({ toFun x := MulOpposite.op (MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t)
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : LeftUnitIntervalIdeal A →ₗ[ℂ] (Unitization ℂ A)ᵐᵒᵖ).mkContinuous
    1 (fun x => by
      change ‖MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t‖ ≤
        1 * ‖MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ)‖
      rw [one_mul]
      exact (MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ)).norm_coe_le_norm t)

@[simp] theorem leftUnitIntervalEvaluation_inner (t : unitInterval)
    (x y : LeftUnitIntervalIdeal A) :
    ⟪leftUnitIntervalEvaluation t x, leftUnitIntervalEvaluation t y⟫_((Unitization ℂ A)ᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t) := rfl

/-- The scalar ramp vanishes only at the A endpoint and evaluates to the
actual unit of U at zero. -/
def leftUnitIntervalRamp (u : (Unitization ℂ A)ᵐᵒᵖ) : LeftUnitIntervalIdeal A :=
  ⟨MulOpposite.op
    ⟨fun t => (1 - (t : ℝ)) • MulOpposite.unop u,
      (continuous_const.sub continuous_subtype_val).smul continuous_const⟩,
    by change (((1 : ℝ) - 1) • MulOpposite.unop u).fst = 0; simp⟩

@[simp] theorem leftUnitIntervalEvaluation_zero_ramp (u : (Unitization ℂ A)ᵐᵒᵖ) :
    leftUnitIntervalEvaluation 0 (leftUnitIntervalRamp u) = u := by
  change MulOpposite.op (((1 : ℝ) - 0) • MulOpposite.unop u) = u
  simp only [sub_zero, one_smul, MulOpposite.op_unop]

theorem leftUnitIntervalEvaluation_zero_surjective :
    Function.Surjective (leftUnitIntervalEvaluation (A := A) 0) :=
  fun u => ⟨leftUnitIntervalRamp u, leftUnitIntervalEvaluation_zero_ramp u⟩

def leftUnitIntervalEvaluationOne : LeftUnitIntervalIdeal A →L[ℂ] LeftUnitCoefficientIdeal A :=
  (leftUnitIntervalEvaluation 1).codRestrict
    (starHomKernelSubmodule (D := Unitization ℂ A) (C := ℂ)
      (leftUnitScalarQuotient (A := A)))
    (fun x => x.property)

@[simp] theorem leftUnitIntervalEvaluationOne_coe (x : LeftUnitIntervalIdeal A) :
    (leftUnitIntervalEvaluationOne x : (Unitization ℂ A)ᵐᵒᵖ) = leftUnitIntervalEvaluation 1 x := rfl

def leftUnitIntervalIdealConstant (u : LeftUnitCoefficientIdeal A) : LeftUnitIntervalIdeal A :=
  ⟨MulOpposite.op (ContinuousMap.const unitInterval (MulOpposite.unop (u : (Unitization ℂ A)ᵐᵒᵖ))),
    u.property⟩

theorem leftUnitIntervalEvaluationOne_surjective :
    Function.Surjective (leftUnitIntervalEvaluationOne (A := A)) := by
  intro u
  refine ⟨leftUnitIntervalIdealConstant u, ?_⟩
  apply Subtype.ext
  rfl

theorem leftUnitIntervalEvaluationOne_inner (x y : LeftUnitIntervalIdeal A) :
    ⟪leftUnitIntervalEvaluationOne x, leftUnitIntervalEvaluationOne y⟫_((Unitization ℂ A)ᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 1) := rfl

def leftUnitIntervalZeroFibreEquiv : HilbertModuleEquiv (Unitization ℂ A)
    (HilbertModuleFibre (Unitization ℂ A) (LeftUnitIntervalIdeal A) (0 : unitInterval))
      (Unitization ℂ A)ᵐᵒᵖ :=
  hilbertModuleFibreEquivOfEvaluation (B := Unitization ℂ A) (X := unitInterval)
    0 (leftUnitIntervalEvaluation 0)
    (leftUnitIntervalEvaluation_inner 0) leftUnitIntervalEvaluation_zero_surjective

def leftUnitIntervalOneFibreEquiv : HilbertModuleEquiv (Unitization ℂ A)
    (HilbertModuleFibre (Unitization ℂ A) (LeftUnitIntervalIdeal A) (1 : unitInterval))
      (LeftUnitCoefficientIdeal A) :=
  hilbertModuleFibreEquivOfEvaluation (B := Unitization ℂ A) (X := unitInterval)
    1 leftUnitIntervalEvaluationOne
    leftUnitIntervalEvaluationOne_inner leftUnitIntervalEvaluationOne_surjective

@[simp] theorem leftUnitIntervalZeroFibreEquiv_mk (x : LeftUnitIntervalIdeal A) :
    leftUnitIntervalZeroFibreEquiv
      (hilbertModuleFibreMk (B := Unitization ℂ A) (X := unitInterval) 0 x) =
      leftUnitIntervalEvaluation 0 x :=
  hilbertModuleFibreEquivOfEvaluation_mk (B := Unitization ℂ A) (X := unitInterval) 0 _ _ _ x

@[simp] theorem leftUnitIntervalOneFibreEquiv_mk (x : LeftUnitIntervalIdeal A) :
    leftUnitIntervalOneFibreEquiv
      (hilbertModuleFibreMk (B := Unitization ℂ A) (X := unitInterval) 1 x) =
      leftUnitIntervalEvaluationOne x :=
  hilbertModuleFibreEquivOfEvaluation_mk (B := Unitization ℂ A) (X := unitInterval) 1 _ _ _ x

/-- The A ideal in U has its actual A norm, with the embedding recorded
separately from the different coefficient action. -/
def leftUnitCoefficientIdealInr : Aᵐᵒᵖ ≃ₗᵢ[ℂ] LeftUnitCoefficientIdeal A where
  toFun a := ⟨MulOpposite.op ((MulOpposite.unop a : A) : Unitization ℂ A), rfl⟩
  invFun u := MulOpposite.op (MulOpposite.unop (u : (Unitization ℂ A)ᵐᵒᵖ)).snd
  left_inv _ := rfl
  right_inv u := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply Unitization.ext
    · exact u.property.symm
    · rfl
  map_add' a b := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact Unitization.inr_add ℂ _ _
  map_smul' c a := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact Unitization.inr_smul ℂ c _
  norm_map' a := by
    change ‖((MulOpposite.unop a : A) : Unitization ℂ A)‖ = ‖MulOpposite.unop a‖
    exact Unitization.norm_inr _

theorem leftUnitCoefficientIdealInr_inner (x y : Aᵐᵒᵖ) :
    ⟪leftUnitCoefficientIdealInr x, leftUnitCoefficientIdealInr y⟫_((Unitization ℂ A)ᵐᵒᵖ) =
      MulOpposite.op ((MulOpposite.unop ⟪x, y⟫_(Aᵐᵒᵖ) : A) : Unitization ℂ A) := by
  apply MulOpposite.unop_injective
  change star ((MulOpposite.unop x : A) : Unitization ℂ A) *
    ((MulOpposite.unop y : A) : Unitization ℂ A) =
    ((star (MulOpposite.unop x) * MulOpposite.unop y : A) : Unitization ℂ A)
  simp only [← Unitization.inr_star, ← Unitization.inr_mul]

theorem leftUnitCoefficientIdealInr_unitization_smul (u : Unitization ℂ A) (x : Aᵐᵒᵖ) :
    leftUnitCoefficientIdealInr (u.fst • x + MulOpposite.op u.snd • x) =
      MulOpposite.op u • leftUnitCoefficientIdealInr x := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change ((u.fst • (MulOpposite.unop x : A) + (MulOpposite.unop x : A) * u.snd : A) :
    Unitization ℂ A) = ((MulOpposite.unop x : A) : Unitization ℂ A) * u
  apply Unitization.ext
  · simp only [Unitization.fst_inr, Unitization.fst_mul, zero_mul]
  · simp only [Unitization.snd_inr, Unitization.snd_mul, Unitization.fst_inr,
      zero_smul, zero_add]

end BC4lean.KKTheory
