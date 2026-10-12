import BC4lean.PositiveModuleQuotient
import BC4lean.HilbertModuleCompletion
import BC4lean.AdjointableCompletion
import BC4lean.StandardModuleOperator
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # The genuine standard countable right Hilbert B-module

Finite coefficient vectors carry their actual finite sum of coefficient-valued
inner products. The positive form is definite, proved by positivity of each
coordinate square. Its null radical is therefore zero. The norm on the radical
quotient is exactly the square root of the norm of that finite coefficient sum;
completing it gives H_B. This uses neither an lp norm on B nor an assumed
stabilization theorem. Coordinate inclusion and evaluation are proved adjoints.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Finite coefficient vectors, without imposing an unrelated Banach-space norm. -/
abbrev StandardCountableVectors (B : Type*) [Zero B] := ℕ →₀ Bᵐᵒᵖ

/-- The actual coefficient-valued finite-vector form. -/
def standardCountableFiniteInner (x y : StandardCountableVectors B) : Bᵐᵒᵖ :=
  x.sum fun i b => ⟪b, y i⟫_(Bᵐᵒᵖ)

/-- In the coefficient algebra itself, the form is exactly the usual sum x_i* y_i. -/
theorem standardCountableFiniteInner_unop (x y : StandardCountableVectors B) :
    MulOpposite.unop (standardCountableFiniteInner x y) =
      ∑ i ∈ x.support, star (MulOpposite.unop (x i)) * MulOpposite.unop (y i) := by
  change MulOpposite.unop (∑ i ∈ x.support, y i * star (x i)) = _
  simp only [Finset.unop_sum, MulOpposite.unop_mul, MulOpposite.unop_star]

theorem standardCountableFiniteInner_eq_sum (x y : StandardCountableVectors B) (s : Finset ℕ)
    (h : x.support ⊆ s) :
    standardCountableFiniteInner x y = ∑ i ∈ s, ⟪x i, y i⟫_(Bᵐᵒᵖ) :=
  Finsupp.sum_of_support_subset x h _ (fun _ _ => CStarModule.inner_zero_left)

theorem standardCountableFiniteInner_star (x y : StandardCountableVectors B) :
    star (standardCountableFiniteInner x y) = standardCountableFiniteInner y x := by
  rw [standardCountableFiniteInner_eq_sum x y (x.support ∪ y.support) Finset.subset_union_left,
    standardCountableFiniteInner_eq_sum y x (x.support ∪ y.support) Finset.subset_union_right,
    star_sum]
  exact Finset.sum_congr rfl fun i _ => CStarModule.star_inner (x i) (y i)

/-- All positive-form laws follow from the finite coefficient sum. -/
instance standardCountableFinitePositiveForm : PositiveModuleForm B (StandardCountableVectors B) where
  inner := standardCountableFiniteInner
  inner_add_right := by
    intro x y z
    simp only [standardCountableFiniteInner, Finsupp.sum, Finsupp.add_apply,
      CStarModule.inner_add_right, Finset.sum_add_distrib]
  inner_self_nonneg := by
    intro x
    exact Finset.sum_nonneg (fun _ _ => CStarModule.inner_self_nonneg)
  inner_op_smul_right := by
    intro a x y
    simp only [standardCountableFiniteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_op_smul_right, Finset.mul_sum]
  inner_smul_right_complex := by
    intro c x y
    simp only [standardCountableFiniteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_smul_right_complex, Finset.smul_sum]
  star_inner := standardCountableFiniteInner_star

@[simp] theorem standardCountableFinite_inner (x y : StandardCountableVectors B) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = standardCountableFiniteInner x y := rfl

/-- Each positive coordinate square is bounded by the entire finite square sum. -/
theorem standardCountableFinite_coordinate_inner_le (x : StandardCountableVectors B) (i : ℕ) :
    ⟪x i, x i⟫_(Bᵐᵒᵖ) ≤ standardCountableFiniteInner x x := by
  by_cases hi : i ∈ x.support
  · exact Finset.single_le_sum (fun _ _ => CStarModule.inner_self_nonneg) hi
  · have hz : x i = 0 := Finsupp.notMem_support_iff.mp hi
    simpa only [hz, CStarModule.inner_zero_left, standardCountableFinite_inner] using
      (PositiveModuleForm.inner_self_nonneg (B := B) (x := x))

/-- The finite-vector form is definite; zero inner square forces every coefficient to vanish. -/
theorem standardCountableFiniteInner_self_eq_zero_iff (x : StandardCountableVectors B) :
    standardCountableFiniteInner x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have hi : ⟪x i, x i⟫_(Bᵐᵒᵖ) = 0 := le_antisymm
      (hx ▸ standardCountableFinite_coordinate_inner_le x i) CStarModule.inner_self_nonneg
    exact CStarModule.inner_self.mp hi
  · rintro rfl
    simp [standardCountableFiniteInner]

/-- The radical is proved zero before the normed quotient is used. -/
theorem standardCountableFinite_nullRadical_eq_bot :
    PositiveModuleForm.nullRadical (B := B) (E := StandardCountableVectors B) = ⊥ := by
  ext x
  rw [PositiveModuleForm.mem_nullRadical, standardCountableFinite_inner,
    standardCountableFiniteInner_self_eq_zero_iff, Submodule.mem_bot]

/-- Coordinate inclusion has the genuine coefficient inner-product adjoint law. -/
@[simp] theorem standardCountableFiniteInner_single_left (i : ℕ) (b : Bᵐᵒᵖ)
    (x : StandardCountableVectors B) :
    standardCountableFiniteInner (Finsupp.single i b) x = ⟪b, x i⟫_(Bᵐᵒᵖ) := by
  simp [standardCountableFiniteInner]

theorem standardCountableFinite_formNorm_single (i : ℕ) (b : Bᵐᵒᵖ) :
    PositiveModuleForm.formNorm (B := B) (Finsupp.single i b) = ‖b‖ := by
  rw [PositiveModuleForm.formNorm, standardCountableFinite_inner,
    standardCountableFiniteInner_single_left, Finsupp.single_eq_same]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) b).symm

theorem standardCountableFinite_norm_coordinate_le (x : StandardCountableVectors B) (i : ℕ) :
    ‖x i‖ ≤ PositiveModuleForm.formNorm (B := B) x := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x i), PositiveModuleForm.formNorm]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le CStarModule.inner_self_nonneg
    (standardCountableFinite_coordinate_inner_le x i)

/-- The finite vectors with the actual form-derived Hilbert norm. -/
abbrev StandardCountablePreModule (B : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] := PositiveModuleQuotient B (StandardCountableVectors B)

theorem standardCountablePreMk_injective :
    Function.Injective (positiveModuleQuotientMk (B := B) (E := StandardCountableVectors B)) := by
  intro x y h
  have hr := (PositiveModuleQuotient.mk_eq_mk x y).mp h
  rw [standardCountableFinite_nullRadical_eq_bot, Submodule.mem_bot] at hr
  exact sub_eq_zero.mp hr

/-- H_B is the completion of the actual finite coefficient-inner-product norm. -/
abbrev StandardCountableHilbertModule (B : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] := Completion (StandardCountablePreModule B)

/-- The canonical finite-vector map to H_B. -/
def standardCountableMk : StandardCountableVectors B →ₗ[ℂ] StandardCountableHilbertModule B :=
  Completion.toComplL.toLinearMap.comp (positiveModuleQuotientMk (B := B))

@[simp] theorem standardCountableMk_apply (x : StandardCountableVectors B) :
    standardCountableMk x = ((positiveModuleQuotientMk (B := B) x) : StandardCountableHilbertModule B) := rfl

theorem standardCountableMk_injective : Function.Injective (standardCountableMk (B := B)) :=
  (Completion.coe_injective _).comp standardCountablePreMk_injective

/-- Finite coefficient vectors have genuinely dense canonical image in H_B. -/
theorem standardCountableMk_denseRange : DenseRange (standardCountableMk (B := B)) :=
  Completion.denseRange_coe.comp positiveModuleQuotientMk_surjective.denseRange (Completion.continuous_coe _)

@[simp] theorem standardCountableMk_inner (x y : StandardCountableVectors B) :
    ⟪standardCountableMk x, standardCountableMk y⟫_(Bᵐᵒᵖ) = standardCountableFiniteInner x y := by
  rw [standardCountableMk_apply, standardCountableMk_apply, completionInner_coe,
    PositiveModuleQuotient.inner_mk]
  rfl

/-- The canonical finite-vector norm is the square root of the actual coefficient sum. -/
@[simp] theorem standardCountableMk_norm (x : StandardCountableVectors B) :
    ‖standardCountableMk x‖ = Real.sqrt ‖x.sum (fun i b => ⟪b, x i⟫_(Bᵐᵒᵖ))‖ := by
  rw [standardCountableMk_apply, Completion.norm_coe, PositiveModuleQuotient.norm_mk]
  rfl

/-- The H_B norm uses the norm of the sum of positive coefficient squares. -/
theorem standardCountableMk_norm_coefficients (x : StandardCountableVectors B) :
    ‖standardCountableMk x‖ =
      Real.sqrt ‖∑ i ∈ x.support, star (MulOpposite.unop (x i)) * MulOpposite.unop (x i)‖ := by
  rw [standardCountableMk_norm]
  change Real.sqrt ‖standardCountableFiniteInner x x‖ = _
  rw [← MulOpposite.norm_unop (standardCountableFiniteInner x x), standardCountableFiniteInner_unop]

@[simp] theorem standardCountableMk_op_smul (a : Bᵐᵒᵖ) (x : StandardCountableVectors B) :
    standardCountableMk (a • x) = a • standardCountableMk x := by
  rw [standardCountableMk_apply, standardCountableMk_apply, completion_op_smul_coe,
    PositiveModuleQuotient.op_smul_mk]

/-- Evaluation descends because the finite-vector radical is proved zero. -/
def standardCountableQuotientEvaluationLinear (i : ℕ) : StandardCountablePreModule B →ₗ[ℂ] Bᵐᵒᵖ :=
  (PositiveModuleForm.nullRadical (B := B) (E := StandardCountableVectors B)).liftQ
    (Finsupp.lapply i) (fun x hx => by
      rw [standardCountableFinite_nullRadical_eq_bot, Submodule.mem_bot] at hx
      simp [hx])

@[simp] theorem standardCountableQuotientEvaluationLinear_mk (i : ℕ) (x : StandardCountableVectors B) :
    standardCountableQuotientEvaluationLinear i (positiveModuleQuotientMk (B := B) x) = x i := rfl

def standardCountableQuotientEvaluationCLM (i : ℕ) : StandardCountablePreModule B →L[ℂ] Bᵐᵒᵖ :=
  (standardCountableQuotientEvaluationLinear i).mkContinuous 1 (fun q => by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    simpa only [standardCountableQuotientEvaluationLinear_mk, PositiveModuleQuotient.norm_mk, one_mul]
      using standardCountableFinite_norm_coordinate_le x i)

def standardCountableQuotientInclusionCLM (i : ℕ) : Bᵐᵒᵖ →L[ℂ] StandardCountablePreModule B :=
  ((positiveModuleQuotientMk (B := B)).comp (Finsupp.lsingle i)).mkContinuous 1
    (fun b => by
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, PositiveModuleQuotient.norm_mk,
        standardCountableFinite_formNorm_single, one_mul, le_refl])

/-- Coordinate inclusion and evaluation on the normed finite-vector module are adjoints. -/
def standardCountableQuotientInclusion (i : ℕ) :
    AdjointableMap B Bᵐᵒᵖ (StandardCountablePreModule B) where
  toCLM := standardCountableQuotientInclusionCLM i
  adjointCLM := standardCountableQuotientEvaluationCLM (B := B) i
  adjoint_identity b q := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    change ⟪positiveModuleQuotientMk (B := B) (Finsupp.single i b),
      positiveModuleQuotientMk (B := B) x⟫_(Bᵐᵒᵖ) = ⟪b, x i⟫_(Bᵐᵒᵖ)
    rw [PositiveModuleQuotient.inner_mk]
    exact standardCountableFiniteInner_single_left i b x

/-- The complete-module coordinate inclusion, with its adjoint extended into complete B. -/
def standardCountableInclusion (i : ℕ) : AdjointableMap B Bᵐᵒᵖ (StandardCountableHilbertModule B) where
  toCLM := Completion.toComplL.comp (standardCountableQuotientInclusion (B := B) i).toCLM
  adjointCLM := (standardCountableQuotientInclusion (B := B) i).adjointCLM.fromCompletion
  adjoint_identity b x := by
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp (continuous_const.prodMk continuous_id))
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk (standardCountableQuotientInclusion (B := B) i).adjointCLM.fromCompletion.continuous))
    · intro q
      change ⟪(((standardCountableQuotientInclusion (B := B) i).toCLM b : StandardCountablePreModule B) :
        StandardCountableHilbertModule B), (q : StandardCountableHilbertModule B)⟫_(Bᵐᵒᵖ) =
        ⟪b, (standardCountableQuotientInclusion (B := B) i).adjointCLM.fromCompletion
          (q : StandardCountableHilbertModule B)⟫_(Bᵐᵒᵖ)
      rw [completionInner_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      exact (standardCountableQuotientInclusion (B := B) i).adjoint_identity b q

/-- Actual coordinate evaluation is the proved coordinate inclusion adjoint. -/
def standardCountableEvaluation (i : ℕ) : AdjointableMap B (StandardCountableHilbertModule B) Bᵐᵒᵖ :=
  (standardCountableInclusion (B := B) i).adjoint

@[simp] theorem standardCountableInclusion_apply (i : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableInclusion i b = standardCountableMk (Finsupp.single i b) := rfl

@[simp] theorem standardCountableEvaluation_mk (i : ℕ) (x : StandardCountableVectors B) :
    standardCountableEvaluation i (standardCountableMk x) = x i := by
  rw [standardCountableMk_apply]
  change (standardCountableQuotientEvaluationCLM (B := B) i).fromCompletion
    ((positiveModuleQuotientMk (B := B) x) : StandardCountableHilbertModule B) = x i
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

@[simp] theorem standardCountableInclusion_norm (i : ℕ) (b : Bᵐᵒᵖ) :
    ‖standardCountableInclusion i b‖ = ‖b‖ := by
  rw [standardCountableInclusion_apply, standardCountableMk_apply, Completion.norm_coe,
    PositiveModuleQuotient.norm_mk, standardCountableFinite_formNorm_single]

theorem norm_standardCountableInclusion_le (i : ℕ) : ‖standardCountableInclusion (B := B) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b
  change ‖standardCountableInclusion (B := B) i b‖ ≤ 1 * ‖b‖
  rw [standardCountableInclusion_norm, one_mul]

theorem norm_standardCountableEvaluation_le (i : ℕ) : ‖standardCountableEvaluation (B := B) i‖ ≤ 1 := by
  change ‖(standardCountableInclusion (B := B) i).adjoint.toCLM‖ ≤ 1
  rw [AdjointableMap.norm_adjoint_toCLM]
  exact norm_standardCountableInclusion_le i

end BC4lean.KKTheory
