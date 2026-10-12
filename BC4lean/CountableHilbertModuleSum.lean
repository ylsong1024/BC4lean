import BC4lean.PositiveModuleQuotient
import BC4lean.HilbertModuleCompletion
import BC4lean.AdjointableCompletion
import BC4lean.AdjointableNorm
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Genuine countable sums of a right Hilbert module

Finite vectors with entries in E carry the finite sum of their B-valued inner
products. Removing the proved zero radical and completing its form norm gives
the countable Hilbert-module sum. Its norm is the square root of the coefficient
sum norm; scalar summability of the squared entry norms is not imposed. For
complete E, coordinate inclusion and evaluation are actual adjoint pairs.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

abbrev CountableModuleVectors (E : Type*) [Zero E] := ℕ →₀ E

/-- The given coefficient action preserves zero, by nondegeneracy of the inner product. -/
instance countableModuleCoefficientSMulZeroClass : SMulZeroClass Bᵐᵒᵖ E where
  smul_zero a := by
    apply module_inner_ext_right (B := B)
    intro z
    simp only [CStarModule.inner_op_smul_right, CStarModule.inner_zero_right, mul_zero]

/-- The actual finite coefficient form of a sequence of module vectors. -/
def countableModuleFiniteInner (x y : CountableModuleVectors E) : Bᵐᵒᵖ :=
  x.sum fun i v => ⟪v, y i⟫_(Bᵐᵒᵖ)

omit [StarOrderedRing B] in
theorem countableModuleFiniteInner_eq_sum (x y : CountableModuleVectors E) (s : Finset ℕ)
    (h : x.support ⊆ s) :
    countableModuleFiniteInner (B := B) x y = ∑ i ∈ s, ⟪x i, y i⟫_(Bᵐᵒᵖ) :=
  Finsupp.sum_of_support_subset x h _ (fun _ _ => CStarModule.inner_zero_left)

omit [StarOrderedRing B] in
theorem countableModuleFiniteInner_star (x y : CountableModuleVectors E) :
    star (countableModuleFiniteInner (B := B) x y) = countableModuleFiniteInner (B := B) y x := by
  rw [countableModuleFiniteInner_eq_sum x y (x.support ∪ y.support) Finset.subset_union_left,
    countableModuleFiniteInner_eq_sum y x (x.support ∪ y.support) Finset.subset_union_right,
    star_sum]
  exact Finset.sum_congr rfl fun i _ => CStarModule.star_inner (x i) (y i)

instance countableModuleFinitePositiveForm : PositiveModuleForm B (CountableModuleVectors E) where
  inner := countableModuleFiniteInner
  inner_add_right := by
    intro x y z
    simp only [countableModuleFiniteInner, Finsupp.sum, Finsupp.add_apply,
      CStarModule.inner_add_right, Finset.sum_add_distrib]
  inner_self_nonneg := by
    intro x
    exact Finset.sum_nonneg (fun _ _ => CStarModule.inner_self_nonneg)
  inner_op_smul_right := by
    intro a x y
    simp only [countableModuleFiniteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_op_smul_right, Finset.mul_sum]
  inner_smul_right_complex := by
    intro c x y
    simp only [countableModuleFiniteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_smul_right_complex, Finset.smul_sum]
  star_inner := countableModuleFiniteInner_star

@[simp] theorem countableModuleFinite_inner (x y : CountableModuleVectors E) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = countableModuleFiniteInner (B := B) x y := rfl

theorem countableModuleFinite_coordinate_inner_le (x : CountableModuleVectors E) (i : ℕ) :
    ⟪x i, x i⟫_(Bᵐᵒᵖ) ≤ countableModuleFiniteInner (B := B) x x := by
  by_cases hi : i ∈ x.support
  · exact Finset.single_le_sum (fun _ _ => CStarModule.inner_self_nonneg) hi
  · have hz : x i = 0 := Finsupp.notMem_support_iff.mp hi
    simpa only [hz, CStarModule.inner_zero_left, countableModuleFinite_inner] using
      (PositiveModuleForm.inner_self_nonneg (B := B) (x := x))

theorem countableModuleFiniteInner_self_eq_zero_iff (x : CountableModuleVectors E) :
    countableModuleFiniteInner (B := B) x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have hi : ⟪x i, x i⟫_(Bᵐᵒᵖ) = 0 := le_antisymm
      (hx ▸ countableModuleFinite_coordinate_inner_le x i) CStarModule.inner_self_nonneg
    exact CStarModule.inner_self.mp hi
  · rintro rfl
    simp [countableModuleFiniteInner]

theorem countableModuleFinite_nullRadical_eq_bot :
    PositiveModuleForm.nullRadical (B := B) (E := CountableModuleVectors E) = ⊥ := by
  ext x
  rw [PositiveModuleForm.mem_nullRadical, countableModuleFinite_inner,
    countableModuleFiniteInner_self_eq_zero_iff, Submodule.mem_bot]

omit [StarOrderedRing B] in
@[simp] theorem countableModuleFiniteInner_single_left (i : ℕ) (v : E) (x : CountableModuleVectors E) :
    countableModuleFiniteInner (B := B) (Finsupp.single i v) x = ⟪v, x i⟫_(Bᵐᵒᵖ) := by
  simp [countableModuleFiniteInner]

theorem countableModuleFinite_formNorm_single (i : ℕ) (v : E) :
    PositiveModuleForm.formNorm (B := B) (Finsupp.single i v) = ‖v‖ := by
  rw [PositiveModuleForm.formNorm, countableModuleFinite_inner,
    countableModuleFiniteInner_single_left, Finsupp.single_eq_same]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) v).symm

theorem countableModuleFinite_norm_coordinate_le (x : CountableModuleVectors E) (i : ℕ) :
    ‖x i‖ ≤ PositiveModuleForm.formNorm (B := B) x := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x i), PositiveModuleForm.formNorm]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le CStarModule.inner_self_nonneg
    (countableModuleFinite_coordinate_inner_le x i)

/-- Finite module vectors with their actual form-derived Hilbert norm. -/
abbrev CountableHilbertModulePreSum (B E : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] :=
  PositiveModuleQuotient B (CountableModuleVectors E)

/-- The actual countable Hilbert-module sum, completed in its coefficient norm. -/
abbrev CountableHilbertModuleSum (B E : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] :=
  Completion (CountableHilbertModulePreSum B E)

def countableModuleMk : CountableModuleVectors E →ₗ[ℂ] CountableHilbertModuleSum B E :=
  Completion.toComplL.toLinearMap.comp (positiveModuleQuotientMk (B := B))

@[simp] theorem countableModuleMk_apply (x : CountableModuleVectors E) :
    countableModuleMk (B := B) x =
      ((positiveModuleQuotientMk (B := B) x) : CountableHilbertModuleSum B E) := rfl

theorem countableModuleMk_denseRange : DenseRange (countableModuleMk (B := B) (E := E)) :=
  Completion.denseRange_coe.comp positiveModuleQuotientMk_surjective.denseRange (Completion.continuous_coe _)

@[simp] theorem countableModuleMk_inner (x y : CountableModuleVectors E) :
    ⟪countableModuleMk (B := B) x, countableModuleMk (B := B) y⟫_(Bᵐᵒᵖ) =
      countableModuleFiniteInner (B := B) x y := by
  rw [countableModuleMk_apply, countableModuleMk_apply, completionInner_coe,
    PositiveModuleQuotient.inner_mk]
  rfl

@[simp] theorem countableModuleMk_norm (x : CountableModuleVectors E) :
    ‖countableModuleMk (B := B) x‖ = Real.sqrt ‖x.sum (fun i v => ⟪v, x i⟫_(Bᵐᵒᵖ))‖ := by
  rw [countableModuleMk_apply, Completion.norm_coe, PositiveModuleQuotient.norm_mk]
  rfl

@[simp] theorem countableModuleMk_op_smul (a : Bᵐᵒᵖ) (x : CountableModuleVectors E) :
    countableModuleMk (B := B) (a • x) = a • countableModuleMk (B := B) x := by
  rw [countableModuleMk_apply, countableModuleMk_apply, completion_op_smul_coe,
    PositiveModuleQuotient.op_smul_mk]

def countableModuleQuotientEvaluationLinear (i : ℕ) : CountableHilbertModulePreSum B E →ₗ[ℂ] E :=
  (PositiveModuleForm.nullRadical (B := B) (E := CountableModuleVectors E)).liftQ
    (Finsupp.lapply i) (fun x hx => by
      rw [countableModuleFinite_nullRadical_eq_bot, Submodule.mem_bot] at hx
      simp [hx])

@[simp] theorem countableModuleQuotientEvaluationLinear_mk (i : ℕ) (x : CountableModuleVectors E) :
    countableModuleQuotientEvaluationLinear (B := B) i (positiveModuleQuotientMk (B := B) x) = x i := rfl

def countableModuleQuotientEvaluationCLM (i : ℕ) : CountableHilbertModulePreSum B E →L[ℂ] E :=
  (countableModuleQuotientEvaluationLinear i).mkContinuous 1 (fun q => by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    simpa only [countableModuleQuotientEvaluationLinear_mk, PositiveModuleQuotient.norm_mk, one_mul]
      using countableModuleFinite_norm_coordinate_le x i)

def countableModuleQuotientInclusionCLM (i : ℕ) : E →L[ℂ] CountableHilbertModulePreSum B E :=
  ((positiveModuleQuotientMk (B := B)).comp (Finsupp.lsingle i)).mkContinuous 1
    (fun v => by
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, PositiveModuleQuotient.norm_mk,
        countableModuleFinite_formNorm_single, one_mul, le_refl])

def countableModuleQuotientInclusion (i : ℕ) :
    AdjointableMap B E (CountableHilbertModulePreSum B E) where
  toCLM := countableModuleQuotientInclusionCLM i
  adjointCLM := countableModuleQuotientEvaluationCLM i
  adjoint_identity v q := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    change ⟪positiveModuleQuotientMk (B := B) (Finsupp.single i v),
      positiveModuleQuotientMk (B := B) x⟫_(Bᵐᵒᵖ) = ⟪v, x i⟫_(Bᵐᵒᵖ)
    rw [PositiveModuleQuotient.inner_mk]
    exact countableModuleFiniteInner_single_left i v x

variable [CompleteSpace E]

/-- Inclusion in the complete countable sum, with the actual extended restriction adjoint. -/
def countableModuleInclusion (i : ℕ) : AdjointableMap B E (CountableHilbertModuleSum B E) where
  toCLM := Completion.toComplL.comp (countableModuleQuotientInclusion i).toCLM
  adjointCLM := (countableModuleQuotientInclusion i).adjointCLM.fromCompletion
  adjoint_identity v x := by
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp (continuous_const.prodMk continuous_id))
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk (countableModuleQuotientInclusion i).adjointCLM.fromCompletion.continuous))
    · intro q
      change ⟪(((countableModuleQuotientInclusion i).toCLM v : CountableHilbertModulePreSum B E) :
        CountableHilbertModuleSum B E), (q : CountableHilbertModuleSum B E)⟫_(Bᵐᵒᵖ) =
        ⟪v, (countableModuleQuotientInclusion i).adjointCLM.fromCompletion
          (q : CountableHilbertModuleSum B E)⟫_(Bᵐᵒᵖ)
      rw [completionInner_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      exact (countableModuleQuotientInclusion i).adjoint_identity v q

def countableModuleEvaluation (i : ℕ) : AdjointableMap B (CountableHilbertModuleSum B E) E :=
  (countableModuleInclusion i).adjoint

@[simp] theorem countableModuleInclusion_apply (i : ℕ) (v : E) :
    countableModuleInclusion (B := B) i v = countableModuleMk (B := B) (Finsupp.single i v) := rfl

@[simp] theorem countableModuleEvaluation_mk (i : ℕ) (x : CountableModuleVectors E) :
    countableModuleEvaluation (B := B) i (countableModuleMk (B := B) x) = x i := by
  rw [countableModuleMk_apply]
  change (countableModuleQuotientEvaluationCLM i).fromCompletion
    ((positiveModuleQuotientMk (B := B) x) : CountableHilbertModuleSum B E) = x i
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

@[simp] theorem countableModuleInclusion_norm (i : ℕ) (v : E) :
    ‖countableModuleInclusion (B := B) i v‖ = ‖v‖ := by
  rw [countableModuleInclusion_apply, countableModuleMk_apply, Completion.norm_coe,
    PositiveModuleQuotient.norm_mk, countableModuleFinite_formNorm_single]

theorem norm_countableModuleInclusion_le (i : ℕ) : ‖countableModuleInclusion (B := B) (E := E) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖countableModuleInclusion (B := B) i v‖ ≤ 1 * ‖v‖
  rw [countableModuleInclusion_norm, one_mul]

theorem norm_countableModuleEvaluation_le (i : ℕ) : ‖countableModuleEvaluation (B := B) (E := E) i‖ ≤ 1 := by
  change ‖(countableModuleInclusion (B := B) (E := E) i).adjoint.toCLM‖ ≤ 1
  rw [AdjointableMap.norm_adjoint_toCLM]
  exact norm_countableModuleInclusion_le i

/-- Pairing a finite vector with any actual sum uses its finitely many coordinates. -/
theorem countableModuleMk_inner_right (u : CountableModuleVectors E)
    (x : CountableHilbertModuleSum B E) :
    ⟪countableModuleMk (B := B) u, x⟫_(Bᵐᵒᵖ) =
      ∑ i ∈ u.support, ⟪u i, countableModuleEvaluation (B := B) i x⟫_(Bᵐᵒᵖ) := by
  classical
  have hu : countableModuleMk (B := B) u =
      ∑ i ∈ u.support, countableModuleInclusion (B := B) i (u i) := by
    simp only [countableModuleInclusion_apply, ← map_sum]
    exact congrArg (countableModuleMk (B := B)) u.sum_single.symm
  rw [hu, CStarModule.inner_sum_left (A := Bᵐᵒᵖ) (E := CountableHilbertModuleSum B E)]
  exact Finset.sum_congr rfl (fun i _ => (countableModuleInclusion (B := B) i).adjoint_identity _ _)

/-- Actual coordinate evaluations separate the completed countable sum. -/
theorem countableModule_ext_eval {x y : CountableHilbertModuleSum B E}
    (h : ∀ i : ℕ, countableModuleEvaluation (B := B) i x = countableModuleEvaluation (B := B) i y) :
    x = y := by
  apply module_inner_ext_right (B := B)
  have he := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    (CStarModule.continuous_inner.comp (continuous_id.prodMk (continuous_const (y := x))))
    (CStarModule.continuous_inner.comp (continuous_id.prodMk (continuous_const (y := y)))) (by
      funext u
      change ⟪countableModuleMk (B := B) u, x⟫_(Bᵐᵒᵖ) =
        ⟪countableModuleMk (B := B) u, y⟫_(Bᵐᵒᵖ)
      rw [countableModuleMk_inner_right, countableModuleMk_inner_right]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : E => ⟪u i, v⟫_(Bᵐᵒᵖ)) (h i)))
  intro z
  exact congrFun he z

end BC4lean.KKTheory
