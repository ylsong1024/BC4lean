import BC4lean.PositiveModuleQuotient
import BC4lean.HilbertModuleCompletion
import BC4lean.AdjointableCompletion
import BC4lean.StandardModuleOperator
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # The arbitrary-index Hilbert module for regular crossed products

Finite coefficient vectors carry their actual finite sum of coefficient-valued
inner products. The positive form is definite, proved by positivity of each
coordinate square. Its null radical is therefore zero. The norm on the radical
quotient is exactly the square root of the norm of that finite coefficient sum;
completing it gives the Hilbert module on an arbitrary index type Γ.
This uses neither an lp norm on B nor an assumed stabilization theorem. Coordinate inclusion and evaluation are proved adjoints.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {Γ : Type*} {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance : DecidableEq Γ := Classical.decEq Γ

/-- Finite coefficient vectors, without imposing an unrelated Banach-space norm. -/
abbrev ReducedCrossedVectors (B Γ : Type*) [Zero B] := Γ →₀ Bᵐᵒᵖ

/-- The actual coefficient-valued finite-vector form. -/
def reducedCrossedFiniteInner (x y : ReducedCrossedVectors B Γ) : Bᵐᵒᵖ :=
  x.sum fun i b => ⟪b, y i⟫_(Bᵐᵒᵖ)

/-- In the coefficient algebra itself, the form is exactly the usual sum x_i* y_i. -/
theorem reducedCrossedFiniteInner_unop (x y : ReducedCrossedVectors B Γ) :
    MulOpposite.unop (reducedCrossedFiniteInner x y) =
      ∑ i ∈ x.support, star (MulOpposite.unop (x i)) * MulOpposite.unop (y i) := by
  change MulOpposite.unop (∑ i ∈ x.support, y i * star (x i)) = _
  simp only [Finset.unop_sum, MulOpposite.unop_mul, MulOpposite.unop_star]

theorem reducedCrossedFiniteInner_eq_sum (x y : ReducedCrossedVectors B Γ) (s : Finset Γ)
    (h : x.support ⊆ s) :
    reducedCrossedFiniteInner x y = ∑ i ∈ s, ⟪x i, y i⟫_(Bᵐᵒᵖ) :=
  Finsupp.sum_of_support_subset x h _ (fun _ _ => CStarModule.inner_zero_left)

theorem reducedCrossedFiniteInner_star (x y : ReducedCrossedVectors B Γ) :
    star (reducedCrossedFiniteInner x y) = reducedCrossedFiniteInner y x := by
  rw [reducedCrossedFiniteInner_eq_sum x y (x.support ∪ y.support) Finset.subset_union_left,
    reducedCrossedFiniteInner_eq_sum y x (x.support ∪ y.support) Finset.subset_union_right,
    star_sum]
  exact Finset.sum_congr rfl fun i _ => CStarModule.star_inner (x i) (y i)

/-- All positive-form laws follow from the finite coefficient sum. -/
instance reducedCrossedFinitePositiveForm : PositiveModuleForm B (ReducedCrossedVectors B Γ) where
  inner := reducedCrossedFiniteInner
  inner_add_right := by
    intro x y z
    simp only [reducedCrossedFiniteInner, Finsupp.sum, Finsupp.add_apply,
      CStarModule.inner_add_right, Finset.sum_add_distrib]
  inner_self_nonneg := by
    intro x
    exact Finset.sum_nonneg (fun _ _ => CStarModule.inner_self_nonneg)
  inner_op_smul_right := by
    intro a x y
    simp only [reducedCrossedFiniteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_op_smul_right, Finset.mul_sum]
  inner_smul_right_complex := by
    intro c x y
    simp only [reducedCrossedFiniteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_smul_right_complex, Finset.smul_sum]
  star_inner := reducedCrossedFiniteInner_star

@[simp] theorem reducedCrossedFinite_inner (x y : ReducedCrossedVectors B Γ) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = reducedCrossedFiniteInner x y := rfl

/-- Each positive coordinate square is bounded by the entire finite square sum. -/
theorem reducedCrossedFinite_coordinate_inner_le (x : ReducedCrossedVectors B Γ) (i : Γ) :
    ⟪x i, x i⟫_(Bᵐᵒᵖ) ≤ reducedCrossedFiniteInner x x := by
  by_cases hi : i ∈ x.support
  · exact Finset.single_le_sum (fun _ _ => CStarModule.inner_self_nonneg) hi
  · have hz : x i = 0 := Finsupp.notMem_support_iff.mp hi
    simpa only [hz, CStarModule.inner_zero_left, reducedCrossedFinite_inner] using
      (PositiveModuleForm.inner_self_nonneg (B := B) (x := x))

/-- The finite-vector form is definite; zero inner square forces every coefficient to vanish. -/
theorem reducedCrossedFiniteInner_self_eq_zero_iff (x : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have hi : ⟪x i, x i⟫_(Bᵐᵒᵖ) = 0 := le_antisymm
      (hx ▸ reducedCrossedFinite_coordinate_inner_le x i) CStarModule.inner_self_nonneg
    exact CStarModule.inner_self.mp hi
  · rintro rfl
    simp [reducedCrossedFiniteInner]

/-- The radical is proved zero before the normed quotient is used. -/
theorem reducedCrossedFinite_nullRadical_eq_bot :
    PositiveModuleForm.nullRadical (B := B) (E := ReducedCrossedVectors B Γ) = ⊥ := by
  ext x
  rw [PositiveModuleForm.mem_nullRadical, reducedCrossedFinite_inner,
    reducedCrossedFiniteInner_self_eq_zero_iff, Submodule.mem_bot]

/-- Coordinate inclusion has the genuine coefficient inner-product adjoint law. -/
@[simp] theorem reducedCrossedFiniteInner_single_left (i : Γ) (b : Bᵐᵒᵖ)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner (Finsupp.single i b) x = ⟪b, x i⟫_(Bᵐᵒᵖ) := by
  simp [reducedCrossedFiniteInner]

theorem reducedCrossedFinite_formNorm_single (i : Γ) (b : Bᵐᵒᵖ) :
    PositiveModuleForm.formNorm (B := B) (Finsupp.single i b) = ‖b‖ := by
  rw [PositiveModuleForm.formNorm, reducedCrossedFinite_inner,
    reducedCrossedFiniteInner_single_left, Finsupp.single_eq_same]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) b).symm

theorem reducedCrossedFinite_norm_coordinate_le (x : ReducedCrossedVectors B Γ) (i : Γ) :
    ‖x i‖ ≤ PositiveModuleForm.formNorm (B := B) x := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x i), PositiveModuleForm.formNorm]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le CStarModule.inner_self_nonneg
    (reducedCrossedFinite_coordinate_inner_le x i)

/-- The finite vectors with the actual form-derived Hilbert norm. -/
abbrev ReducedCrossedPreModule (B Γ : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] := PositiveModuleQuotient B (ReducedCrossedVectors B Γ)

theorem reducedCrossedPreMk_injective :
    Function.Injective (positiveModuleQuotientMk (B := B) (E := ReducedCrossedVectors B Γ)) := by
  intro x y h
  have hr := (PositiveModuleQuotient.mk_eq_mk x y).mp h
  rw [reducedCrossedFinite_nullRadical_eq_bot, Submodule.mem_bot] at hr
  exact sub_eq_zero.mp hr

/-- The arbitrary-index Hilbert module is the completion of the actual finite coefficient-inner-product norm. -/
abbrev ReducedCrossedHilbertModule (B Γ : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] := Completion (ReducedCrossedPreModule B Γ)

/-- The canonical finite-vector map to the completed module. -/
def reducedCrossedMk : ReducedCrossedVectors B Γ →ₗ[ℂ] ReducedCrossedHilbertModule B Γ :=
  Completion.toComplL.toLinearMap.comp (positiveModuleQuotientMk (B := B))

@[simp] theorem reducedCrossedMk_apply (x : ReducedCrossedVectors B Γ) :
    reducedCrossedMk x = ((positiveModuleQuotientMk (B := B) x) : ReducedCrossedHilbertModule B Γ) := rfl

theorem reducedCrossedMk_injective : Function.Injective (reducedCrossedMk (B := B) (Γ := Γ)) :=
  (Completion.coe_injective _).comp reducedCrossedPreMk_injective

/-- Finite coefficient vectors have genuinely dense canonical image in the completed module. -/
theorem reducedCrossedMk_denseRange : DenseRange (reducedCrossedMk (B := B) (Γ := Γ)) :=
  Completion.denseRange_coe.comp positiveModuleQuotientMk_surjective.denseRange (Completion.continuous_coe _)

@[simp] theorem reducedCrossedMk_inner (x y : ReducedCrossedVectors B Γ) :
    ⟪reducedCrossedMk x, reducedCrossedMk y⟫_(Bᵐᵒᵖ) = reducedCrossedFiniteInner x y := by
  rw [reducedCrossedMk_apply, reducedCrossedMk_apply, completionInner_coe,
    PositiveModuleQuotient.inner_mk]
  rfl

/-- The canonical finite-vector norm is the square root of the actual coefficient sum. -/
@[simp] theorem reducedCrossedMk_norm (x : ReducedCrossedVectors B Γ) :
    ‖reducedCrossedMk x‖ = Real.sqrt ‖x.sum (fun i b => ⟪b, x i⟫_(Bᵐᵒᵖ))‖ := by
  rw [reducedCrossedMk_apply, Completion.norm_coe, PositiveModuleQuotient.norm_mk]
  rfl

/-- The completed module norm uses the norm of the sum of positive coefficient squares. -/
theorem reducedCrossedMk_norm_coefficients (x : ReducedCrossedVectors B Γ) :
    ‖reducedCrossedMk x‖ =
      Real.sqrt ‖∑ i ∈ x.support, star (MulOpposite.unop (x i)) * MulOpposite.unop (x i)‖ := by
  rw [reducedCrossedMk_norm]
  change Real.sqrt ‖reducedCrossedFiniteInner x x‖ = _
  rw [← MulOpposite.norm_unop (reducedCrossedFiniteInner x x), reducedCrossedFiniteInner_unop]

@[simp] theorem reducedCrossedMk_op_smul (a : Bᵐᵒᵖ) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedMk (a • x) = a • reducedCrossedMk x := by
  rw [reducedCrossedMk_apply, reducedCrossedMk_apply, completion_op_smul_coe,
    PositiveModuleQuotient.op_smul_mk]

/-- Evaluation descends because the finite-vector radical is proved zero. -/
def reducedCrossedQuotientEvaluationLinear (i : Γ) : ReducedCrossedPreModule B Γ →ₗ[ℂ] Bᵐᵒᵖ :=
  (PositiveModuleForm.nullRadical (B := B) (E := ReducedCrossedVectors B Γ)).liftQ
    (Finsupp.lapply i) (fun x hx => by
      rw [reducedCrossedFinite_nullRadical_eq_bot, Submodule.mem_bot] at hx
      simp [hx])

@[simp] theorem reducedCrossedQuotientEvaluationLinear_mk (i : Γ) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedQuotientEvaluationLinear i (positiveModuleQuotientMk (B := B) x) = x i := rfl

def reducedCrossedQuotientEvaluationCLM (i : Γ) : ReducedCrossedPreModule B Γ →L[ℂ] Bᵐᵒᵖ :=
  (reducedCrossedQuotientEvaluationLinear i).mkContinuous 1 (fun q => by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    simpa only [reducedCrossedQuotientEvaluationLinear_mk, PositiveModuleQuotient.norm_mk, one_mul]
      using reducedCrossedFinite_norm_coordinate_le x i)

def reducedCrossedQuotientInclusionCLM (i : Γ) : Bᵐᵒᵖ →L[ℂ] ReducedCrossedPreModule B Γ :=
  ((positiveModuleQuotientMk (B := B)).comp (Finsupp.lsingle i)).mkContinuous 1
    (fun b => by
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, PositiveModuleQuotient.norm_mk,
        reducedCrossedFinite_formNorm_single, one_mul, le_refl])

/-- Coordinate inclusion and evaluation on the normed finite-vector module are adjoints. -/
def reducedCrossedQuotientInclusion (i : Γ) :
    AdjointableMap B Bᵐᵒᵖ (ReducedCrossedPreModule B Γ) where
  toCLM := reducedCrossedQuotientInclusionCLM i
  adjointCLM := reducedCrossedQuotientEvaluationCLM (B := B) i
  adjoint_identity b q := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    change ⟪positiveModuleQuotientMk (B := B) (Finsupp.single i b),
      positiveModuleQuotientMk (B := B) x⟫_(Bᵐᵒᵖ) = ⟪b, x i⟫_(Bᵐᵒᵖ)
    rw [PositiveModuleQuotient.inner_mk]
    exact reducedCrossedFiniteInner_single_left i b x

/-- The complete-module coordinate inclusion, with its adjoint extended into complete B. -/
def reducedCrossedInclusion (i : Γ) : AdjointableMap B Bᵐᵒᵖ (ReducedCrossedHilbertModule B Γ) where
  toCLM := Completion.toComplL.comp (reducedCrossedQuotientInclusion (B := B) i).toCLM
  adjointCLM := (reducedCrossedQuotientInclusion (B := B) i).adjointCLM.fromCompletion
  adjoint_identity b x := by
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp (continuous_const.prodMk continuous_id))
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk (reducedCrossedQuotientInclusion (B := B) i).adjointCLM.fromCompletion.continuous))
    · intro q
      change ⟪(((reducedCrossedQuotientInclusion (B := B) i).toCLM b : ReducedCrossedPreModule B Γ) :
        ReducedCrossedHilbertModule B Γ), (q : ReducedCrossedHilbertModule B Γ)⟫_(Bᵐᵒᵖ) =
        ⟪b, (reducedCrossedQuotientInclusion (B := B) i).adjointCLM.fromCompletion
          (q : ReducedCrossedHilbertModule B Γ)⟫_(Bᵐᵒᵖ)
      rw [completionInner_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      exact (reducedCrossedQuotientInclusion (B := B) i).adjoint_identity b q

/-- Actual coordinate evaluation is the proved coordinate inclusion adjoint. -/
def reducedCrossedEvaluation (i : Γ) : AdjointableMap B (ReducedCrossedHilbertModule B Γ) Bᵐᵒᵖ :=
  (reducedCrossedInclusion (B := B) i).adjoint

@[simp] theorem reducedCrossedInclusion_apply (i : Γ) (b : Bᵐᵒᵖ) :
    reducedCrossedInclusion i b = reducedCrossedMk (Finsupp.single i b) := rfl

@[simp] theorem reducedCrossedEvaluation_mk (i : Γ) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedEvaluation i (reducedCrossedMk x) = x i := by
  rw [reducedCrossedMk_apply]
  change (reducedCrossedQuotientEvaluationCLM (B := B) i).fromCompletion
    ((positiveModuleQuotientMk (B := B) x) : ReducedCrossedHilbertModule B Γ) = x i
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

@[simp] theorem reducedCrossedInclusion_norm (i : Γ) (b : Bᵐᵒᵖ) :
    ‖reducedCrossedInclusion i b‖ = ‖b‖ := by
  rw [reducedCrossedInclusion_apply, reducedCrossedMk_apply, Completion.norm_coe,
    PositiveModuleQuotient.norm_mk, reducedCrossedFinite_formNorm_single]

theorem norm_reducedCrossedInclusion_le (i : Γ) : ‖reducedCrossedInclusion (B := B) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b
  change ‖reducedCrossedInclusion (B := B) i b‖ ≤ 1 * ‖b‖
  rw [reducedCrossedInclusion_norm, one_mul]

theorem norm_reducedCrossedEvaluation_le (i : Γ) : ‖reducedCrossedEvaluation (B := B) i‖ ≤ 1 := by
  change ‖(reducedCrossedInclusion (B := B) i).adjoint.toCLM‖ ≤ 1
  rw [AdjointableMap.norm_adjoint_toCLM]
  exact norm_reducedCrossedInclusion_le i


/-- The coordinate inclusion and evaluation have the expected delta pairing. -/
@[simp] theorem reducedCrossedEvaluation_inclusion (i j : Γ) (b : Bᵐᵒᵖ) :
    reducedCrossedEvaluation i (reducedCrossedInclusion j b) =
      if j = i then b else 0 := by
  rw [reducedCrossedInclusion_apply, reducedCrossedEvaluation_mk]
  exact Finsupp.single_apply

/-- Equality on canonical finite coefficient vectors determines an adjointable map. -/
theorem reducedCrossed_adjointable_ext_mk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E]
    (S T : AdjointableMap B (ReducedCrossedHilbertModule B Γ) E)
    (h : ∀ x : ReducedCrossedVectors B Γ, S (reducedCrossedMk x) = T (reducedCrossedMk x)) :
    S = T := by
  apply AdjointableMap.ext
  intro x
  exact congrFun (reducedCrossedMk_denseRange.equalizer
    S.toCLM.continuous T.toCLM.continuous (funext h)) x


/-- Inject the actual finite coefficient coordinates. -/
def reducedCrossedEmbeddingLinear (f : Γ ↪ Γ) :
    ReducedCrossedVectors B Γ →ₗ[ℂ] ReducedCrossedVectors B Γ :=
  Finsupp.lmapDomain Bᵐᵒᵖ ℂ f

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem reducedCrossedEmbeddingLinear_apply (f : Γ ↪ Γ)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedEmbeddingLinear f x = x.embDomain f :=
  (Finsupp.embDomain_eq_mapDomain f x).symm

/-- Restrict the actual finite coefficient coordinates along an injection. -/
def reducedCrossedRestrictionLinear (f : Γ ↪ Γ) :
    ReducedCrossedVectors B Γ →ₗ[ℂ] ReducedCrossedVectors B Γ :=
  Finsupp.lcomapDomain f f.injective

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem reducedCrossedRestrictionLinear_apply (f : Γ ↪ Γ)
    (x : ReducedCrossedVectors B Γ) (n : Γ) :
    reducedCrossedRestrictionLinear f x n = x (f n) := rfl

/-- The finite coordinate maps satisfy the genuine coefficient adjoint identity. -/
theorem reducedCrossedFiniteEmbedding_inner (f : Γ ↪ Γ)
    (x y : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner (reducedCrossedEmbeddingLinear f x) y =
      reducedCrossedFiniteInner x (reducedCrossedRestrictionLinear f y) := by
  simp only [reducedCrossedEmbeddingLinear_apply, reducedCrossedFiniteInner,
    Finsupp.sum_embDomain, reducedCrossedRestrictionLinear_apply]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem reducedCrossedRestriction_embedding (f : Γ ↪ Γ)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedRestrictionLinear f (reducedCrossedEmbeddingLinear f x) = x := by
  ext n
  simp only [reducedCrossedRestrictionLinear_apply, reducedCrossedEmbeddingLinear_apply,
    Finsupp.embDomain_apply_self]

theorem reducedCrossedFiniteEmbedding_inner_map (f : Γ ↪ Γ)
    (x y : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner (reducedCrossedEmbeddingLinear f x)
      (reducedCrossedEmbeddingLinear f y) = reducedCrossedFiniteInner x y := by
  rw [reducedCrossedFiniteEmbedding_inner, reducedCrossedRestriction_embedding]

/-- Coordinate injection is isometric for the actual finite-vector form norm. -/
theorem reducedCrossedEmbedding_formNorm (f : Γ ↪ Γ) (x : ReducedCrossedVectors B Γ) :
    PositiveModuleForm.formNorm (B := B) (reducedCrossedEmbeddingLinear f x) =
      PositiveModuleForm.formNorm (B := B) x := by
  simp only [PositiveModuleForm.formNorm, reducedCrossedFinite_inner,
    reducedCrossedFiniteEmbedding_inner_map]

/-- Restriction is contractive by the genuine form Cauchy--Schwarz inequality. -/
theorem reducedCrossedRestriction_formNorm_le (f : Γ ↪ Γ) (x : ReducedCrossedVectors B Γ) :
    PositiveModuleForm.formNorm (B := B) (reducedCrossedRestrictionLinear f x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  rw [one_mul]
  let y := reducedCrossedRestrictionLinear f x
  have hsq : (PositiveModuleForm.formNorm (B := B) y) ^ 2 ≤
      PositiveModuleForm.formNorm (B := B) y * PositiveModuleForm.formNorm (B := B) x := by
    rw [PositiveModuleForm.formNorm_sq]
    change ‖reducedCrossedFiniteInner y y‖ ≤ _
    rw [← reducedCrossedFiniteEmbedding_inner f y x]
    simpa only [reducedCrossedFinite_inner, reducedCrossedEmbedding_formNorm]
      using PositiveModuleForm.norm_inner_le (B := B) (reducedCrossedEmbeddingLinear f y) x
  by_contra h
  have hlt : PositiveModuleForm.formNorm (B := B) x < PositiveModuleForm.formNorm (B := B) y :=
    lt_of_not_ge h
  have hy : 0 < PositiveModuleForm.formNorm (B := B) y :=
    lt_of_le_of_lt (PositiveModuleForm.formNorm_nonneg x) hlt
  have hm := mul_lt_mul_of_pos_left hlt hy
  rw [← pow_two] at hm
  exact not_lt_of_ge hsq hm

/-- Coordinate inclusion and restriction on the normed finite-vector quotient. -/
def reducedCrossedQuotientEmbedding (f : Γ ↪ Γ) :
    AdjointableMap B (ReducedCrossedPreModule B Γ) (ReducedCrossedPreModule B Γ) where
  toCLM := positiveModuleQuotientLiftCLM (reducedCrossedEmbeddingLinear f) (K := 1)
    (fun x => by rw [reducedCrossedEmbedding_formNorm]; simp only [one_mul, le_refl])
  adjointCLM := positiveModuleQuotientLiftCLM (reducedCrossedRestrictionLinear f)
    (reducedCrossedRestriction_formNorm_le f)
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    exact reducedCrossedFiniteEmbedding_inner f x y

/-- The actual completed coordinate embedding, with the proved restriction adjoint. -/
def reducedCrossedEmbedding (f : Γ ↪ Γ) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  (reducedCrossedQuotientEmbedding f).completion

@[simp] theorem reducedCrossedEmbedding_mk (f : Γ ↪ Γ) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedEmbedding f (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedEmbeddingLinear f x) := by
  rw [reducedCrossedMk_apply, reducedCrossedEmbedding, AdjointableMap.completion_apply_coe,
    reducedCrossedMk_apply]
  rfl

@[simp] theorem reducedCrossedEmbedding_adjoint_mk (f : Γ ↪ Γ) (x : ReducedCrossedVectors B Γ) :
    (reducedCrossedEmbedding f).adjoint (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedRestrictionLinear f x) := by
  rw [reducedCrossedMk_apply, reducedCrossedEmbedding, AdjointableMap.completion_adjoint,
    AdjointableMap.completion_apply_coe, reducedCrossedMk_apply]
  rfl

@[simp] theorem reducedCrossedEmbedding_adjoint_comp_self (f : Γ ↪ Γ) :
    (reducedCrossedEmbedding (B := B) f).adjoint.comp (reducedCrossedEmbedding f) =
      AdjointableMap.id := by
  apply reducedCrossed_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.comp_apply, reducedCrossedEmbedding_mk,
    reducedCrossedEmbedding_adjoint_mk, reducedCrossedRestriction_embedding,
    AdjointableMap.id_apply]

/-- The completed coordinate map preserves the actual coefficient-valued inner product. -/
theorem reducedCrossedEmbedding_inner (f : Γ ↪ Γ) (x y : ReducedCrossedHilbertModule B Γ) :
    ⟪reducedCrossedEmbedding f x, reducedCrossedEmbedding f y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(reducedCrossedEmbedding (B := B) f).adjoint_identity]
  change ⟪x, (reducedCrossedEmbedding f).adjoint (reducedCrossedEmbedding f y)⟫_(Bᵐᵒᵖ) = _
  have h := congrArg (fun T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
    (ReducedCrossedHilbertModule B Γ) => T y) (reducedCrossedEmbedding_adjoint_comp_self f)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg
    (fun z : ReducedCrossedHilbertModule B Γ => ⟪x, z⟫_(Bᵐᵒᵖ)) h

@[simp] theorem reducedCrossedEmbedding_norm (f : Γ ↪ Γ) (x : ReducedCrossedHilbertModule B Γ) :
    ‖reducedCrossedEmbedding f x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (reducedCrossedEmbedding f x),
    reducedCrossedEmbedding_inner]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

theorem norm_reducedCrossedEmbedding_le (f : Γ ↪ Γ) :
    ‖reducedCrossedEmbedding (B := B) f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖reducedCrossedEmbedding (B := B) f x‖ ≤ 1 * ‖x‖
  rw [reducedCrossedEmbedding_norm, one_mul]

/-- Evaluation in an injected coordinate recovers the actual original coefficient. -/
@[simp] theorem reducedCrossedEvaluation_embedding (f : Γ ↪ Γ)
    (x : ReducedCrossedHilbertModule B Γ) (n : Γ) :
    reducedCrossedEvaluation (f n) (reducedCrossedEmbedding f x) =
      reducedCrossedEvaluation n x := by
  have h := (reducedCrossedMk_denseRange (B := B)).equalizer
    ((reducedCrossedEvaluation (B := B) (f n)).toCLM.continuous.comp
      (reducedCrossedEmbedding (B := B) f).toCLM.continuous)
    (reducedCrossedEvaluation (B := B) n).toCLM.continuous (by
      funext y
      simp only [Function.comp_def, reducedCrossedEmbedding_mk, reducedCrossedEvaluation_mk,
        reducedCrossedEmbeddingLinear_apply, Finsupp.embDomain_apply_self])
  exact congrFun h x


/-- A permutation of the arbitrary coordinate set gives an actual adjointable isometry. -/
def reducedCrossedReindex (e : Γ ≃ Γ) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  reducedCrossedEmbedding e.toEmbedding

@[simp] theorem reducedCrossedReindex_mk (e : Γ ≃ Γ) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedReindex e (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedEmbeddingLinear e.toEmbedding x) :=
  reducedCrossedEmbedding_mk e.toEmbedding x

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem reducedCrossedEmbeddingLinear_equiv_apply (e : Γ ≃ Γ)
    (x : ReducedCrossedVectors B Γ) (i : Γ) :
    reducedCrossedEmbeddingLinear e.toEmbedding x i = x (e.symm i) := by
  simpa only [reducedCrossedEmbeddingLinear_apply, Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply] using Finsupp.embDomain_apply_self e.toEmbedding x (e.symm i)

@[simp] theorem reducedCrossedReindex_adjoint_mk (e : Γ ≃ Γ)
    (x : ReducedCrossedVectors B Γ) :
    (reducedCrossedReindex e).adjoint (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedEmbeddingLinear e.symm.toEmbedding x) := by
  rw [reducedCrossedReindex, reducedCrossedEmbedding_adjoint_mk]
  congr 1
  ext i
  simp only [reducedCrossedRestrictionLinear_apply,
    reducedCrossedEmbeddingLinear_equiv_apply, Equiv.symm_symm, Equiv.toEmbedding_apply]

/-- Reversing a coordinate permutation is exactly its Hilbert-module adjoint. -/
@[simp] theorem reducedCrossedReindex_adjoint (e : Γ ≃ Γ) :
    (reducedCrossedReindex (B := B) e).adjoint = reducedCrossedReindex e.symm := by
  apply reducedCrossed_adjointable_ext_mk
  intro x
  rw [reducedCrossedReindex_adjoint_mk, reducedCrossedReindex_mk]

@[simp] theorem reducedCrossedReindex_adjoint_comp_self (e : Γ ≃ Γ) :
    (reducedCrossedReindex (B := B) e).adjoint.comp (reducedCrossedReindex e) =
      AdjointableMap.id := reducedCrossedEmbedding_adjoint_comp_self e.toEmbedding

@[simp] theorem reducedCrossedReindex_comp_adjoint (e : Γ ≃ Γ) :
    (reducedCrossedReindex (B := B) e).comp (reducedCrossedReindex e).adjoint =
      AdjointableMap.id := by
  have h := reducedCrossedReindex_adjoint_comp_self (B := B) e.symm
  simpa only [reducedCrossedReindex_adjoint, Equiv.symm_symm] using h

/-- Coordinate permutations preserve the actual coefficient-valued inner product. -/
theorem reducedCrossedReindex_inner (e : Γ ≃ Γ)
    (x y : ReducedCrossedHilbertModule B Γ) :
    ⟪reducedCrossedReindex e x, reducedCrossedReindex e y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) :=
  reducedCrossedEmbedding_inner e.toEmbedding x y

@[simp] theorem reducedCrossedReindex_norm (e : Γ ≃ Γ)
    (x : ReducedCrossedHilbertModule B Γ) : ‖reducedCrossedReindex e x‖ = ‖x‖ :=
  reducedCrossedEmbedding_norm e.toEmbedding x

@[simp] theorem reducedCrossedEvaluation_reindex (e : Γ ≃ Γ)
    (x : ReducedCrossedHilbertModule B Γ) (i : Γ) :
    reducedCrossedEvaluation i (reducedCrossedReindex e x) =
      reducedCrossedEvaluation (e.symm i) x := by
  simpa only [reducedCrossedReindex, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
    using reducedCrossedEvaluation_embedding e.toEmbedding x (e.symm i)

end BC4lean.KKTheory
