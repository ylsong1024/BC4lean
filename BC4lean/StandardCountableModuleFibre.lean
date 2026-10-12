import BC4lean.StandardCountableReindex
import BC4lean.IntervalModuleFibre
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Evaluation of the genuine standard module

Evaluation is constructed on finite coefficient vectors with their actual
coefficient form. Its form bound permits descent and completion. Constant
coefficient vectors give a bounded right inverse, proved on the dense finite
vectors. The evaluated radical quotient completion is consequently identified
with H_B by an actual coefficient-inner-product unitary.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The interval coefficient algebra inherits separability from B through
the genuine topology of continuous maps on a compact metrizable interval. -/
theorem intervalCoefficient_separable [TopologicalSpace.SeparableSpace B] :
    TopologicalSpace.SeparableSpace C(unitInterval, B) := by infer_instance

/-- Actual evaluation of an opposite coefficient. -/
def standardCoefficientEvaluationLinear (t : X) : C(X, B)ᵐᵒᵖ →ₗ[ℂ] Bᵐᵒᵖ where
  toFun b := MulOpposite.op (MulOpposite.unop b t)
  map_add' b c := by simp
  map_smul' z b := by simp

/-- Actual constant opposite coefficients. -/
def standardCoefficientConstantLinear : Bᵐᵒᵖ →ₗ[ℂ] C(X, B)ᵐᵒᵖ where
  toFun b := MulOpposite.op (ContinuousMap.const X (MulOpposite.unop b))
  map_add' b c := by
    apply MulOpposite.unop_injective
    ext t
    simp
  map_smul' z b := by
    apply MulOpposite.unop_injective
    ext t
    simp

def standardFiniteCoefficientEvaluation (t : X) :
    StandardCountableVectors C(X, B) →ₗ[ℂ] StandardCountableVectors B :=
  Finsupp.mapRange.linearMap (standardCoefficientEvaluationLinear t)

def standardFiniteCoefficientConstant :
    StandardCountableVectors B →ₗ[ℂ] StandardCountableVectors C(X, B) :=
  Finsupp.mapRange.linearMap (standardCoefficientConstantLinear (X := X))

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem standardFiniteCoefficientEvaluation_apply (t : X)
    (x : StandardCountableVectors C(X, B)) (i : ℕ) :
    standardFiniteCoefficientEvaluation t x i = MulOpposite.op (MulOpposite.unop (x i) t) := rfl

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem standardFiniteCoefficientConstant_apply
    (x : StandardCountableVectors B) (i : ℕ) :
    standardFiniteCoefficientConstant (X := X) x i =
      MulOpposite.op (ContinuousMap.const X (MulOpposite.unop (x i))) := rfl

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem standardFiniteCoefficientEvaluation_constant (t : X)
    (x : StandardCountableVectors B) :
    standardFiniteCoefficientEvaluation t (standardFiniteCoefficientConstant x) = x := by
  ext i
  rfl

/-- Evaluation preserves the actual finite coefficient form, evaluated at t. -/
theorem standardFiniteCoefficientEvaluation_inner (t : X)
    (x y : StandardCountableVectors C(X, B)) :
    standardCountableFiniteInner (standardFiniteCoefficientEvaluation t x)
        (standardFiniteCoefficientEvaluation t y) =
      MulOpposite.op (MulOpposite.unop (standardCountableFiniteInner x y) t) := by
  classical
  have hsupport : (standardFiniteCoefficientEvaluation t x).support ⊆ x.support := by
    change (Finsupp.mapRange (standardCoefficientEvaluationLinear t)
      (map_zero (standardCoefficientEvaluationLinear t)) x).support ⊆ x.support
    exact Finsupp.support_mapRange
  apply MulOpposite.unop_injective
  rw [standardCountableFiniteInner_eq_sum _ _ x.support hsupport,
    standardCountableFiniteInner_unop]
  change MulOpposite.unop
    (∑ i ∈ x.support, MulOpposite.op (MulOpposite.unop (y i) t) *
      star (MulOpposite.op (MulOpposite.unop (x i) t))) = _
  simp only [Finset.unop_sum,
    MulOpposite.unop_op, MulOpposite.unop_mul, MulOpposite.unop_star,
    ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply]

/-- Constant coefficients preserve the finite inner form as a constant function. -/
theorem standardFiniteCoefficientConstant_inner (x y : StandardCountableVectors B) :
    standardCountableFiniteInner (standardFiniteCoefficientConstant (X := X) x)
        (standardFiniteCoefficientConstant y) =
      MulOpposite.op (ContinuousMap.const X (MulOpposite.unop (standardCountableFiniteInner x y))) := by
  apply MulOpposite.unop_injective
  ext t
  have h := congrArg MulOpposite.unop
    (standardFiniteCoefficientEvaluation_inner t
      (standardFiniteCoefficientConstant (X := X) x) (standardFiniteCoefficientConstant y))
  simpa only [standardFiniteCoefficientEvaluation_constant, MulOpposite.unop_op,
    ContinuousMap.const_apply] using h.symm

theorem standardFiniteCoefficientEvaluation_formNorm_le (t : X)
    (x : StandardCountableVectors C(X, B)) :
    PositiveModuleForm.formNorm (B := B) (standardFiniteCoefficientEvaluation t x) ≤
      1 * PositiveModuleForm.formNorm (B := C(X, B)) x := by
  rw [one_mul, PositiveModuleForm.formNorm, PositiveModuleForm.formNorm,
    standardCountableFinite_inner, standardCountableFinite_inner,
    standardFiniteCoefficientEvaluation_inner]
  apply Real.sqrt_le_sqrt
  simpa only [MulOpposite.norm_op, MulOpposite.norm_unop] using
    (MulOpposite.unop (standardCountableFiniteInner x x)).norm_coe_le_norm t

theorem standardFiniteCoefficientConstant_formNorm_le (x : StandardCountableVectors B) :
    PositiveModuleForm.formNorm (B := C(X, B)) (standardFiniteCoefficientConstant (X := X) x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  rw [one_mul, PositiveModuleForm.formNorm, PositiveModuleForm.formNorm,
    standardCountableFinite_inner, standardCountableFinite_inner,
    standardFiniteCoefficientConstant_inner]
  apply Real.sqrt_le_sqrt
  rw [MulOpposite.norm_op, ← MulOpposite.norm_unop (standardCountableFiniteInner x x)]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  exact le_rfl

/-- The actual completed evaluation, obtained from the form-bounded finite map. -/
def standardCountableCoefficientEvaluation (t : X) :
    StandardCountableHilbertModule C(X, B) →L[ℂ] StandardCountableHilbertModule B :=
  (positiveModuleQuotientLiftCLM (standardFiniteCoefficientEvaluation t)
    (standardFiniteCoefficientEvaluation_formNorm_le t)).completion

/-- Constant coefficients extend to a bounded map on the completed standard modules. -/
def standardCountableCoefficientConstant :
    StandardCountableHilbertModule B →L[ℂ] StandardCountableHilbertModule C(X, B) :=
  (positiveModuleQuotientLiftCLM (standardFiniteCoefficientConstant (X := X))
    standardFiniteCoefficientConstant_formNorm_le).completion

@[simp] theorem standardCountableCoefficientEvaluation_mk (t : X)
    (x : StandardCountableVectors C(X, B)) :
    standardCountableCoefficientEvaluation t (standardCountableMk x) =
      standardCountableMk (standardFiniteCoefficientEvaluation t x) := by
  rw [standardCountableMk_apply, standardCountableCoefficientEvaluation,
    ContinuousLinearMap.completion_apply_coe, positiveModuleQuotientLiftCLM_mk,
    standardCountableMk_apply]

@[simp] theorem standardCountableCoefficientConstant_mk (x : StandardCountableVectors B) :
    standardCountableCoefficientConstant (X := X) (standardCountableMk x) =
      standardCountableMk (standardFiniteCoefficientConstant x) := by
  rw [standardCountableMk_apply, standardCountableCoefficientConstant,
    ContinuousLinearMap.completion_apply_coe, positiveModuleQuotientLiftCLM_mk,
    standardCountableMk_apply]

theorem standardCountableCoefficientEvaluation_inner (t : X)
    (x y : StandardCountableHilbertModule C(X, B)) :
    ⟪standardCountableCoefficientEvaluation t x, standardCountableCoefficientEvaluation t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  have h (z : StandardCountableHilbertModule C(X, B) × StandardCountableHilbertModule C(X, B)) :
      ⟪standardCountableCoefficientEvaluation t z.1, standardCountableCoefficientEvaluation t z.2⟫_(Bᵐᵒᵖ) =
        MulOpposite.op (MulOpposite.unop ⟪z.1, z.2⟫_(C(X, B)ᵐᵒᵖ) t) := by
    refine ((standardCountableMk_denseRange (B := C(X, B))).prodMap
      (standardCountableMk_denseRange (B := C(X, B)))).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro v
      change ⟪standardCountableCoefficientEvaluation t (standardCountableMk v.1),
          standardCountableCoefficientEvaluation t (standardCountableMk v.2)⟫_(Bᵐᵒᵖ) =
        MulOpposite.op (MulOpposite.unop
          ⟪standardCountableMk v.1, standardCountableMk v.2⟫_(C(X, B)ᵐᵒᵖ) t)
      simpa only [standardCountableCoefficientEvaluation_mk, standardCountableMk_inner] using
        standardFiniteCoefficientEvaluation_inner t v.1 v.2
  exact h (x, y)

@[simp] theorem standardCountableCoefficientEvaluation_constant (t : X)
    (x : StandardCountableHilbertModule B) :
    standardCountableCoefficientEvaluation t (standardCountableCoefficientConstant x) = x := by
  refine (standardCountableMk_denseRange (B := B)).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_id
  · intro v
    simp only [standardCountableCoefficientConstant_mk, standardCountableCoefficientEvaluation_mk,
      standardFiniteCoefficientEvaluation_constant]

theorem standardCountableCoefficientEvaluation_surjective (t : X) :
    Function.Surjective (standardCountableCoefficientEvaluation (B := B) t) :=
  fun x => ⟨standardCountableCoefficientConstant x, standardCountableCoefficientEvaluation_constant t x⟩

/-- The genuine fibre of H_{C(X,B)} is H_B. Both the radical quotient and
the coefficient inner product are used in this construction. -/
def standardCountableModuleFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t)
      (StandardCountableHilbertModule B) :=
  hilbertModuleFibreEquivOfEvaluation t (standardCountableCoefficientEvaluation t)
    (standardCountableCoefficientEvaluation_inner t)
    (standardCountableCoefficientEvaluation_surjective t)

@[simp] theorem standardCountableModuleFibreEquiv_mk (t : X)
    (x : StandardCountableHilbertModule C(X, B)) :
    standardCountableModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t x) =
      standardCountableCoefficientEvaluation t x :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

@[simp] theorem standardCountableModuleFibreEquiv_finite_mk (t : X)
    (x : StandardCountableVectors C(X, B)) :
    standardCountableModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t (standardCountableMk x)) =
      standardCountableMk (standardFiniteCoefficientEvaluation t x) := by
  rw [standardCountableModuleFibreEquiv_mk, standardCountableCoefficientEvaluation_mk]

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
/-- Coefficient evaluation commutes with actual finite coordinate filtering. -/
@[simp] theorem standardFiniteCoefficientEvaluation_filter (t : X)
    (x : StandardCountableVectors C(X, B)) (n : ℕ) :
    standardFiniteCoefficientEvaluation t (x.filter (fun i => i < n)) =
      (standardFiniteCoefficientEvaluation t x).filter (fun i => i < n) := by
  ext i
  simp only [standardFiniteCoefficientEvaluation_apply, Finsupp.filter_apply]
  split_ifs <;> simp

theorem standardCountableCoefficientEvaluation_cutoff (t : X) (n : ℕ)
    (x : StandardCountableHilbertModule C(X, B)) :
    standardCountableCoefficientEvaluation t (standardCountableCutoff n x) =
      standardCountableCutoff n (standardCountableCoefficientEvaluation t x) := by
  refine (standardCountableMk_denseRange (B := C(X, B))).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [standardCountableCutoff_mk, standardCountableCoefficientEvaluation_mk,
      standardFiniteCoefficientEvaluation_filter]

/-- The actual fibre operator of a coordinate cutoff is the same cutoff on H_B. -/
theorem standardCountableModuleFibreEquiv_cutoff (t : X) (n : ℕ)
    (x : HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t) :
    standardCountableModuleFibreEquiv t
        (hilbertModuleFibreOperator t (standardCountableCutoff n) x) =
      standardCountableCutoff n (standardCountableModuleFibreEquiv t x) := by
  refine (hilbertModuleFibreMk_denseRange (B := B)
    (M := StandardCountableHilbertModule C(X, B)) t).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    rw [hilbertModuleFibreOperator_mk, standardCountableModuleFibreEquiv_mk,
      standardCountableModuleFibreEquiv_mk, standardCountableCoefficientEvaluation_cutoff]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardFiniteCoefficientEvaluation_restriction (t : X) (f : ℕ ↪ ℕ)
    (x : StandardCountableVectors C(X, B)) :
    standardFiniteCoefficientEvaluation t (standardCountableRestrictionLinear f x) =
      standardCountableRestrictionLinear f (standardFiniteCoefficientEvaluation t x) := by
  ext i
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardFiniteCoefficientEvaluation_embedding (t : X) (f : ℕ ↪ ℕ)
    (x : StandardCountableVectors C(X, B)) :
    standardFiniteCoefficientEvaluation t (standardCountableEmbeddingLinear f x) =
      standardCountableEmbeddingLinear f (standardFiniteCoefficientEvaluation t x) := by
  ext i
  by_cases hi : i ∈ Set.range f
  · obtain ⟨j, rfl⟩ := hi
    simp only [standardFiniteCoefficientEvaluation_apply, standardCountableEmbeddingLinear_apply,
      Finsupp.embDomain_apply_self]
  · simp [standardFiniteCoefficientEvaluation_apply, standardCountableEmbeddingLinear_apply,
      Finsupp.embDomain_of_notMem_range, hi]

theorem standardCountableCoefficientEvaluation_embedding (t : X) (f : ℕ ↪ ℕ)
    (x : StandardCountableHilbertModule C(X, B)) :
    standardCountableCoefficientEvaluation t (standardCountableEmbedding f x) =
      standardCountableEmbedding f (standardCountableCoefficientEvaluation t x) := by
  refine (standardCountableMk_denseRange (B := C(X, B))).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [standardCountableEmbedding_mk, standardCountableCoefficientEvaluation_mk,
      standardFiniteCoefficientEvaluation_embedding]

theorem standardCountableCoefficientEvaluation_embedding_adjoint (t : X) (f : ℕ ↪ ℕ)
    (x : StandardCountableHilbertModule C(X, B)) :
    standardCountableCoefficientEvaluation t ((standardCountableEmbedding f).adjoint x) =
      (standardCountableEmbedding f).adjoint (standardCountableCoefficientEvaluation t x) := by
  refine (standardCountableMk_denseRange (B := C(X, B))).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [standardCountableEmbedding_adjoint_mk, standardCountableCoefficientEvaluation_mk,
      standardFiniteCoefficientEvaluation_restriction]

theorem standardCountableModuleFibreEquiv_embedding (t : X) (f : ℕ ↪ ℕ)
    (x : HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t) :
    standardCountableModuleFibreEquiv t
        (hilbertModuleFibreOperator t (standardCountableEmbedding f) x) =
      standardCountableEmbedding f (standardCountableModuleFibreEquiv t x) := by
  refine (hilbertModuleFibreMk_denseRange (B := B)
    (M := StandardCountableHilbertModule C(X, B)) t).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    rw [hilbertModuleFibreOperator_mk, standardCountableModuleFibreEquiv_mk,
      standardCountableModuleFibreEquiv_mk, standardCountableCoefficientEvaluation_embedding]

end BC4lean.KKTheory
