import BC4lean.IntervalHilbertModule
import BC4lean.PositiveModuleForm
import BC4lean.PositiveModuleQuotient
import BC4lean.AdjointableCompletion
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Fibres of arbitrary interval-coefficient Hilbert modules

For an arbitrary Hilbert `C(X,B)`-module, evaluation of its coefficient-valued
inner product gives a positive semidefinite `B`-valued form. Its radical must
be removed and the resulting Hilbert-module norm completed. The construction
does not assume that this norm equals an ambient Banach-space quotient norm;
that equality is proved separately for compact Hausdorff parameter spaces.

The operator estimate is proved in the coefficient order before evaluation.
It uses the positive square root of `‖T‖² 1 - T* T` in the actual C⋆-algebra
of adjointable endomorphisms. Thus evaluation yields a bounded map on the
genuine fibre norm rather than an additional operator-bound hypothesis.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open UniformSpace

/-- The vector space underlying a module, carrying the form evaluated at `t`.
This type has no inherited norm: the evaluated form can have null vectors. -/
def EvaluatedModuleSpace (_B M : Type*) {X : Type*} (_t : X) := M

section EvaluatedVectorSpace

variable {B X M : Type*} [AddCommGroup M] [Module ℂ M]

instance evaluatedModuleAddCommGroup (t : X) :
    AddCommGroup (EvaluatedModuleSpace B M t) := inferInstanceAs (AddCommGroup M)

instance evaluatedModuleComplexModule (t : X) :
    Module ℂ (EvaluatedModuleSpace B M t) := inferInstanceAs (Module ℂ M)

/-- The underlying vector-space identification, without a norm identification. -/
def evaluatedModuleLinearEquiv (t : X) : EvaluatedModuleSpace B M t ≃ₗ[ℂ] M :=
  LinearEquiv.refl ℂ M

/-- Typed conversion to the original vector space. -/
def evaluatedModuleToOriginal (t : X) (x : EvaluatedModuleSpace B M t) : M :=
  evaluatedModuleLinearEquiv t x

/-- Typed conversion to the vector space with its evaluated form. -/
def evaluatedModuleOfOriginal (B : Type*) (t : X) (x : M) :
    EvaluatedModuleSpace B M t := (evaluatedModuleLinearEquiv t).symm x

@[simp] theorem evaluatedModule_to_of (t : X) (x : M) :
    evaluatedModuleToOriginal t (evaluatedModuleOfOriginal B t x) = x := rfl

@[simp] theorem evaluatedModule_of_to (t : X) (x : EvaluatedModuleSpace B M t) :
    evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t x) = x := rfl

@[simp] theorem evaluatedModuleLinearEquiv_apply (t : X) (x : EvaluatedModuleSpace B M t) :
    evaluatedModuleLinearEquiv t x = evaluatedModuleToOriginal t x := rfl

end EvaluatedVectorSpace

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M]

/-- Restrict the coefficient action along the constant-function homomorphism. -/
instance evaluatedModuleSMul (t : X) : SMul Bᵐᵒᵖ (EvaluatedModuleSpace B M t) where
  smul b x := evaluatedModuleOfOriginal B t
    (MulOpposite.op (ContinuousMap.const X (MulOpposite.unop b)) • evaluatedModuleToOriginal t x)

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] [CStarModule C(X, B)ᵐᵒᵖ M] in
@[simp] theorem evaluatedModule_smul_apply (t : X) (b : Bᵐᵒᵖ)
    (x : EvaluatedModuleSpace B M t) :
    evaluatedModuleLinearEquiv t (b • x) =
      MulOpposite.op (ContinuousMap.const X (MulOpposite.unop b)) •
        evaluatedModuleLinearEquiv t x := rfl

/-- Evaluation of the actual continuous-coefficient inner product. -/
def evaluatedModuleInner (t : X) (x y : EvaluatedModuleSpace B M t) : Bᵐᵒᵖ :=
  MulOpposite.op (MulOpposite.unop ⟪(evaluatedModuleToOriginal t x), (evaluatedModuleToOriginal t y)⟫_(C(X, B)ᵐᵒᵖ) t)

/-- Evaluation preserves positivity and all algebraic inner-product laws.
It need not preserve definiteness; its null vectors are quotiented later. -/
instance evaluatedModulePositiveForm (t : X) :
    PositiveModuleForm B (EvaluatedModuleSpace B M t) where
  inner := evaluatedModuleInner t
  inner_add_right := by
    intro x y z
    exact congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
      (CStarModule.inner_add_right (x := (evaluatedModuleToOriginal t x)) (y := (evaluatedModuleToOriginal t y)) (z := (evaluatedModuleToOriginal t z)))
  inner_self_nonneg := by
    intro x
    exact (CStarModule.inner_self_nonneg (A := C(X, B)ᵐᵒᵖ) (x := (evaluatedModuleToOriginal t x))) t
  inner_op_smul_right := by
    intro b x y
    exact congrArg (fun c : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop c t))
      (CStarModule.inner_op_smul_right
        (a := MulOpposite.op (ContinuousMap.const X (MulOpposite.unop b)))
        (x := (evaluatedModuleToOriginal t x)) (y := (evaluatedModuleToOriginal t y)))
  inner_smul_right_complex := by
    intro c x y
    exact congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
      (CStarModule.inner_smul_right_complex (z := c) (x := (evaluatedModuleToOriginal t x)) (y := (evaluatedModuleToOriginal t y)))
  star_inner x y :=
    congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
      (CStarModule.star_inner (evaluatedModuleToOriginal t x) (evaluatedModuleToOriginal t y))

omit [StarOrderedRing B] in
@[simp] theorem evaluatedModule_inner (t : X) (x y : EvaluatedModuleSpace B M t) :
    ⟪x, y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪(evaluatedModuleToOriginal t x), (evaluatedModuleToOriginal t y)⟫_(C(X, B)ᵐᵒᵖ) t) := rfl

omit [StarOrderedRing B] in
/-- The evaluated length is contractive for the original Hilbert-module norm. -/
theorem evaluatedModule_formNorm_le (t : X) (x : EvaluatedModuleSpace B M t) :
    PositiveModuleForm.formNorm (B := B) x ≤ ‖(evaluatedModuleToOriginal t x)‖ := by
  change Real.sqrt ‖MulOpposite.unop ⟪(evaluatedModuleToOriginal t x), (evaluatedModuleToOriginal t x)⟫_(C(X, B)ᵐᵒᵖ) t‖ ≤ _
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := C(X, B)ᵐᵒᵖ)
    (evaluatedModuleToOriginal t x)]
  exact Real.sqrt_le_sqrt
    ((MulOpposite.unop ⟪(evaluatedModuleToOriginal t x), (evaluatedModuleToOriginal t x)⟫_(C(X, B)ᵐᵒᵖ)).norm_coe_le_norm t)

omit [StarOrderedRing B] in
/-- Variable coefficients evaluate to their actual value on the semidefinite
form. This law is needed when transporting countable generators and rank ones. -/
theorem evaluatedModule_inner_variable_smul_left (t : X) (b : C(X, B)ᵐᵒᵖ)
    (x y : EvaluatedModuleSpace B M t) :
    evaluatedModuleInner t (evaluatedModuleOfOriginal B t (b • evaluatedModuleToOriginal t x)) y =
      evaluatedModuleInner t x y * star (MulOpposite.op (MulOpposite.unop b t)) := by
  exact congrArg (fun c : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop c t))
    (CStarModule.inner_op_smul_left (a := b) (x := (evaluatedModuleToOriginal t x)) (y := (evaluatedModuleToOriginal t y)))

omit [StarOrderedRing B] in
/-- A variable coefficient and its evaluated constant coefficient have the
same class in the actual radical quotient. -/
theorem evaluatedModule_variable_smul_sub_mem_nullRadical (t : X)
    (b : C(X, B)ᵐᵒᵖ) (x : EvaluatedModuleSpace B M t) :
    (evaluatedModuleOfOriginal B t (b • evaluatedModuleToOriginal t x)) -
        MulOpposite.op (MulOpposite.unop b t) • x ∈
      PositiveModuleForm.nullRadical (B := B) (E := EvaluatedModuleSpace B M t) := by
  change ∀ y, ⟪(evaluatedModuleOfOriginal B t (b • evaluatedModuleToOriginal t x)) -
    MulOpposite.op (MulOpposite.unop b t) • x, y⟫_(Bᵐᵒᵖ) = 0
  intro y
  rw [PositiveModuleForm.inner_sub_left, PositiveModuleForm.inner_op_smul_left]
  change evaluatedModuleInner t (evaluatedModuleOfOriginal B t (b • evaluatedModuleToOriginal t x)) y -
    evaluatedModuleInner t x y * star (MulOpposite.op (MulOpposite.unop b t)) = 0
  rw [evaluatedModule_inner_variable_smul_left, sub_self]

namespace AdjointableMap

variable {D E : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Dᵐᵒᵖ E] [CStarModule Dᵐᵒᵖ E]
  [CompleteSpace E]

/-- The C⋆-valued operator bound, proved using an actual positive square root
in the adjointable endomorphism algebra. -/
theorem inner_self_apply_le_norm_sq_smul (T : AdjointableMap D E E) (x : E) :
    ⟪T x, T x⟫_(Dᵐᵒᵖ) ≤ ‖T‖ ^ 2 • ⟪x, x⟫_(Dᵐᵒᵖ) := by
  let : PartialOrder (AdjointableMap D E E) :=
    CStarAlgebra.spectralOrder (AdjointableMap D E E)
  let : StarOrderedRing (AdjointableMap D E E) :=
    CStarAlgebra.spectralOrderedRing (AdjointableMap D E E)
  let a : AdjointableMap D E E := algebraMap ℝ _ (‖T‖ ^ 2) - star T * T
  have ha : 0 ≤ a := sub_nonneg.mpr CStarAlgebra.star_mul_le_algebraMap_norm_sq
  let r : AdjointableMap D E E := CFC.sqrt a
  have hr : star r = r := (CFC.sqrt_nonneg a).isSelfAdjoint
  have hrr : r * r = a := CFC.sqrt_mul_sqrt_self a ha
  have heq : ⟪r x, r x⟫_(Dᵐᵒᵖ) = ⟪x, a x⟫_(Dᵐᵒᵖ) := by
    rw [r.adjoint_identity]
    change ⟪x, (star r * r) x⟫_(Dᵐᵒᵖ) = ⟪x, a x⟫_(Dᵐᵒᵖ)
    rw [hr, hrr]
  have hpos : 0 ≤ ⟪x, a x⟫_(Dᵐᵒᵖ) :=
    heq ▸ CStarModule.inner_self_nonneg (x := r x)
  have hexpand : ⟪x, a x⟫_(Dᵐᵒᵖ) =
      ‖T‖ ^ 2 • ⟪x, x⟫_(Dᵐᵒᵖ) - ⟪T x, T x⟫_(Dᵐᵒᵖ) := by
    dsimp only [a]
    rw [AdjointableMap.coe_sub_apply, CStarModule.inner_sub_right,
      AdjointableMap.mul_apply, AdjointableMap.star_eq_adjoint]
    change ⟪x, (algebraMap ℝ (AdjointableMap D E E) (‖T‖ ^ 2)) x⟫_(Dᵐᵒᵖ) -
      ⟪x, T.adjointCLM (T x)⟫_(Dᵐᵒᵖ) = _
    rw [← T.adjoint_identity]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one]
    change ⟪x, (‖T‖ ^ 2) • x⟫_(Dᵐᵒᵖ) = _
    exact CStarModule.inner_smul_right_real
  exact sub_nonneg.mp (hexpand ▸ hpos)

end AdjointableMap

variable [CompleteSpace M]

/-- Evaluating the proved coefficient-order estimate gives the required
boundedness for the form-derived fibre norm. -/
theorem evaluatedModule_operator_formNorm_le (t : X)
    (T : AdjointableMap C(X, B) M M) (x : EvaluatedModuleSpace B M t) :
    PositiveModuleForm.formNorm (B := B) (evaluatedModuleOfOriginal B t (T (evaluatedModuleToOriginal t x))) ≤
      ‖T‖ * PositiveModuleForm.formNorm (B := B) x := by
  have hord :
      ⟪(evaluatedModuleOfOriginal B t (T (evaluatedModuleToOriginal t x))),
        (evaluatedModuleOfOriginal B t (T (evaluatedModuleToOriginal t x)))⟫_(Bᵐᵒᵖ) ≤
        ‖T‖ ^ 2 • ⟪x, x⟫_(Bᵐᵒᵖ) :=
    (AdjointableMap.inner_self_apply_le_norm_sq_smul T (evaluatedModuleToOriginal t x)) t
  have hnorm :
      ‖⟪(evaluatedModuleOfOriginal B t (T (evaluatedModuleToOriginal t x))),
        (evaluatedModuleOfOriginal B t (T (evaluatedModuleToOriginal t x)))⟫_(Bᵐᵒᵖ)‖ ≤
      ‖T‖ ^ 2 * ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ := by
    calc
      _ ≤ ‖‖T‖ ^ 2 • ⟪x, x⟫_(Bᵐᵒᵖ)‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le
          PositiveModuleForm.inner_self_nonneg hord
      _ = ‖T‖ ^ 2 * ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ := by simp [norm_smul]
  have hsq :
      (PositiveModuleForm.formNorm (B := B)
        (evaluatedModuleOfOriginal B t (T (evaluatedModuleToOriginal t x)))) ^ 2 ≤
      (‖T‖ * PositiveModuleForm.formNorm (B := B) x) ^ 2 := by
    rw [PositiveModuleForm.formNorm_sq, mul_pow, PositiveModuleForm.formNorm_sq]
    exact hnorm
  exact (pow_le_pow_iff_left₀ (PositiveModuleForm.formNorm_nonneg _)
    (mul_nonneg (norm_nonneg _) (PositiveModuleForm.formNorm_nonneg _))
      (by decide : (2 : ℕ) ≠ 0)).mp hsq

/-- The genuine fibre is the completion of the evaluated radical quotient.
Its norm is constructed directly from evaluation of the inner product. -/
abbrev HilbertModuleFibre (B M : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [NormedAddCommGroup M] [NormedSpace ℂ M]
    [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] (t : X) :=
  Completion (PositiveModuleQuotient B (EvaluatedModuleSpace B M t))

/-- The canonical map into the normed radical quotient is contractive for
the original Hilbert-module norm. -/
def hilbertModuleFibreQuotientMk (t : X) :
    M →L[ℂ] PositiveModuleQuotient B (EvaluatedModuleSpace B M t) :=
  LinearMap.mkContinuous
    ((positiveModuleQuotientMk (B := B)).comp
      (evaluatedModuleLinearEquiv (B := B) (M := M) t).symm.toLinearMap)
    1 (fun x => by
      simpa only [LinearMap.comp_apply, PositiveModuleQuotient.norm_mk, one_mul,
        evaluatedModuleToOriginal, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        evaluatedModule_formNorm_le (B := B) t
          ((evaluatedModuleLinearEquiv (B := B) (M := M) t).symm x))

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibreQuotientMk_apply (t : X) (x : M) :
    hilbertModuleFibreQuotientMk (B := B) t x =
      positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t x) := rfl

omit [CompleteSpace M] in
theorem hilbertModuleFibreQuotientMk_surjective (t : X) :
    Function.Surjective (hilbertModuleFibreQuotientMk (B := B) (M := M) t) := by
  intro q
  obtain ⟨x, hx⟩ := positiveModuleQuotientMk_surjective (E := EvaluatedModuleSpace B M t) q
  refine ⟨evaluatedModuleToOriginal t x, ?_⟩
  simpa only [hilbertModuleFibreQuotientMk_apply, evaluatedModule_of_to] using hx

/-- The dense, contractive canonical map from a module to its completed fibre. -/
def hilbertModuleFibreMk (t : X) : M →L[ℂ] HilbertModuleFibre B M t :=
  Completion.toComplL.comp (hilbertModuleFibreQuotientMk (B := B) t)

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibreMk_apply (t : X) (x : M) :
    hilbertModuleFibreMk (B := B) t x =
      ((positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t x)) :
        HilbertModuleFibre B M t) := rfl

omit [CompleteSpace M] in
theorem hilbertModuleFibreMk_denseRange (t : X) :
    DenseRange (hilbertModuleFibreMk (B := B) (M := M) t) :=
  Completion.denseRange_coe.comp
    (hilbertModuleFibreQuotientMk_surjective (B := B) (M := M) t).denseRange
    (Completion.continuous_coe _)

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibre_inner_mk (t : X) (x y : M) :
    ⟪hilbertModuleFibreMk (B := B) t x, hilbertModuleFibreMk (B := B) t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreMk_apply, completionInner_coe,
    PositiveModuleQuotient.inner_mk, evaluatedModule_inner, evaluatedModule_to_of,
    evaluatedModule_to_of]

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibre_norm_mk (t : X) (x : M) :
    ‖hilbertModuleFibreMk (B := B) t x‖ =
      Real.sqrt ‖MulOpposite.unop ⟪x, x⟫_(C(X, B)ᵐᵒᵖ) t‖ := by
  rw [hilbertModuleFibreMk_apply, Completion.norm_coe, PositiveModuleQuotient.norm_mk]
  rfl

omit [CompleteSpace M] in
theorem hilbertModuleFibreMk_norm_le (t : X) (x : M) :
    ‖hilbertModuleFibreMk (B := B) t x‖ ≤ ‖x‖ := by
  rw [hilbertModuleFibreMk_apply, Completion.norm_coe, PositiveModuleQuotient.norm_mk]
  exact evaluatedModule_formNorm_le (B := B) t (evaluatedModuleOfOriginal B t x)

omit [CompleteSpace M] in
/-- Every variable continuous coefficient acts on the fibre by its actual
evaluated coefficient. The source algebra need not have a unit. -/
@[simp] theorem hilbertModuleFibreMk_op_smul (t : X) (b : C(X, B)ᵐᵒᵖ) (x : M) :
    hilbertModuleFibreMk (B := B) t (b • x) =
      MulOpposite.op (MulOpposite.unop b t) • hilbertModuleFibreMk (B := B) t x := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreMk_apply, completion_op_smul_coe,
    PositiveModuleQuotient.op_smul_mk]
  apply congrArg (fun q : PositiveModuleQuotient B (EvaluatedModuleSpace B M t) =>
    (q : HilbertModuleFibre B M t))
  exact (PositiveModuleQuotient.mk_eq_mk _ _).mpr
    (evaluatedModule_variable_smul_sub_mem_nullRadical t b (evaluatedModuleOfOriginal B t x))

omit [CompleteSpace M] in
/-- Countable generation passes to the evaluated radical quotient and its
completion by the actual dense canonical map. -/
theorem IsCountablyGeneratedModule.fibre
    (hM : IsCountablyGeneratedModule C(X, B) M) (t : X) :
    IsCountablyGeneratedModule B (HilbertModuleFibre B M t) := by
  obtain ⟨ξ, hξ⟩ := hM
  refine ⟨fun n => hilbertModuleFibreMk (B := B) t (ξ n), ?_⟩
  have hm : ∀ x ∈ moduleGeneratingSpan (B := C(X, B)) ξ,
      hilbertModuleFibreMk (B := B) t x ∈ moduleGeneratingSpan (B := B)
        (fun n => hilbertModuleFibreMk (B := B) t (ξ n)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      rw [hilbertModuleFibreMk_op_smul]
      exact smul_mem_moduleGeneratingSpan _ n (MulOpposite.op (MulOpposite.unop b t))
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c hx
  exact ((hilbertModuleFibreMk_denseRange (B := B) (M := M) t).dense_image
    (hilbertModuleFibreMk (B := B) t).continuous hξ).mono (by
      rintro y ⟨x, hx, rfl⟩
      exact hm x hx)

/-- The source operator on the vector space carrying the evaluated form. -/
def evaluatedModuleOperatorLinearMap (t : X) (T : AdjointableMap C(X, B) M M) :
    EvaluatedModuleSpace B M t →ₗ[ℂ] EvaluatedModuleSpace B M t :=
  (evaluatedModuleLinearEquiv (B := B) (M := M) t).symm.toLinearMap.comp
    (T.toCLM.toLinearMap.comp (evaluatedModuleLinearEquiv (B := B) (M := M) t).toLinearMap)

/-- The operator descends continuously to the actual form-norm quotient. -/
def hilbertModuleFibreQuotientOperatorCLM (t : X)
    (T : AdjointableMap C(X, B) M M) :
    PositiveModuleQuotient B (EvaluatedModuleSpace B M t) →L[ℂ]
      PositiveModuleQuotient B (EvaluatedModuleSpace B M t) :=
  positiveModuleQuotientLiftCLM (evaluatedModuleOperatorLinearMap t T)
    (evaluatedModule_operator_formNorm_le t T)

@[simp] theorem hilbertModuleFibreQuotientOperatorCLM_mk (t : X)
    (T : AdjointableMap C(X, B) M M) (x : M) :
    hilbertModuleFibreQuotientOperatorCLM (B := B) t T
        (positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t x)) =
      positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t (T x)) := rfl

/-- Evaluation of the actual adjoint identity proves adjointability on the
radical quotient; no adjoint is assumed to exist on the fibre. -/
def hilbertModuleFibreQuotientOperator (t : X)
    (T : AdjointableMap C(X, B) M M) :
    AdjointableMap B (PositiveModuleQuotient B (EvaluatedModuleSpace B M t))
      (PositiveModuleQuotient B (EvaluatedModuleSpace B M t)) where
  toCLM := hilbertModuleFibreQuotientOperatorCLM t T
  adjointCLM := hilbertModuleFibreQuotientOperatorCLM t T.adjoint
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    change ⟪positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t (T (evaluatedModuleToOriginal t x))), positiveModuleQuotientMk (B := B) y⟫_(Bᵐᵒᵖ) =
      ⟪positiveModuleQuotientMk (B := B) x, positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t (T.adjoint (evaluatedModuleToOriginal t y)))⟫_(Bᵐᵒᵖ)
    rw [
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    exact congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
      (T.adjoint_identity (evaluatedModuleToOriginal t x) (evaluatedModuleToOriginal t y))

/-- Complete the proved bounded adjoint pair to the genuine fibre module. -/
def hilbertModuleFibreOperator (t : X) (T : AdjointableMap C(X, B) M M) :
    AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t) :=
  (hilbertModuleFibreQuotientOperator t T).completion

@[simp] theorem hilbertModuleFibreOperator_mk (t : X)
    (T : AdjointableMap C(X, B) M M) (x : M) :
    hilbertModuleFibreOperator (B := B) t T (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (T x) := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreOperator,
    AdjointableMap.completion_apply_coe]
  rfl

theorem hilbertModuleFibreOperator_norm_le (t : X)
    (T : AdjointableMap C(X, B) M M) :
    ‖hilbertModuleFibreOperator (B := B) t T‖ ≤ ‖T‖ := by
  rw [hilbertModuleFibreOperator, AdjointableMap.norm_completion]
  exact norm_positiveModuleQuotientLiftCLM_le
    (evaluatedModuleOperatorLinearMap t T) (norm_nonneg _)
    (evaluatedModule_operator_formNorm_le t T)

omit [CompleteSpace M] in
/-- Dense canonical images determine actual fibre operators uniquely. -/
theorem hilbertModuleFibreOperator_ext (t : X)
    {S T : AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)}
    (h : ∀ x : M, S (hilbertModuleFibreMk (B := B) t x) =
      T (hilbertModuleFibreMk (B := B) t x)) : S = T := by
  apply AdjointableMap.toCLM_injective
  apply ContinuousLinearMap.ext
  intro z
  exact congrFun ((hilbertModuleFibreMk_denseRange (B := B) (M := M) t).equalizer
    S.toCLM.continuous T.toCLM.continuous (funext h)) z

@[simp] theorem hilbertModuleFibreOperator_zero (t : X) :
    hilbertModuleFibreOperator (B := B) (M := M) t 0 = 0 := by
  apply hilbertModuleFibreOperator_ext t
  intro x
  simp only [hilbertModuleFibreOperator_mk, AdjointableMap.coe_zero_apply, map_zero]

@[simp] theorem hilbertModuleFibreOperator_one (t : X) :
    hilbertModuleFibreOperator (B := B) (M := M) t 1 = 1 := by
  apply hilbertModuleFibreOperator_ext t
  intro x
  simp only [hilbertModuleFibreOperator_mk, AdjointableMap.one_apply]

@[simp] theorem hilbertModuleFibreOperator_add (t : X)
    (S T : AdjointableMap C(X, B) M M) :
    hilbertModuleFibreOperator (B := B) t (S + T) =
      hilbertModuleFibreOperator (B := B) t S + hilbertModuleFibreOperator (B := B) t T := by
  apply hilbertModuleFibreOperator_ext t
  intro x
  simp only [hilbertModuleFibreOperator_mk, AdjointableMap.coe_add_apply, map_add]

@[simp] theorem hilbertModuleFibreOperator_smul (t : X) (c : ℂ)
    (T : AdjointableMap C(X, B) M M) :
    hilbertModuleFibreOperator (B := B) t (c • T) =
      c • hilbertModuleFibreOperator (B := B) t T := by
  apply hilbertModuleFibreOperator_ext t
  intro x
  simp only [hilbertModuleFibreOperator_mk, AdjointableMap.coe_smul_apply, map_smul]

@[simp] theorem hilbertModuleFibreOperator_mul (t : X)
    (S T : AdjointableMap C(X, B) M M) :
    hilbertModuleFibreOperator (B := B) t (S * T) =
      hilbertModuleFibreOperator (B := B) t S * hilbertModuleFibreOperator (B := B) t T := by
  apply hilbertModuleFibreOperator_ext t
  intro x
  simp only [hilbertModuleFibreOperator_mk, AdjointableMap.mul_apply]

@[simp] theorem hilbertModuleFibreOperator_star (t : X)
    (T : AdjointableMap C(X, B) M M) :
    hilbertModuleFibreOperator (B := B) t (star T) =
      star (hilbertModuleFibreOperator (B := B) t T) := by
  apply AdjointableMap.toCLM_injective
  ext z
  refine Completion.induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro q
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    simp only [hilbertModuleFibreOperator, AdjointableMap.star_eq_adjoint,
      AdjointableMap.completion_adjoint, AdjointableMap.completion_apply_coe]
    rfl

/-- Fibre evaluation is a contractive complex star-algebra homomorphism on
the actual adjointable endomorphism algebras. -/
def hilbertModuleFibreOperatorHom (t : X) :
    AdjointableMap C(X, B) M M →⋆ₐ[ℂ]
      AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t) where
  toFun := hilbertModuleFibreOperator t
  map_zero' := hilbertModuleFibreOperator_zero t
  map_one' := hilbertModuleFibreOperator_one t
  map_add' := hilbertModuleFibreOperator_add t
  map_mul' := hilbertModuleFibreOperator_mul t
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, hilbertModuleFibreOperator_smul,
      hilbertModuleFibreOperator_one, Algebra.algebraMap_eq_smul_one]
  map_star' := hilbertModuleFibreOperator_star t

@[simp] theorem hilbertModuleFibreOperator_sub (t : X)
    (S T : AdjointableMap C(X, B) M M) :
    hilbertModuleFibreOperator (B := B) t (S - T) =
      hilbertModuleFibreOperator (B := B) t S - hilbertModuleFibreOperator (B := B) t T :=
  (hilbertModuleFibreOperatorHom t).map_sub S T

/-- The same contractive operator map, bundled continuously and linearly. -/
def hilbertModuleFibreOperatorCLM (t : X) :
    AdjointableMap C(X, B) M M →L[ℂ]
      AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t) :=
  LinearMap.mkContinuous (hilbertModuleFibreOperatorHom t).toLinearMap 1
    (fun T => by
      change ‖hilbertModuleFibreOperator (B := B) t T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using hilbertModuleFibreOperator_norm_le t T)

/-- Actual module rank-one maps evaluate to rank-one maps of the canonical
fibre vectors. The coefficient in a source rank one is a variable function. -/
@[simp] theorem hilbertModuleFibreOperator_rankOne (t : X) (x y : M) :
    hilbertModuleFibreOperator (B := B) t (moduleRankOne (B := C(X, B)) x y) =
      moduleRankOne (B := B) (hilbertModuleFibreMk (B := B) t x)
        (hilbertModuleFibreMk (B := B) t y) := by
  apply hilbertModuleFibreOperator_ext t
  intro z
  simp only [hilbertModuleFibreOperator_mk, moduleRankOne_apply,
    hilbertModuleFibreMk_op_smul, hilbertModuleFibre_inner_mk]

/-- Fibre evaluation preserves module compactness by continuity and the
proved image of rank-one maps, rather than pointwise compactness alone. -/
theorem IsModuleCompact.fibre {T : AdjointableMap C(X, B) M M}
    (hT : IsModuleCompact T) (t : X) :
    IsModuleCompact (hilbertModuleFibreOperator (B := B) t T) := by
  let S : Submodule ℂ (AdjointableMap C(X, B) M M) :=
    (moduleCompact B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)).comap
      (hilbertModuleFibreOperatorCLM (B := B) (M := M) t).toLinearMap
  have hS : IsClosed (S : Set (AdjointableMap C(X, B) M M)) :=
    (moduleCompact_isClosed (B := B) (E := HilbertModuleFibre B M t)
      (F := HilbertModuleFibre B M t)).preimage
      (hilbertModuleFibreOperatorCLM (B := B) (M := M) t).continuous
  have hθ (x y : M) : moduleRankOne (B := C(X, B)) x y ∈ S := by
    change IsModuleCompact
      (hilbertModuleFibreOperator (B := B) t (moduleRankOne (B := C(X, B)) x y))
    rw [hilbertModuleFibreOperator_rankOne]
    exact moduleRankOne_mem_moduleCompact _ _
  exact (moduleCompact_le_of_isClosed S hS hθ) hT

/-- Any complex-linear map with a proved evaluated-form bound descends to
the fibre. This also handles actions that twist the coefficient algebra. -/
def evaluatedModuleLinearMap (t : X) (f : M →ₗ[ℂ] M) :
    EvaluatedModuleSpace B M t →ₗ[ℂ] EvaluatedModuleSpace B M t :=
  (evaluatedModuleLinearEquiv (B := B) (M := M) t).symm.toLinearMap.comp
    (f.comp (evaluatedModuleLinearEquiv (B := B) (M := M) t).toLinearMap)

def hilbertModuleFibreLinearMap (t : X) (f : M →ₗ[ℂ] M) {K : ℝ}
    (hf : ∀ x : EvaluatedModuleSpace B M t,
      PositiveModuleForm.formNorm (B := B) (evaluatedModuleOfOriginal B t (f (evaluatedModuleToOriginal t x))) ≤
        K * PositiveModuleForm.formNorm (B := B) x) :
    HilbertModuleFibre B M t →L[ℂ] HilbertModuleFibre B M t :=
  (positiveModuleQuotientLiftCLM (evaluatedModuleLinearMap t f) hf).completion

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibreLinearMap_mk (t : X) (f : M →ₗ[ℂ] M) {K : ℝ}
    (hf : ∀ x : EvaluatedModuleSpace B M t,
      PositiveModuleForm.formNorm (B := B) (evaluatedModuleOfOriginal B t (f (evaluatedModuleToOriginal t x))) ≤
        K * PositiveModuleForm.formNorm (B := B) x) (x : M) :
    hilbertModuleFibreLinearMap (B := B) t f hf (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (f x) := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreLinearMap,
    ContinuousLinearMap.completion_apply_coe]
  rfl

omit [CompleteSpace M] in
theorem hilbertModuleFibreLinearMap_norm_le (t : X) (f : M →ₗ[ℂ] M) {K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ x : EvaluatedModuleSpace B M t,
      PositiveModuleForm.formNorm (B := B) (evaluatedModuleOfOriginal B t (f (evaluatedModuleToOriginal t x))) ≤
        K * PositiveModuleForm.formNorm (B := B) x) :
    ‖hilbertModuleFibreLinearMap (B := B) t f hf‖ ≤ K := by
  rw [hilbertModuleFibreLinearMap, completionCLM_norm]
  exact norm_positiveModuleQuotientLiftCLM_le (evaluatedModuleLinearMap t f) hK hf

omit [CompleteSpace M] in
/-- Equality of continuous fibre maps is determined by the actual dense
canonical image of the original module. -/
theorem hilbertModuleFibreCLM_ext (t : X)
    {S T : HilbertModuleFibre B M t →L[ℂ] HilbertModuleFibre B M t}
    (h : ∀ x : M, S (hilbertModuleFibreMk (B := B) t x) =
      T (hilbertModuleFibreMk (B := B) t x)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  exact congrFun ((hilbertModuleFibreMk_denseRange (B := B) (M := M) t).equalizer
    S.continuous T.continuous (funext h)) z

/-- A complex-linear vector-space automorphism preserving the evaluated
length gives an actual isometric automorphism of the completed fibre. -/
def hilbertModuleFibreLinearIsometryEquiv (t : X) (e : M ≃ₗ[ℂ] M)
    (he : ∀ x : EvaluatedModuleSpace B M t,
      PositiveModuleForm.formNorm (B := B) (evaluatedModuleOfOriginal B t (e (evaluatedModuleToOriginal t x))) =
        PositiveModuleForm.formNorm (B := B) x) :
    HilbertModuleFibre B M t ≃ₗᵢ[ℂ] HilbertModuleFibre B M t := by
  have hei (x : EvaluatedModuleSpace B M t) :
      PositiveModuleForm.formNorm (B := B)
        (evaluatedModuleOfOriginal B t (e.symm (evaluatedModuleToOriginal t x))) =
          PositiveModuleForm.formNorm (B := B) x := by
    have h := he (evaluatedModuleOfOriginal B t (e.symm (evaluatedModuleToOriginal t x)))
    simpa only [evaluatedModule_to_of, e.apply_symm_apply, evaluatedModule_of_to] using h.symm
  let f := hilbertModuleFibreLinearMap (B := B) t e.toLinearMap (K := 1)
    (fun x => by simpa only [one_mul, LinearEquiv.coe_coe] using (he x).le)
  let g := hilbertModuleFibreLinearMap (B := B) t e.symm.toLinearMap (K := 1)
    (fun x => by simpa only [one_mul, LinearEquiv.coe_coe] using (hei x).le)
  have hgf : g.comp f = ContinuousLinearMap.id ℂ _ := by
    apply hilbertModuleFibreCLM_ext t
    intro x
    simp only [ContinuousLinearMap.comp_apply, f, g, hilbertModuleFibreLinearMap_mk,
      LinearEquiv.coe_coe, e.symm_apply_apply, ContinuousLinearMap.id_apply]
  have hfg : f.comp g = ContinuousLinearMap.id ℂ _ := by
    apply hilbertModuleFibreCLM_ext t
    intro x
    simp only [ContinuousLinearMap.comp_apply, f, g, hilbertModuleFibreLinearMap_mk,
      LinearEquiv.coe_coe, e.apply_symm_apply, ContinuousLinearMap.id_apply]
  have hf_norm : ∀ z, ‖f z‖ ≤ ‖z‖ := by
    intro z
    exact (f.le_opNorm z).trans (by
      have h := hilbertModuleFibreLinearMap_norm_le (B := B) t e.toLinearMap
        (by norm_num : (0 : ℝ) ≤ 1) (fun x => by simpa only [one_mul, LinearEquiv.coe_coe] using (he x).le)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg z))
  have hg_norm : ∀ z, ‖g z‖ ≤ ‖z‖ := by
    intro z
    exact (g.le_opNorm z).trans (by
      have h := hilbertModuleFibreLinearMap_norm_le (B := B) t e.symm.toLinearMap
        (by norm_num : (0 : ℝ) ≤ 1) (fun x => by simpa only [one_mul, LinearEquiv.coe_coe] using (hei x).le)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg z))
  exact
    { toLinearEquiv :=
        { toLinearMap := f.toLinearMap
          invFun := g
          left_inv := fun z => congrArg (fun h : _ →L[ℂ] _ => h z) hgf
          right_inv := fun z => congrArg (fun h : _ →L[ℂ] _ => h z) hfg }
      norm_map' z := by
        change ‖f z‖ = ‖z‖
        apply le_antisymm (hf_norm z)
        have hh : g (f z) = z := congrArg (fun h : _ →L[ℂ] _ => h z) hgf
        calc
          ‖z‖ = ‖g (f z)‖ := congrArg norm hh.symm
          _ ≤ ‖f z‖ := hg_norm (f z) }

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibreLinearIsometryEquiv_mk (t : X) (e : M ≃ₗ[ℂ] M)
    (he : ∀ x : EvaluatedModuleSpace B M t,
      PositiveModuleForm.formNorm (B := B) (evaluatedModuleOfOriginal B t (e (evaluatedModuleToOriginal t x))) =
        PositiveModuleForm.formNorm (B := B) x) (x : M) :
    hilbertModuleFibreLinearIsometryEquiv (B := B) t e he (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (e x) := by
  exact hilbertModuleFibreLinearMap_mk (B := B) t e.toLinearMap _ x

section ContinuousSections

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- For actual continuous sections, the evaluated form length is the norm
of the evaluated section. -/
theorem evaluatedContinuousSection_formNorm (t : X)
    (x : EvaluatedModuleSpace B C(X, E) t) :
    PositiveModuleForm.formNorm (B := B) x = ‖(evaluatedModuleToOriginal t x) t‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]
  rfl

/-- Actual evaluation factors through the null radical of the evaluated form. -/
def continuousSectionEvaluatedQuotientEvaluation (t : X) :
    PositiveModuleQuotient B (EvaluatedModuleSpace B C(X, E) t) →ₗ[ℂ] E :=
  (PositiveModuleForm.nullRadical (B := B) (E := EvaluatedModuleSpace B C(X, E) t)).liftQ
    ((continuousSectionEvaluation (E := E) t).toLinearMap.comp
      (evaluatedModuleLinearEquiv (B := B) (M := C(X, E)) t).toLinearMap)
    (fun x hx => by
      change (evaluatedModuleToOriginal t x) t = 0
      apply norm_eq_zero.mp
      rw [← evaluatedContinuousSection_formNorm]
      exact (PositiveModuleForm.formNorm_eq_zero_iff x).mpr hx)

omit [CompleteSpace E] in
@[simp] theorem continuousSectionEvaluatedQuotientEvaluation_mk (t : X) (x : C(X, E)) :
    continuousSectionEvaluatedQuotientEvaluation (B := B) t
        (positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t x)) =
      x t := rfl

omit [CompleteSpace E] in
/-- The evaluated quotient carries exactly the evaluation norm. -/
theorem continuousSectionEvaluatedQuotientEvaluation_norm (t : X)
    (q : PositiveModuleQuotient B (EvaluatedModuleSpace B C(X, E) t)) :
    ‖continuousSectionEvaluatedQuotientEvaluation (B := B) t q‖ = ‖q‖ := by
  obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
  change ‖evaluatedModuleToOriginal t x t‖ = ‖positiveModuleQuotientMk (B := B) x‖
  rw [PositiveModuleQuotient.norm_mk]
  exact (evaluatedContinuousSection_formNorm t x).symm

def continuousSectionEvaluatedQuotientEvaluationCLM (t : X) :
    PositiveModuleQuotient B (EvaluatedModuleSpace B C(X, E) t) →L[ℂ] E :=
  (continuousSectionEvaluatedQuotientEvaluation (B := B) t).mkContinuous 1
    (fun q => by simpa only [one_mul] using
      (continuousSectionEvaluatedQuotientEvaluation_norm (B := B) t q).le)

/-- Evaluation extends from its genuine radical quotient to its completion. -/
def continuousSectionHilbertModuleFibreEvaluation (t : X) :
    HilbertModuleFibre B C(X, E) t →L[ℂ] E :=
  (continuousSectionEvaluatedQuotientEvaluationCLM (B := B) t).fromCompletion

@[simp] theorem continuousSectionHilbertModuleFibreEvaluation_mk (t : X) (x : C(X, E)) :
    continuousSectionHilbertModuleFibreEvaluation (B := B) t
      (hilbertModuleFibreMk (B := B) t x) = x t := by
  rw [hilbertModuleFibreMk_apply, continuousSectionHilbertModuleFibreEvaluation,
    ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- The genuine completed fibre of `C(X,E)` is unitarily isomorphic to `E`.
This is proved for the form-derived quotient completion, independently of
the earlier Banach-quotient model of continuous-section evaluation. -/
def continuousSectionHilbertModuleFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B C(X, E) t) E := by
  let f := continuousSectionHilbertModuleFibreEvaluation (B := B) (E := E) t
  have hnorm (z : HilbertModuleFibre B C(X, E) t) : ‖f z‖ = ‖z‖ := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(X, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_norm
    · intro x
      rw [continuousSectionHilbertModuleFibreEvaluation_mk, hilbertModuleFibre_norm_mk]
      exact CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) _
  have hleft (z : HilbertModuleFibre B C(X, E) t) :
      hilbertModuleFibreMk (B := B) t (ContinuousMap.const X (f z)) = z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(X, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_id
    · intro x
      rw [continuousSectionHilbertModuleFibreEvaluation_mk]
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      rw [← map_sub, hilbertModuleFibre_norm_mk]
      have hzero : (ContinuousMap.const X (x t) - x) t = 0 := by simp
      change Real.sqrt ‖⟪(ContinuousMap.const X (x t) - x) t,
        (ContinuousMap.const X (x t) - x) t⟫_(Bᵐᵒᵖ)‖ = 0
      simp only [hzero, CStarModule.inner_zero_left, norm_zero, Real.sqrt_zero]
  have hright (x : E) : f (hilbertModuleFibreMk (B := B) t (ContinuousMap.const X x)) = x :=
    continuousSectionHilbertModuleFibreEvaluation_mk t (ContinuousMap.const X x)
  refine
    { linearIsometryEquiv :=
        { toLinearEquiv :=
            { toLinearMap := f.toLinearMap
              invFun := fun x => hilbertModuleFibreMk (B := B) t (ContinuousMap.const X x)
              left_inv := hleft
              right_inv := hright }
          norm_map' := hnorm }
      inner_map := ?_ }
  intro x y
  have hinner (p : HilbertModuleFibre B C(X, E) t × HilbertModuleFibre B C(X, E) t) :
      ⟪f p.1, f p.2⟫_(Bᵐᵒᵖ) = ⟪p.1, p.2⟫_(Bᵐᵒᵖ) := by
    refine ((hilbertModuleFibreMk_denseRange (B := B) (M := C(X, E)) t).prodMap
      (hilbertModuleFibreMk_denseRange (B := B) (M := C(X, E)) t)).induction_on p ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro q
      change ⟪f (hilbertModuleFibreMk (B := B) t q.1),
        f (hilbertModuleFibreMk (B := B) t q.2)⟫_(Bᵐᵒᵖ) =
          ⟪hilbertModuleFibreMk (B := B) t q.1, hilbertModuleFibreMk (B := B) t q.2⟫_(Bᵐᵒᵖ)
      simp only [f, continuousSectionHilbertModuleFibreEvaluation_mk,
        hilbertModuleFibre_inner_mk, continuousSection_inner_apply]
      rfl
  exact hinner (x, y)

@[simp] theorem continuousSectionHilbertModuleFibreEquiv_mk (t : X) (x : C(X, E)) :
    continuousSectionHilbertModuleFibreEquiv (B := B) t
      (hilbertModuleFibreMk (B := B) t x) = x t :=
  continuousSectionHilbertModuleFibreEvaluation_mk t x

end ContinuousSections

section EvaluationIdentification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- An actual surjective evaluation preserving the evaluated coefficient form
identifies the completed fibre with its target. The norm and completeness of
the fibre are the already constructed form-quotient completion. -/
def hilbertModuleFibreEquivOfEvaluation (t : X) (f : M →L[ℂ] E)
    (hf : ∀ x y : M, ⟪f x, f y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t))
    (hfs : Function.Surjective f) : HilbertModuleEquiv B (HilbertModuleFibre B M t) E := by
  let fq : PositiveModuleQuotient B (EvaluatedModuleSpace B M t) →ₗ[ℂ] E :=
    (PositiveModuleForm.nullRadical (B := B) (E := EvaluatedModuleSpace B M t)).liftQ
      (f.toLinearMap.comp (evaluatedModuleLinearEquiv (B := B) (M := M) t).toLinearMap)
      (fun x hx => by
        apply (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp
        change ⟪f (evaluatedModuleToOriginal t x), f (evaluatedModuleToOriginal t x)⟫_(Bᵐᵒᵖ) = 0
        rw [hf]
        exact (PositiveModuleForm.mem_nullRadical x).mp hx)
  have fq_mk (x : M) :
      fq (positiveModuleQuotientMk (B := B) (evaluatedModuleOfOriginal B t x)) = f x := rfl
  have fq_norm (q : PositiveModuleQuotient B (EvaluatedModuleSpace B M t)) :
      ‖fq q‖ = ‖q‖ := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    change ‖f (evaluatedModuleToOriginal t x)‖ = ‖positiveModuleQuotientMk (B := B) x‖
    rw [PositiveModuleQuotient.norm_mk,
      CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), hf]
    rfl
  let fqL : PositiveModuleQuotient B (EvaluatedModuleSpace B M t) →L[ℂ] E :=
    fq.mkContinuous 1 (fun q => by simpa only [one_mul] using (fq_norm q).le)
  let F : HilbertModuleFibre B M t →L[ℂ] E := fqL.fromCompletion
  have F_mk (x : M) : F (hilbertModuleFibreMk (B := B) t x) = f x := by
    rw [hilbertModuleFibreMk_apply, ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have F_norm (z : HilbertModuleFibre B M t) : ‖F z‖ = ‖z‖ := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_norm
    · intro x
      rw [F_mk, hilbertModuleFibre_norm_mk,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), hf]
      rfl
  have F_inj : Function.Injective F := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← F_norm, map_sub, hxy, sub_self, norm_zero]
  have F_surj : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := hfs y
    exact ⟨hilbertModuleFibreMk (B := B) t x, F_mk x⟩
  refine
    { linearIsometryEquiv :=
        { toLinearEquiv := LinearEquiv.ofBijective F.toLinearMap ⟨F_inj, F_surj⟩
          norm_map' := F_norm }
      inner_map := ?_ }
  intro x y
  have hinner (p : HilbertModuleFibre B M t × HilbertModuleFibre B M t) :
      ⟪F p.1, F p.2⟫_(Bᵐᵒᵖ) = ⟪p.1, p.2⟫_(Bᵐᵒᵖ) := by
    refine ((hilbertModuleFibreMk_denseRange (B := B) (M := M) t).prodMap
      (hilbertModuleFibreMk_denseRange (B := B) (M := M) t)).induction_on p ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro q
      change ⟪F (hilbertModuleFibreMk (B := B) t q.1),
        F (hilbertModuleFibreMk (B := B) t q.2)⟫_(Bᵐᵒᵖ) =
          ⟪hilbertModuleFibreMk (B := B) t q.1, hilbertModuleFibreMk (B := B) t q.2⟫_(Bᵐᵒᵖ)
      rw [F_mk, F_mk, hilbertModuleFibre_inner_mk]
      exact hf q.1 q.2
  exact hinner (x, y)

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibreEquivOfEvaluation_mk (t : X) (f : M →L[ℂ] E)
    (hf : ∀ x y : M, ⟪f x, f y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t))
    (hfs : Function.Surjective f) (x : M) :
    hilbertModuleFibreEquivOfEvaluation t f hf hfs (hilbertModuleFibreMk (B := B) t x) = f x := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _ _

end EvaluationIdentification

end BC4lean.KKTheory
