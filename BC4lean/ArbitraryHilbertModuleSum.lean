import BC4lean.CountableHilbertModuleSum

/-! # The actual arbitrary-index Hilbert-module sum



This generalizes the proved finite-form construction in
CountableHilbertModuleSum.lean by replacing its index type Nat with any type I.
The finite coefficient-valued form is built from the given CStarModule inner
product; its positivity, definiteness, zero radical, and coordinate estimates
are proved below. The actual radical quotient and its norm completion supply
the normed Hilbert-module structures through PositiveModuleQuotient and
HilbertModuleCompletion. No scalar l2 norm on E is imposed.

The import reuses the already proved coefficient SMulZeroClass law from
CountableHilbertModuleSum.lean; it supplies no positivity or completion
hypotheses for the new arbitrary-index form. Completeness of E is required
only for extending coordinate evaluation back into E.
-/

noncomputable section
namespace BC4lean.KKTheory
namespace IndexedHilbertModule
open UniformSpace
open scoped InnerProductSpace

variable {B E I : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

local instance : DecidableEq I := Classical.decEq I

abbrev Vectors (E I : Type*) [Zero E] := I →₀ E

/-- The actual finite coefficient form of a finite family of module vectors. -/
def finiteInner (x y : Vectors E I) : Bᵐᵒᵖ :=
  x.sum fun i v => ⟪v, y i⟫_(Bᵐᵒᵖ)

omit [StarOrderedRing B] in
theorem finiteInner_eq_sum (x y : Vectors E I) (s : Finset I)
    (h : x.support ⊆ s) :
    finiteInner (B := B) x y = ∑ i ∈ s, ⟪x i, y i⟫_(Bᵐᵒᵖ) :=
  Finsupp.sum_of_support_subset x h _ (fun _ _ => CStarModule.inner_zero_left)

omit [StarOrderedRing B] in
theorem finiteInner_star (x y : Vectors E I) :
    star (finiteInner (B := B) x y) = finiteInner (B := B) y x := by
  rw [finiteInner_eq_sum x y (x.support ∪ y.support) Finset.subset_union_left,
    finiteInner_eq_sum y x (x.support ∪ y.support) Finset.subset_union_right,
    star_sum]
  exact Finset.sum_congr rfl fun i _ => CStarModule.star_inner (x i) (y i)

instance finitePositiveForm : PositiveModuleForm B (Vectors E I) where
  inner := finiteInner
  inner_add_right := by
    intro x y z
    simp only [finiteInner, Finsupp.sum, Finsupp.add_apply,
      CStarModule.inner_add_right, Finset.sum_add_distrib]
  inner_self_nonneg := by
    intro x
    exact Finset.sum_nonneg (fun _ _ => CStarModule.inner_self_nonneg)
  inner_op_smul_right := by
    intro a x y
    simp only [finiteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_op_smul_right, Finset.mul_sum]
  inner_smul_right_complex := by
    intro c x y
    simp only [finiteInner, Finsupp.sum, Finsupp.smul_apply,
      CStarModule.inner_smul_right_complex, Finset.smul_sum]
  star_inner := finiteInner_star

@[simp] theorem finite_inner (x y : Vectors E I) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = finiteInner (B := B) x y := rfl

theorem finite_coordinate_inner_le (x : Vectors E I) (i : I) :
    ⟪x i, x i⟫_(Bᵐᵒᵖ) ≤ finiteInner (B := B) x x := by
  by_cases hi : i ∈ x.support
  · exact Finset.single_le_sum (fun _ _ => CStarModule.inner_self_nonneg) hi
  · have hz : x i = 0 := Finsupp.notMem_support_iff.mp hi
    simpa only [hz, CStarModule.inner_zero_left, finite_inner] using
      (PositiveModuleForm.inner_self_nonneg (B := B) (x := x))

theorem finiteInner_self_eq_zero_iff (x : Vectors E I) :
    finiteInner (B := B) x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have hi : ⟪x i, x i⟫_(Bᵐᵒᵖ) = 0 := le_antisymm
      (hx ▸ finite_coordinate_inner_le x i) CStarModule.inner_self_nonneg
    exact CStarModule.inner_self.mp hi
  · rintro rfl
    simp [finiteInner]

theorem finite_nullRadical_eq_bot :
    PositiveModuleForm.nullRadical (B := B) (E := Vectors E I) = ⊥ := by
  ext x
  rw [PositiveModuleForm.mem_nullRadical, finite_inner,
    finiteInner_self_eq_zero_iff, Submodule.mem_bot]

omit [StarOrderedRing B] in
@[simp] theorem finiteInner_single_left (i : I) (v : E) (x : Vectors E I) :
    finiteInner (B := B) (Finsupp.single i v) x = ⟪v, x i⟫_(Bᵐᵒᵖ) := by
  simp [finiteInner]

theorem finite_formNorm_single (i : I) (v : E) :
    PositiveModuleForm.formNorm (B := B) (Finsupp.single i v) = ‖v‖ := by
  rw [PositiveModuleForm.formNorm, finite_inner,
    finiteInner_single_left, Finsupp.single_eq_same]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) v).symm

theorem finite_norm_coordinate_le (x : Vectors E I) (i : I) :
    ‖x i‖ ≤ PositiveModuleForm.formNorm (B := B) x := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x i), PositiveModuleForm.formNorm]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le CStarModule.inner_self_nonneg
    (finite_coordinate_inner_le x i)

/-- Finite module vectors with their actual form-derived Hilbert norm. -/
abbrev PreModule (B E I : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] :=
  PositiveModuleQuotient B (Vectors E I)

/-- The actual finite-vector quotient map is injective because its radical is zero. -/
theorem preMk_injective :
    Function.Injective (positiveModuleQuotientMk (B := B) (E := Vectors E I)) := by
  intro x y h
  have hr := (PositiveModuleQuotient.mk_eq_mk x y).mp h
  rw [finite_nullRadical_eq_bot, Submodule.mem_bot] at hr
  exact sub_eq_zero.mp hr

/-- The actual indexed Hilbert-module sum, completed in its coefficient norm. -/
abbrev Module (B E I : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] :=
  Completion (PreModule B E I)

def mk : Vectors E I →ₗ[ℂ] Module B E I :=
  Completion.toComplL.toLinearMap.comp (positiveModuleQuotientMk (B := B))

@[simp] theorem mk_apply (x : Vectors E I) :
    mk (B := B) x =
      ((positiveModuleQuotientMk (B := B) x) : Module B E I) := rfl

theorem mk_injective : Function.Injective (mk (B := B) (E := E) (I := I)) :=
  (Completion.coe_injective _).comp (preMk_injective (B := B) (E := E) (I := I))

theorem mk_denseRange : DenseRange (mk (B := B) (E := E) (I := I)) :=
  Completion.denseRange_coe.comp positiveModuleQuotientMk_surjective.denseRange (Completion.continuous_coe _)

@[simp] theorem mk_inner (x y : Vectors E I) :
    ⟪mk (B := B) x, mk (B := B) y⟫_(Bᵐᵒᵖ) =
      finiteInner (B := B) x y := by
  rw [mk_apply, mk_apply, completionInner_coe,
    PositiveModuleQuotient.inner_mk]
  rfl

@[simp] theorem mk_norm (x : Vectors E I) :
    ‖mk (B := B) x‖ = Real.sqrt ‖x.sum (fun i v => ⟪v, x i⟫_(Bᵐᵒᵖ))‖ := by
  rw [mk_apply, Completion.norm_coe, PositiveModuleQuotient.norm_mk]
  rfl

theorem mk_norm_eq_formNorm (x : Vectors E I) :
    ‖mk (B := B) x‖ = PositiveModuleForm.formNorm (B := B) x := by
  rw [mk_apply, Completion.norm_coe, PositiveModuleQuotient.norm_mk]

@[simp] theorem mk_op_smul (a : Bᵐᵒᵖ) (x : Vectors E I) :
    mk (B := B) (a • x) = a • mk (B := B) x := by
  rw [mk_apply, mk_apply, completion_op_smul_coe,
    PositiveModuleQuotient.op_smul_mk]

def quotientEvaluationLinear (i : I) : PreModule B E I →ₗ[ℂ] E :=
  (PositiveModuleForm.nullRadical (B := B) (E := Vectors E I)).liftQ
    (Finsupp.lapply i) (fun x hx => by
      rw [finite_nullRadical_eq_bot, Submodule.mem_bot] at hx
      simp [hx])

@[simp] theorem quotientEvaluationLinear_mk (i : I) (x : Vectors E I) :
    quotientEvaluationLinear (B := B) i (positiveModuleQuotientMk (B := B) x) = x i := rfl

def quotientEvaluationCLM (i : I) : PreModule B E I →L[ℂ] E :=
  (quotientEvaluationLinear i).mkContinuous 1 (fun q => by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    simpa only [quotientEvaluationLinear_mk, PositiveModuleQuotient.norm_mk, one_mul]
      using finite_norm_coordinate_le x i)

def quotientInclusionCLM (i : I) : E →L[ℂ] PreModule B E I :=
  ((positiveModuleQuotientMk (B := B)).comp (Finsupp.lsingle i)).mkContinuous 1
    (fun v => by
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, PositiveModuleQuotient.norm_mk,
        finite_formNorm_single, one_mul, le_refl])

def quotientInclusion (i : I) :
    AdjointableMap B E (PreModule B E I) where
  toCLM := quotientInclusionCLM i
  adjointCLM := quotientEvaluationCLM i
  adjoint_identity v q := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    change ⟪positiveModuleQuotientMk (B := B) (Finsupp.single i v),
      positiveModuleQuotientMk (B := B) x⟫_(Bᵐᵒᵖ) = ⟪v, x i⟫_(Bᵐᵒᵖ)
    rw [PositiveModuleQuotient.inner_mk]
    exact finiteInner_single_left i v x

variable [CompleteSpace E]

/-- Inclusion in the complete indexed sum, with the actual extended restriction adjoint. -/
def inclusion (i : I) : AdjointableMap B E (Module B E I) where
  toCLM := Completion.toComplL.comp (quotientInclusion i).toCLM
  adjointCLM := (quotientInclusion i).adjointCLM.fromCompletion
  adjoint_identity v x := by
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp (continuous_const.prodMk continuous_id))
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk (quotientInclusion i).adjointCLM.fromCompletion.continuous))
    · intro q
      change ⟪(((quotientInclusion i).toCLM v : PreModule B E I) :
        Module B E I), (q : Module B E I)⟫_(Bᵐᵒᵖ) =
        ⟪v, (quotientInclusion i).adjointCLM.fromCompletion
          (q : Module B E I)⟫_(Bᵐᵒᵖ)
      rw [completionInner_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      exact (quotientInclusion i).adjoint_identity v q

def evaluation (i : I) : AdjointableMap B (Module B E I) E :=
  (inclusion i).adjoint

@[simp] theorem inclusion_adjoint (i : I) :
    (inclusion (B := B) (E := E) i).adjoint = evaluation (B := B) i := rfl

@[simp] theorem evaluation_adjoint (i : I) :
    (evaluation (B := B) (E := E) i).adjoint = inclusion (B := B) i := rfl

@[simp] theorem inclusion_apply (i : I) (v : E) :
    inclusion (B := B) i v = mk (B := B) (Finsupp.single i v) := rfl

@[simp] theorem evaluation_mk (i : I) (x : Vectors E I) :
    evaluation (B := B) i (mk (B := B) x) = x i := by
  rw [mk_apply]
  change (quotientEvaluationCLM i).fromCompletion
    ((positiveModuleQuotientMk (B := B) x) : Module B E I) = x i
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- Coordinate evaluation and inclusion have the actual Kronecker delta law. -/
@[simp] theorem evaluation_inclusion (i j : I) (v : E) :
    evaluation (B := B) i (inclusion (B := B) j v) =
      if j = i then v else 0 := by
  rw [inclusion_apply, evaluation_mk]
  exact Finsupp.single_apply

@[simp] theorem inclusion_norm (i : I) (v : E) :
    ‖inclusion (B := B) i v‖ = ‖v‖ := by
  rw [inclusion_apply, mk_apply, Completion.norm_coe,
    PositiveModuleQuotient.norm_mk, finite_formNorm_single]

theorem norm_inclusion_le (i : I) : ‖inclusion (B := B) (E := E) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖inclusion (B := B) i v‖ ≤ 1 * ‖v‖
  rw [inclusion_norm, one_mul]

theorem norm_evaluation_le (i : I) : ‖evaluation (B := B) (E := E) i‖ ≤ 1 := by
  change ‖(inclusion (B := B) (E := E) i).adjoint.toCLM‖ ≤ 1
  rw [AdjointableMap.norm_adjoint_toCLM]
  exact norm_inclusion_le i

/-- Pairing a finite vector with any actual sum uses its finitely many coordinates. -/
theorem mk_inner_right (u : Vectors E I)
    (x : Module B E I) :
    ⟪mk (B := B) u, x⟫_(Bᵐᵒᵖ) =
      ∑ i ∈ u.support, ⟪u i, evaluation (B := B) i x⟫_(Bᵐᵒᵖ) := by
  classical
  have hu : mk (B := B) u =
      ∑ i ∈ u.support, inclusion (B := B) i (u i) := by
    simp only [inclusion_apply, ← map_sum]
    exact congrArg (mk (B := B)) u.sum_single.symm
  rw [hu, CStarModule.inner_sum_left (A := Bᵐᵒᵖ) (E := Module B E I)]
  exact Finset.sum_congr rfl (fun i _ => (inclusion (B := B) i).adjoint_identity _ _)

/-- Actual coordinate evaluations separate the completed indexed sum. -/
theorem ext_eval {x y : Module B E I}
    (h : ∀ i : I, evaluation (B := B) i x = evaluation (B := B) i y) :
    x = y := by
  apply module_inner_ext_right (B := B)
  have he := (mk_denseRange (B := B) (E := E) (I := I)).equalizer
    (CStarModule.continuous_inner.comp (continuous_id.prodMk (continuous_const (y := x))))
    (CStarModule.continuous_inner.comp (continuous_id.prodMk (continuous_const (y := y)))) (by
      funext u
      change ⟪mk (B := B) u, x⟫_(Bᵐᵒᵖ) =
        ⟪mk (B := B) u, y⟫_(Bᵐᵒᵖ)
      rw [mk_inner_right, mk_inner_right]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : E => ⟪u i, v⟫_(Bᵐᵒᵖ)) (h i)))
  intro z
  exact congrFun he z

end IndexedHilbertModule
end BC4lean.KKTheory
