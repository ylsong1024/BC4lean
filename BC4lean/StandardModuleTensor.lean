import BC4lean.ModuleTensorInner
import BC4lean.InteriorModuleTensor
import BC4lean.HilbertModuleEquiv
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # The standard-module tensor and its actual completed essential range

For the standard right module B_B, the balanced tensor has an actual linear
evaluation `x ⊗ y ↦ φ(x)y`.  Its descended coefficient form is the pullback of
the existing Hilbert-module inner product on F.  Hence positivity on every
algebraic tensor, and identification of the null space, are proved in this
specific case, including nonunital B and degenerate representations. Evaluation
then descends to the constructed separated tensor and extends isometrically to
the actual completed interior tensor. Its range is precisely the closed complex
span of `φ(B)F`, with the entire coefficient-valued inner product preserved.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B C F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]

/-- The bilinear evaluation of a standard-module elementary tensor. -/
def standardModuleTensorEvaluationBilinear
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) : Bᵐᵒᵖ →ₗ[ℂ] F →ₗ[ℂ] F where
  toFun x := (φ (MulOpposite.unop x)).toCLM.toLinearMap
  map_add' x z := by
    ext y
    change φ (MulOpposite.unop (x + z)) y =
      φ (MulOpposite.unop x) y + φ (MulOpposite.unop z) y
    rw [MulOpposite.unop_add, map_add]
    rfl
  map_smul' c x := by
    ext y
    change φ (MulOpposite.unop (c • x)) y = c • φ (MulOpposite.unop x) y
    rw [MulOpposite.unop_smul, map_smul]
    rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- Standard-module evaluation satisfies the genuine coefficient-balancing
identity. -/
theorem standardModuleTensorEvaluationBilinear_balance
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (x : Bᵐᵒᵖ) (y : F) :
    standardModuleTensorEvaluationBilinear φ (MulOpposite.op b • x) y =
      standardModuleTensorEvaluationBilinear φ x (φ b y) := by
  change φ (MulOpposite.unop (MulOpposite.op b * x)) y = φ (MulOpposite.unop x) (φ b y)
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op, map_mul, AdjointableMap.mul_apply]

/-- Evaluation on the actual balanced algebraic tensor quotient. -/
def standardModuleTensorEvaluation (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    BalancedModuleTensor (E := Bᵐᵒᵖ) φ →ₗ[ℂ] F :=
  moduleTensorLift φ (standardModuleTensorEvaluationBilinear φ)
    (standardModuleTensorEvaluationBilinear_balance φ)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardModuleTensorEvaluation_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : Bᵐᵒᵖ) (y : F) :
    standardModuleTensorEvaluation φ (moduleTensorMk φ x y) = φ (MulOpposite.unop x) y := rfl

/-- In the standard-module case, the entire descended form is the pullback of
the actual coefficient-valued inner product on F. -/
theorem moduleTensorInner_standard_eq
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u v : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :
    moduleTensorInner φ u v =
      ⟪standardModuleTensorEvaluation φ u, standardModuleTensorEvaluation φ v⟫_(Cᵐᵒᵖ) := by
  revert v
  refine moduleTensor_induction φ u ?_ ?_ ?_
  · intro v
    simp
  · intro x y v
    refine moduleTensor_induction φ v ?_ ?_ ?_
    · simp
    · intro x' y'
      change ⟪y, φ (star (MulOpposite.unop x) * MulOpposite.unop x') y'⟫_(Cᵐᵒᵖ) =
        ⟪φ (MulOpposite.unop x) y, φ (MulOpposite.unop x') y'⟫_(Cᵐᵒᵖ)
      rw [map_mul, map_star]
      exact ((φ (MulOpposite.unop x)).adjoint_identity y
        (φ (MulOpposite.unop x') y')).symm
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hw]

/-- Positivity is proved for every standard-module balanced tensor, rather
than assumed as part of a proposed tensor-product structure. -/
theorem moduleTensorInner_standard_self_nonneg
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) : 0 ≤ moduleTensorInner φ u u := by
  rw [moduleTensorInner_standard_eq]
  exact CStarModule.inner_self_nonneg

/-- The null vectors in the standard-module balanced tensor are exactly the
kernel of its actual evaluation map. -/
theorem moduleTensorInner_standard_self_eq_zero_iff
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :
    moduleTensorInner φ u u = 0 ↔ standardModuleTensorEvaluation φ u = 0 := by
  rw [moduleTensorInner_standard_eq]
  exact CStarModule.inner_self

/-- An actual seminorm on the standard-module balanced tensor, obtained from
its evaluation in F. It retains null vectors until a separated quotient is
constructed. -/
def standardModuleTensorSeminorm (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    Seminorm ℂ (BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :=
  (normSeminorm ℂ F).comp (standardModuleTensorEvaluation φ)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardModuleTensorSeminorm_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :
    standardModuleTensorSeminorm φ u = ‖standardModuleTensorEvaluation φ u‖ := rfl

/-- The constructed seminorm agrees with the coefficient-valued form. -/
theorem standardModuleTensorSeminorm_sq
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :
    (standardModuleTensorSeminorm φ u) ^ 2 = ‖moduleTensorInner φ u u‖ := by
  rw [standardModuleTensorSeminorm_apply, moduleTensorInner_standard_eq]
  exact norm_sq_eq (Cᵐᵒᵖ)

/-- The null space of this seminorm is exactly the null space of the form. -/
theorem standardModuleTensorSeminorm_eq_zero_iff
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :
    standardModuleTensorSeminorm φ u = 0 ↔ moduleTensorInner φ u u = 0 := by
  rw [standardModuleTensorSeminorm_apply]
  exact norm_eq_zero.trans (moduleTensorInner_standard_self_eq_zero_iff φ u).symm

omit [PartialOrder B] [StarOrderedRing B] in
/-- The actual standard-module tensor seminorm satisfies the elementary
cross-norm bound. -/
theorem standardModuleTensorSeminorm_mk_le [StarOrderedRing C] [CompleteSpace F]
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : Bᵐᵒᵖ) (y : F) :
    standardModuleTensorSeminorm φ (moduleTensorMk φ x y) ≤ ‖x‖ * ‖y‖ := by
  rw [standardModuleTensorSeminorm_apply, standardModuleTensorEvaluation_mk]
  calc
    ‖φ (MulOpposite.unop x) y‖ ≤ ‖(φ (MulOpposite.unop x)).toCLM‖ * ‖y‖ :=
      AdjointableMap.norm_apply_le _ _
    _ ≤ ‖MulOpposite.unop x‖ * ‖y‖ :=
      mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le φ (MulOpposite.unop x))
        (_root_.norm_nonneg y)
    _ = ‖x‖ * ‖y‖ := by rw [MulOpposite.norm_unop]

section CompletionIdentification

variable [StarOrderedRing C] [CompleteSpace F]

/-- Evaluation descends through the actual null quotient, because its kernel
is exactly the null space of the standard-module tensor form. -/
def standardPreModuleTensorEvaluationLinear
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    PreHilbertModuleTensor (E := Bᵐᵒᵖ) φ →ₗ[ℂ] F :=
  (moduleTensorNull φ).liftQ (standardModuleTensorEvaluation φ) (by
    intro u hu
    exact (moduleTensorInner_standard_self_eq_zero_iff φ u).mp
      ((mem_moduleTensorNull_iff φ u).mp hu))

@[simp] theorem standardPreModuleTensorEvaluationLinear_mkQ
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :
    standardPreModuleTensorEvaluationLinear φ ((moduleTensorNull φ).mkQ u) =
      standardModuleTensorEvaluation φ u := rfl

/-- The separated evaluation preserves the full coefficient-valued pairing. -/
theorem standardPreModuleTensorEvaluationLinear_inner
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u v : PreHilbertModuleTensor (E := Bᵐᵒᵖ) φ) :
    ⟪standardPreModuleTensorEvaluationLinear φ u,
      standardPreModuleTensorEvaluationLinear φ v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (moduleTensorInner_standard_eq φ u v).symm

/-- Standard-module evaluation on the genuine separated tensor is isometric. -/
def standardPreModuleTensorEvaluation
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    PreHilbertModuleTensor (E := Bᵐᵒᵖ) φ →ₗᵢ[ℂ] F where
  toLinearMap := standardPreModuleTensorEvaluationLinear φ
  norm_map' u := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ),
      standardPreModuleTensorEvaluationLinear_inner,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)]

@[simp] theorem standardPreModuleTensorEvaluation_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : Bᵐᵒᵖ) (y : F) :
    standardPreModuleTensorEvaluation φ (preModuleTensorMk φ x y) =
      φ (MulOpposite.unop x) y := rfl

/-- The bounded evaluation extends to the actual completed interior tensor. -/
def standardInteriorModuleTensorEvaluationCLM
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    InteriorModuleTensor (E := Bᵐᵒᵖ) φ →L[ℂ] F :=
  (standardPreModuleTensorEvaluation φ).toContinuousLinearMap.fromCompletion

@[simp] theorem standardInteriorModuleTensorEvaluationCLM_coe
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : PreHilbertModuleTensor (E := Bᵐᵒᵖ) φ) :
    standardInteriorModuleTensorEvaluationCLM φ
      (moduleTensorToCompletion φ u) = standardPreModuleTensorEvaluation φ u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem standardInteriorModuleTensorEvaluationCLM_norm
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    ‖standardInteriorModuleTensorEvaluationCLM φ u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    change ‖standardInteriorModuleTensorEvaluationCLM φ (moduleTensorToCompletion φ u)‖ =
      ‖moduleTensorToCompletion φ u‖
    rw [standardInteriorModuleTensorEvaluationCLM_coe,
      (standardPreModuleTensorEvaluation φ).norm_map, (moduleTensorToCompletion φ).norm_map]

/-- The genuine standard-module interior tensor embeds isometrically in F. -/
def standardInteriorModuleTensorEvaluation
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    InteriorModuleTensor (E := Bᵐᵒᵖ) φ →ₗᵢ[ℂ] F where
  toLinearMap := (standardInteriorModuleTensorEvaluationCLM φ).toLinearMap
  norm_map' := standardInteriorModuleTensorEvaluationCLM_norm φ

@[simp] theorem standardInteriorModuleTensorEvaluation_coe
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : PreHilbertModuleTensor (E := Bᵐᵒᵖ) φ) :
    standardInteriorModuleTensorEvaluation φ (moduleTensorToCompletion φ u) =
      standardPreModuleTensorEvaluation φ u :=
  standardInteriorModuleTensorEvaluationCLM_coe φ u

@[simp] theorem standardInteriorModuleTensorEvaluation_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : Bᵐᵒᵖ) (y : F) :
    standardInteriorModuleTensorEvaluation φ (interiorModuleTensorMk φ x y) =
      φ (MulOpposite.unop x) y :=
  (standardInteriorModuleTensorEvaluation_coe φ _).trans
    (standardPreModuleTensorEvaluation_mk φ x y)

/-- Completion preserves the entire coefficient-valued inner product. -/
theorem standardInteriorModuleTensorEvaluation_inner
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u v : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    ⟪standardInteriorModuleTensorEvaluation φ u,
      standardInteriorModuleTensorEvaluation φ v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    change ⟪standardInteriorModuleTensorEvaluation φ (moduleTensorToCompletion φ u),
      standardInteriorModuleTensorEvaluation φ (moduleTensorToCompletion φ v)⟫_(Cᵐᵒᵖ) =
      ⟪moduleTensorToCompletion φ u, moduleTensorToCompletion φ v⟫_(Cᵐᵒᵖ)
    rw [standardInteriorModuleTensorEvaluation_coe, standardInteriorModuleTensorEvaluation_coe]
    exact (standardPreModuleTensorEvaluationLinear_inner φ u v).trans
      (hilbertModuleToCompletion_inner u v).symm

/-- Preservation of the coefficient pairing forces the actual right action
to commute with evaluation, even when evaluation is not onto F. -/
@[simp] theorem standardInteriorModuleTensorEvaluation_op_smul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ)
    (u : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    standardInteriorModuleTensorEvaluation φ (a • u) =
      a • standardInteriorModuleTensorEvaluation φ u := by
  apply sub_eq_zero.mp
  apply (CStarModule.inner_self (A := Cᵐᵒᵖ)).mp
  simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
    standardInteriorModuleTensorEvaluation_inner]
  noncomm_ring [CStarModule.inner_op_smul_left
      (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := Bᵐᵒᵖ) φ),
    CStarModule.inner_op_smul_right
      (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := Bᵐᵒᵖ) φ)]

/-- The essential range is the closed complex span of the actual vectors
φ(b)y. It may be a proper submodule for a degenerate representation. -/
def moduleEssentialRange (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) : Submodule ℂ F :=
  (Submodule.span ℂ (Set.range fun p : B × F => φ p.1 p.2)).topologicalClosure

/-- Every completed standard tensor evaluates into the essential range. -/
theorem standardInteriorModuleTensorEvaluation_mem_essentialRange
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    standardInteriorModuleTensorEvaluation φ u ∈ moduleEssentialRange φ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp =>
    exact (Submodule.isClosed_topologicalClosure _).preimage
      (standardInteriorModuleTensorEvaluation φ).continuous
  | ih u =>
    change standardInteriorModuleTensorEvaluation φ (moduleTensorToCompletion φ u) ∈ _
    rw [standardInteriorModuleTensorEvaluation_coe]
    refine preModuleTensor_induction φ u ?_ ?_ ?_
    · simpa only [map_zero] using (moduleEssentialRange φ).zero_mem
    · intro x y
      rw [standardPreModuleTensorEvaluation_mk]
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨(MulOpposite.unop x, y), rfl⟩)
    · intro v w hv hw
      simpa only [map_add] using (moduleEssentialRange φ).add_mem hv hw

/-- The range is exactly the essential range, including for nonunital B and
degenerate φ. Completeness closes the range of the constructed isometry. -/
theorem standardInteriorModuleTensorEvaluation_range
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    LinearMap.range (standardInteriorModuleTensorEvaluation φ).toLinearMap =
      moduleEssentialRange φ := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact standardInteriorModuleTensorEvaluation_mem_essentialRange φ u
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨b, y⟩, rfl⟩
      exact ⟨interiorModuleTensorMk φ (MulOpposite.op b) y,
        standardInteriorModuleTensorEvaluation_mk φ (MulOpposite.op b) y⟩
    · exact (standardInteriorModuleTensorEvaluation φ).isometry.isUniformInducing.isComplete_range.isClosed

/-- The actual essential range is invariant under the ambient right C-action. -/
theorem moduleEssentialRange_op_smul_mem
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) {y : F}
    (hy : y ∈ moduleEssentialRange φ) : a • y ∈ moduleEssentialRange φ := by
  rw [← standardInteriorModuleTensorEvaluation_range] at hy ⊢
  obtain ⟨u, rfl⟩ := hy
  exact ⟨a • u, standardInteriorModuleTensorEvaluation_op_smul φ a u⟩

/-- The essential range carries the actual restricted right coefficient action. -/
instance moduleEssentialRangeSMul (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    SMul Cᵐᵒᵖ (moduleEssentialRange φ) where
  smul a y := ⟨a • (y : F), moduleEssentialRange_op_smul_mem φ a y.property⟩

@[simp] theorem moduleEssentialRange_coe_op_smul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) (y : moduleEssentialRange φ) :
    ((a • y : moduleEssentialRange φ) : F) = a • (y : F) := rfl

/-- The restricted coefficient-valued inner product gives the genuine
Hilbert-module structure on the essential range. -/
instance moduleEssentialRangeCStarModule (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    CStarModule Cᵐᵒᵖ (moduleEssentialRange φ) where
  inner x y := ⟪(x : F), (y : F)⟫_(Cᵐᵒᵖ)
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro h
      apply Subtype.ext
      exact CStarModule.inner_self.mp h
    · intro h
      rw [h]
      exact CStarModule.inner_zero_left
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner x y := CStarModule.star_inner (x : F) (y : F)
  norm_eq_sqrt_norm_inner_self x :=
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) (x : F)

@[simp] theorem moduleEssentialRange_inner
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x y : moduleEssentialRange φ) :
    ⟪x, y⟫_(Cᵐᵒᵖ) = ⟪(x : F), (y : F)⟫_(Cᵐᵒᵖ) := rfl

/-- The essential range is complete because it is closed in the complete F. -/
instance moduleEssentialRangeCompleteSpace (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    CompleteSpace (moduleEssentialRange φ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The completed standard-module tensor is linearly isometrically equivalent
to the essential range; surjectivity onto all of F is not required. -/
def standardInteriorModuleTensorEquivEssential
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    InteriorModuleTensor (E := Bᵐᵒᵖ) φ ≃ₗᵢ[ℂ] moduleEssentialRange φ :=
  (standardInteriorModuleTensorEvaluation φ).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (standardInteriorModuleTensorEvaluation_range φ))

@[simp] theorem standardInteriorModuleTensorEquivEssential_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    (standardInteriorModuleTensorEquivEssential φ u : F) =
      standardInteriorModuleTensorEvaluation φ u := by
  simp [standardInteriorModuleTensorEquivEssential]

/-- The standard-module interior tensor is genuinely unitarily equivalent to
the complete essential Hilbert module of the possibly degenerate left action. -/
def standardInteriorModuleTensorHilbertEquiv
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    HilbertModuleEquiv C (InteriorModuleTensor (E := Bᵐᵒᵖ) φ) (moduleEssentialRange φ) where
  linearIsometryEquiv := standardInteriorModuleTensorEquivEssential φ
  inner_map u v := by
    rw [moduleEssentialRange_inner, standardInteriorModuleTensorEquivEssential_apply,
      standardInteriorModuleTensorEquivEssential_apply]
    exact standardInteriorModuleTensorEvaluation_inner φ u v

end CompletionIdentification

end BC4lean.KKTheory
