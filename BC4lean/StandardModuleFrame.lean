import BC4lean.StandardCountableCutoff
import BC4lean.StandardCountableGeneration
import BC4lean.CompactModuleOperatorCriterion
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual summable-generator synthesis from the standard Hilbert module

Coefficient creation b ↦ ξb and coefficient inner-product evaluation are a
proved bounded adjoint pair. A family with summable vector norms therefore
defines an absolutely convergent series of coordinate adjointable operators
H_B → E. Its adjoint is the actual convergent coefficient-inner-product column.
Rescaling any countable generating family by nonzero positive geometric
weights produces such a family and preserves its closed coefficient span.
The resulting synthesis operator has dense range. No stabilization or index
theorem is assumed or asserted here.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

omit [StarOrderedRing B] in
/-- Complex scalar multiplication commutes with the right coefficient action. -/
theorem module_op_smul_complex (a : Bᵐᵒᵖ) (c : ℂ) (x : E) :
    a • (c • x) = c • (a • x) := by
  apply module_inner_ext_right (B := B)
  intro y
  simp only [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex, mul_smul_comm]

/-- Creation from the coefficient module by a module vector, with its actual adjoint. -/
def moduleVectorCreation (ξ : E) : AdjointableMap B Bᵐᵒᵖ E where
  toCLM :=
    ({ toFun := fun b => b • ξ
       map_add' := fun b c => module_add_smul b c ξ
       map_smul' := fun c b => module_complex_smul c b ξ } : Bᵐᵒᵖ →ₗ[ℂ] E).mkContinuous
      ‖ξ‖ (fun b => by
        change ‖b • ξ‖ ≤ ‖ξ‖ * ‖b‖
        simpa only [mul_comm] using module_norm_smul_le b ξ)
  adjointCLM := CStarModule.innerSL (A := Bᵐᵒᵖ) ξ
  adjoint_identity b y := by
    change ⟪b • ξ, y⟫_(Bᵐᵒᵖ) = ⟪b, ⟪ξ, y⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ)
    rw [CStarModule.inner_op_smul_left]
    rfl

@[simp] theorem moduleVectorCreation_apply (ξ : E) (b : Bᵐᵒᵖ) :
    moduleVectorCreation ξ b = b • ξ := rfl

@[simp] theorem moduleVectorCreation_adjoint_apply (ξ y : E) :
    (moduleVectorCreation (B := B) ξ).adjoint y = ⟪ξ, y⟫_(Bᵐᵒᵖ) := rfl

/-- Creation has the actual coefficient left-multiplication operator as its adjoint square. -/
theorem moduleVectorCreation_adjoint_comp (ξ : E) :
    (moduleVectorCreation (B := B) ξ).adjoint.comp (moduleVectorCreation ξ) =
      standardLeftMul (MulOpposite.unop ⟪ξ, ξ⟫_(Bᵐᵒᵖ)) := by
  ext b
  change ⟪ξ, b • ξ⟫_(Bᵐᵒᵖ) =
    MulOpposite.op (MulOpposite.unop ⟪ξ, ξ⟫_(Bᵐᵒᵖ) * MulOpposite.unop b)
  rw [CStarModule.inner_op_smul_right]
  rfl

/-- Coefficient creation is compact even when B has no unit. -/
theorem moduleVectorCreation_compact (ξ : E) :
    IsModuleCompact (moduleVectorCreation (B := B) ξ) := by
  apply IsModuleCompact.of_adjoint_comp_self
  rw [moduleVectorCreation_adjoint_comp]
  exact standardLeftMul_mem_moduleCompact _

theorem norm_moduleVectorCreation_le (ξ : E) : ‖moduleVectorCreation (B := B) ξ‖ ≤ ‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ξ)
  intro b
  change ‖b • ξ‖ ≤ ‖ξ‖ * ‖b‖
  simpa only [mul_comm] using module_norm_smul_le b ξ

/-- The n-th row contribution to the synthesis operator on the actual H_B. -/
def standardModuleSynthesisTerm (η : ℕ → E) (n : ℕ) :
    AdjointableMap B (StandardCountableHilbertModule B) E :=
  (moduleVectorCreation (η n)).comp (standardCountableEvaluation n)

@[simp] theorem standardModuleSynthesisTerm_apply (η : ℕ → E) (n : ℕ)
    (x : StandardCountableHilbertModule B) :
    standardModuleSynthesisTerm η n x = standardCountableEvaluation n x • η n := rfl

/-- Each synthesis row is compact by its actual compact coefficient creation. -/
theorem standardModuleSynthesisTerm_compact (η : ℕ → E) (n : ℕ) :
    IsModuleCompact (standardModuleSynthesisTerm (B := B) η n) :=
  (moduleVectorCreation_compact (η n)).comp_right (standardCountableEvaluation n)

theorem norm_standardModuleSynthesisTerm_le (η : ℕ → E) (n : ℕ) :
    ‖standardModuleSynthesisTerm (B := B) η n‖ ≤ ‖η n‖ := by
  calc
    ‖standardModuleSynthesisTerm (B := B) η n‖ ≤
        ‖moduleVectorCreation (B := B) (η n)‖ * ‖standardCountableEvaluation (B := B) n‖ :=
      AdjointableMap.norm_comp_le _ _
    _ ≤ ‖η n‖ * 1 := mul_le_mul (norm_moduleVectorCreation_le _)
      (norm_standardCountableEvaluation_le _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖η n‖ := mul_one _

theorem standardModuleSynthesisTerm_norm_summable (η : ℕ → E)
    (hη : Summable (fun n => ‖η n‖)) :
    Summable (fun n => ‖standardModuleSynthesisTerm (B := B) η n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_standardModuleSynthesisTerm_le η) hη

variable [CompleteSpace E]

theorem standardModuleSynthesisTerm_summable (η : ℕ → E) (hη : Summable (fun n => ‖η n‖)) :
    Summable (standardModuleSynthesisTerm (B := B) η) :=
  (standardModuleSynthesisTerm_norm_summable η hη).of_norm

/-- The actual bounded adjointable synthesis operator is a norm-convergent operator series. -/
def standardModuleSynthesis (η : ℕ → E) : AdjointableMap B (StandardCountableHilbertModule B) E :=
  ∑' n, standardModuleSynthesisTerm η n

theorem standardModuleSynthesis_hasSum (η : ℕ → E) (hη : Summable (fun n => ‖η n‖)) :
    HasSum (standardModuleSynthesisTerm (B := B) η) (standardModuleSynthesis η) :=
  (standardModuleSynthesisTerm_summable η hη).hasSum

/-- The norm-convergent series of compact synthesis rows is genuinely compact. -/
theorem standardModuleSynthesis_compact (η : ℕ → E)
    (hη : Summable (fun n => ‖η n‖)) :
    IsModuleCompact (standardModuleSynthesis (B := B) η) := by
  apply moduleCompact_isClosed.mem_of_tendsto (standardModuleSynthesis_hasSum η hη)
  exact Eventually.of_forall (fun s : Finset ℕ =>
    (moduleCompact B (StandardCountableHilbertModule B) E).sum_mem
      (fun n _ => standardModuleSynthesisTerm_compact η n))

omit [CompleteSpace E] in
theorem norm_standardModuleSynthesis_le (η : ℕ → E) (hη : Summable (fun n => ‖η n‖)) :
    ‖standardModuleSynthesis (B := B) η‖ ≤ ∑' n, ‖η n‖ := by
  calc
    ‖standardModuleSynthesis (B := B) η‖ ≤ ∑' n, ‖standardModuleSynthesisTerm (B := B) η n‖ :=
      norm_tsum_le_tsum_norm (standardModuleSynthesisTerm_norm_summable η hη)
    _ ≤ ∑' n, ‖η n‖ := (standardModuleSynthesisTerm_norm_summable η hη).tsum_le_tsum
      (norm_standardModuleSynthesisTerm_le η) hη

private def standardFrameApplyCLM (x : StandardCountableHilbertModule B) :
    AdjointableMap B (StandardCountableHilbertModule B) E →L[ℂ] E :=
  (ContinuousLinearMap.apply ℂ E x).comp AdjointableMap.toCLMContinuousLinearMap

private def standardFrameAdjointApplyCLM (y : E) :
    AdjointableMap B (StandardCountableHilbertModule B) E →L⋆[ℂ] StandardCountableHilbertModule B :=
  ({ toFun := fun T => T.adjoint y
     map_add' := fun S T => by
       change (S.adjointCLM + T.adjointCLM) y = _
       rfl
     map_smul' := fun c T => by
       change (star c • T.adjointCLM) y = _
       rfl } : AdjointableMap B (StandardCountableHilbertModule B) E →ₗ⋆[ℂ]
         StandardCountableHilbertModule B).mkContinuous ‖y‖ (fun T => by
           calc
             ‖T.adjoint y‖ ≤ ‖T.adjoint.toCLM‖ * ‖y‖ := T.adjoint.norm_apply_le y
             _ = ‖y‖ * ‖T‖ := by rw [AdjointableMap.norm_adjoint_toCLM]; exact mul_comm _ _)

/-- Synthesis applies by the actual convergent coefficient-weighted vector series. -/
theorem standardModuleSynthesis_apply (η : ℕ → E) (hη : Summable (fun n => ‖η n‖))
    (x : StandardCountableHilbertModule B) :
    standardModuleSynthesis η x = ∑' n, standardCountableEvaluation n x • η n :=
  (standardFrameApplyCLM x).map_tsum (standardModuleSynthesisTerm_summable η hη)

/-- The adjoint is the actual H_B sum of coefficient-inner-product coordinates. -/
theorem standardModuleSynthesis_adjoint_apply (η : ℕ → E) (hη : Summable (fun n => ‖η n‖))
    (y : E) :
    (standardModuleSynthesis (B := B) η).adjoint y =
      ∑' n, standardCountableInclusion n ⟪η n, y⟫_(Bᵐᵒᵖ) := by
  have h := (standardFrameAdjointApplyCLM (B := B) y).map_tsum (standardModuleSynthesisTerm_summable η hη)
  change (standardModuleSynthesis (B := B) η).adjoint y =
    ∑' n, (standardModuleSynthesisTerm (B := B) η n).adjoint y at h
  simpa only [
    standardModuleSynthesisTerm, AdjointableMap.adjoint_comp, standardCountableEvaluation,
    AdjointableMap.adjoint_adjoint, AdjointableMap.comp_apply, moduleVectorCreation_adjoint_apply] using h

omit [CompleteSpace E] in
/-- The analysis column itself is summable in the true standard-module norm. -/
theorem standardModuleAnalysis_summable (η : ℕ → E) (hη : Summable (fun n => ‖η n‖)) (y : E) :
    Summable (fun n => standardCountableInclusion (B := B) n ⟪η n, y⟫_(Bᵐᵒᵖ)) := by
  apply (hη.mul_right ‖y‖).of_norm_bounded
  intro n
  rw [standardCountableInclusion_norm]
  exact CStarModule.norm_inner_le E

/-- Evaluation of the synthesis adjoint recovers its coefficient inner products. -/
@[simp] theorem standardModuleSynthesis_evaluation_adjoint (η : ℕ → E)
    (hη : Summable (fun n => ‖η n‖)) (y : E) (n : ℕ) :
    standardCountableEvaluation n ((standardModuleSynthesis (B := B) η).adjoint y) =
      ⟪η n, y⟫_(Bᵐᵒᵖ) := by
  rw [standardModuleSynthesis_adjoint_apply η hη]
  rw [(standardCountableEvaluation n).toCLM.map_tsum (standardModuleAnalysis_summable η hη y)]
  rw [tsum_eq_single n]
  · rw [standardCountableEvaluation_inclusion, if_pos rfl]
  · intro i hi
    rw [standardCountableEvaluation_inclusion, if_neg hi]

/-- The analysis square is an actual convergent positive coefficient series. -/
theorem standardModuleAnalysis_square_hasSum (η : ℕ → E)
    (hη : Summable (fun n => ‖η n‖)) (y : E) :
    HasSum (fun n => ⟪⟪η n, y⟫_(Bᵐᵒᵖ), ⟪η n, y⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ))
      ⟪(standardModuleSynthesis (B := B) η).adjoint y,
        (standardModuleSynthesis (B := B) η).adjoint y⟫_(Bᵐᵒᵖ) := by
  let C : ℝ := ∑' n, ‖η n‖
  have hb (n : ℕ) : ‖η n‖ ≤ C := hη.le_tsum n (fun _ _ => norm_nonneg _)
  have hn : Summable (fun n => ‖⟪⟪η n, y⟫_(Bᵐᵒᵖ), ⟪η n, y⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hη.mul_right (C * ‖y‖ ^ 2))
    intro n
    calc
      ‖⟪⟪η n, y⟫_(Bᵐᵒᵖ), ⟪η n, y⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ)‖ = ‖⟪η n, y⟫_(Bᵐᵒᵖ)‖ ^ 2 :=
        (CStarModule.norm_sq_eq (Bᵐᵒᵖ)).symm
      _ ≤ (‖η n‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (CStarModule.norm_inner_le E) 2
      _ = (‖η n‖ * ‖η n‖) * ‖y‖ ^ 2 := by ring
      _ ≤ (‖η n‖ * C) * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)) (sq_nonneg _)
      _ = ‖η n‖ * (C * ‖y‖ ^ 2) := by ring
  apply (hasSum_iff_tendsto_nat_of_summable_norm hn).mpr
  have hP := standardCountableCutoff_tendsto ((standardModuleSynthesis (B := B) η).adjoint y)
  have hlim := (CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B)).tendsto
    ((standardModuleSynthesis (B := B) η).adjoint y,
      (standardModuleSynthesis (B := B) η).adjoint y) |>.comp (hP.prodMk_nhds hP)
  simpa only [Function.comp_def, standardCountableCutoff_inner_self, standardModuleSynthesis_evaluation_adjoint η hη] using hlim

/-- A single coordinate synthesizes exactly its coefficient multiple of the generator. -/
@[simp] theorem standardModuleSynthesis_inclusion (η : ℕ → E) (hη : Summable (fun n => ‖η n‖))
    (n : ℕ) (b : Bᵐᵒᵖ) :
    standardModuleSynthesis η (standardCountableInclusion n b) = b • η n := by
  rw [standardModuleSynthesis_apply η hη]
  rw [tsum_eq_single n]
  · rw [standardCountableEvaluation_inclusion, if_pos rfl]
  · intro i hi
    have hni : n ≠ i := Ne.symm hi
    rw [standardCountableEvaluation_inclusion, if_neg hni]
    apply module_inner_ext_right (B := B)
    intro z
    simp only [CStarModule.inner_op_smul_right, zero_mul, CStarModule.inner_zero_right]

/-- Every countable generating family has nonzero positive summable rescaling weights. -/
def standardFrameWeight (ξ : ℕ → E) (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n / (1 + ‖ξ n‖)

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem standardFrameWeight_pos (ξ : ℕ → E) (n : ℕ) : 0 < standardFrameWeight ξ n := by
  unfold standardFrameWeight
  positivity

/-- Rescale the given generators without changing their closed coefficient span. -/
def standardFrameRescale (ξ : ℕ → E) (n : ℕ) : E := (standardFrameWeight ξ n : ℂ) • ξ n

omit [CompleteSpace E] in
theorem standardFrameRescale_norm_le (ξ : ℕ → E) (n : ℕ) :
    ‖standardFrameRescale ξ n‖ ≤ ((1 : ℝ) / 2) ^ n := by
  have hnonneg := (standardFrameWeight_pos ξ n).le
  rw [standardFrameRescale, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    standardFrameWeight ξ n * ‖ξ n‖ ≤ standardFrameWeight ξ n * (1 + ‖ξ n‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hnonneg
    _ = ((1 : ℝ) / 2) ^ n := div_mul_cancel₀ _ (by positivity)

omit [CompleteSpace E] in
theorem standardFrameRescale_norm_summable (ξ : ℕ → E) :
    Summable (fun n => ‖standardFrameRescale ξ n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (standardFrameRescale_norm_le ξ)
    summable_geometric_two

/-- The actual synthesis of the rescaled countable generators has dense range. -/
theorem standardFrameSynthesis_denseRange (ξ : ℕ → E)
    (hξ : Dense (moduleGeneratingSpan (B := B) ξ : Set E)) :
    DenseRange (standardModuleSynthesis (B := B) (standardFrameRescale ξ)) := by
  let T := standardModuleSynthesis (B := B) (standardFrameRescale ξ)
  let S := T.toCLM.toLinearMap.range.topologicalClosure
  have hg : moduleGeneratingSpan (B := B) ξ ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨n, b, rfl⟩
    have hc : (standardFrameWeight ξ n : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (standardFrameWeight_pos ξ n))
    have hi : b • standardFrameRescale ξ n ∈ S :=
      T.toCLM.toLinearMap.range.le_topologicalClosure
        ⟨standardCountableInclusion n b,
          standardModuleSynthesis_inclusion (standardFrameRescale ξ)
            (standardFrameRescale_norm_summable ξ) n b⟩
    have he : (standardFrameWeight ξ n : ℂ)⁻¹ • (b • standardFrameRescale ξ n) = b • ξ n := by
      rw [standardFrameRescale, module_op_smul_complex, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [← he]
    exact S.smul_mem _ hi
  have ht : S = ⊤ := by
    apply top_unique
    rw [← (moduleGeneratingSpan_closure_eq_top_iff ξ).mpr hξ]
    exact (moduleGeneratingSpan (B := B) ξ).topologicalClosure_minimal hg
      T.toCLM.toLinearMap.range.isClosed_topologicalClosure
  change Dense (T.toCLM.toLinearMap.range : Set E)
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr ht

/-- A countably generated complete Hilbert module admits actual bounded
adjointable dense-range synthesis from H_B. -/
theorem exists_standardModuleSynthesis_denseRange
    (hE : IsCountablyGeneratedModule B E) :
    ∃ T : AdjointableMap B (StandardCountableHilbertModule B) E, DenseRange T := by
  obtain ⟨ξ, hξ⟩ := hE
  exact ⟨standardModuleSynthesis (standardFrameRescale ξ), standardFrameSynthesis_denseRange ξ hξ⟩

/-- The actual rescaled frame provides compact, adjointable dense-range synthesis. -/
theorem exists_standardModuleCompactSynthesis_denseRange
    (hE : IsCountablyGeneratedModule B E) :
    ∃ T : AdjointableMap B (StandardCountableHilbertModule B) E,
      IsModuleCompact T ∧ DenseRange T := by
  obtain ⟨ξ, hξ⟩ := hE
  exact ⟨standardModuleSynthesis (standardFrameRescale ξ),
    standardModuleSynthesis_compact _ (standardFrameRescale_norm_summable ξ),
    standardFrameSynthesis_denseRange ξ hξ⟩

namespace AdjointableMap

omit [CompleteSpace E] in
/-- Dense range forces injectivity of the actual module adjoint. This implication
uses continuity and the coefficient inner product, without an orthogonal-range
decomposition assumption. -/
theorem injective_adjoint_of_denseRange
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
    [CStarModule Bᵐᵒᵖ F] (T : AdjointableMap B F E) (hT : DenseRange T) :
    Function.Injective T.adjoint := by
  intro x y hxy
  apply module_inner_ext_right (B := B)
  have he := hT.equalizer
    ((CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := E)).comp
      (continuous_id.prodMk (continuous_const (y := x))))
    ((CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := E)).comp
      (continuous_id.prodMk (continuous_const (y := y)))) (by
      funext z
      change ⟪T z, x⟫_(Bᵐᵒᵖ) = ⟪T z, y⟫_(Bᵐᵒᵖ)
      rw [T.adjoint_identity, T.adjoint_identity]
      change ⟪z, T.adjoint x⟫_(Bᵐᵒᵖ) = ⟪z, T.adjoint y⟫_(Bᵐᵒᵖ)
      rw [hxy])
  intro z
  exact congrFun he z

end AdjointableMap

/-- Analysis of the rescaled actual countable generating frame is injective. -/
theorem standardFrameAnalysis_injective (ξ : ℕ → E)
    (hξ : Dense (moduleGeneratingSpan (B := B) ξ : Set E)) :
    Function.Injective (standardModuleSynthesis (B := B) (standardFrameRescale ξ)).adjoint :=
  AdjointableMap.injective_adjoint_of_denseRange _ (standardFrameSynthesis_denseRange ξ hξ)

end BC4lean.KKTheory
