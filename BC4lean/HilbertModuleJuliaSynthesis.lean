import BC4lean.HilbertModuleJuliaRecursion
import BC4lean.CountableModuleSequence

/-! # Actual countable Julia synthesis

The proved coefficient telescoping and strong residual decay realize the Julia
outputs in the genuine countable module sum. Their finite-input linear map
extends continuously to E ⊕ F^∞ and preserves the actual coefficient inner
product. Surjectivity requires the separate finite backward construction.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter UniformSpace
open scoped InnerProductSpace Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The actual output vector of a finite Julia input. -/
def juliaFiniteSynthesis (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) (hDense : DenseRange T) :
    (E × CountableModuleVectors F) →ₗ[ℂ] CountableHilbertModuleSum B F where
  toFun p := countableModuleSequenceSum (B := B) (juliaOutput T p.1 p.2)
  map_add' p q := by
    apply countableModule_ext_eval
    intro i
    rw [map_add]
    change countableModuleEvaluation (B := B) i (countableModuleSequenceSum (B := B)
      (juliaOutput T (p.1 + q.1) (p.2 + q.2))) =
        countableModuleEvaluation (B := B) i (countableModuleSequenceSum (B := B) (juliaOutput T p.1 p.2)) +
        countableModuleEvaluation (B := B) i (countableModuleSequenceSum (B := B) (juliaOutput T q.1 q.2))
    have hsum := countableModuleEvaluation_sequenceSum _
      (juliaOutput_finite_inner_tendsto T hT hDense (p.1 + q.1) (p.1 + q.1) (p.2 + q.2) (p.2 + q.2)) i
    simp only [Finsupp.coe_add] at hsum
    rw [hsum,
      countableModuleEvaluation_sequenceSum _
        (juliaOutput_finite_inner_tendsto T hT hDense p.1 p.1 p.2 p.2),
      countableModuleEvaluation_sequenceSum _
        (juliaOutput_finite_inner_tendsto T hT hDense q.1 q.1 q.2 q.2)]
    exact (juliaOutputLinear T i).map_add (p.1, p.2) (q.1, q.2)
  map_smul' c p := by
    apply countableModule_ext_eval
    intro i
    rw [map_smul]
    change countableModuleEvaluation (B := B) i (countableModuleSequenceSum (B := B)
      (juliaOutput T (c • p.1) (c • p.2))) =
        c • countableModuleEvaluation (B := B) i (countableModuleSequenceSum (B := B) (juliaOutput T p.1 p.2))
    have hsmul := countableModuleEvaluation_sequenceSum _
      (juliaOutput_finite_inner_tendsto T hT hDense (c • p.1) (c • p.1) (c • p.2) (c • p.2)) i
    simp only [Finsupp.coe_smul] at hsmul
    rw [hsmul,
      countableModuleEvaluation_sequenceSum _
        (juliaOutput_finite_inner_tendsto T hT hDense p.1 p.1 p.2 p.2)]
    exact (juliaOutputLinear T i).map_smul c (p.1, p.2)

@[simp] theorem juliaFiniteSynthesis_evaluation (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (e : E) (h : CountableModuleVectors F) (n : ℕ) :
    countableModuleEvaluation (B := B) n (juliaFiniteSynthesis T hT hDense (e, h)) =
      juliaOutput T e h n :=
  countableModuleEvaluation_sequenceSum _ (juliaOutput_finite_inner_tendsto T hT hDense e e h h) n

theorem juliaFiniteSynthesis_inner (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (p q : E × CountableModuleVectors F) :
    ⟪juliaFiniteSynthesis T hT hDense p, juliaFiniteSynthesis T hT hDense q⟫_(Bᵐᵒᵖ) =
      ⟪p.1, q.1⟫_(Bᵐᵒᵖ) + countableModuleFiniteInner (B := B) p.2 q.2 :=
  countableModuleSequenceSum_inner _ _
    (juliaOutput_finite_inner_tendsto T hT hDense p.1 p.1 p.2 p.2)
    (juliaOutput_finite_inner_tendsto T hT hDense q.1 q.1 q.2 q.2)
    (juliaOutput_finite_inner_tendsto T hT hDense p.1 q.1 p.2 q.2)

theorem juliaFiniteSynthesis_norm (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (p : E × CountableModuleVectors F) :
    ‖juliaFiniteSynthesis T hT hDense p‖ =
      Real.sqrt ‖⟪p.1, p.1⟫_(Bᵐᵒᵖ) + countableModuleFiniteInner (B := B) p.2 p.2‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (juliaFiniteSynthesis T hT hDense p), juliaFiniteSynthesis_inner]

def juliaInitialSynthesisCLM (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) (hDense : DenseRange T) :
    E →L[ℂ] CountableHilbertModuleSum B F :=
  ((juliaFiniteSynthesis T hT hDense).comp (LinearMap.inl ℂ E (CountableModuleVectors F))).mkContinuous 1
    (fun e => by
      change ‖juliaFiniteSynthesis T hT hDense (e, 0)‖ ≤ 1 * ‖e‖
      rw [juliaFiniteSynthesis_norm]
      simp only [countableModuleFiniteInner, Finsupp.sum_zero_index, add_zero, one_mul]
      exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) e).symm.le)

def juliaInputSynthesisQuotientLinear (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) : CountableHilbertModulePreSum B F →ₗ[ℂ] CountableHilbertModuleSum B F :=
  (PositiveModuleForm.nullRadical (B := B) (E := CountableModuleVectors F)).liftQ
    ((juliaFiniteSynthesis T hT hDense).comp (LinearMap.inr ℂ E (CountableModuleVectors F)))
    (fun x hx => by
      rw [countableModuleFinite_nullRadical_eq_bot, Submodule.mem_bot] at hx
      simp [hx])

@[simp] theorem juliaInputSynthesisQuotientLinear_mk (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (h : CountableModuleVectors F) :
    juliaInputSynthesisQuotientLinear T hT hDense (positiveModuleQuotientMk (B := B) h) =
      juliaFiniteSynthesis T hT hDense (0, h) := rfl

theorem juliaInputSynthesisQuotientLinear_norm (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (q : CountableHilbertModulePreSum B F) :
    ‖juliaInputSynthesisQuotientLinear T hT hDense q‖ = ‖q‖ := by
  obtain ⟨h, rfl⟩ := positiveModuleQuotientMk_surjective q
  rw [juliaInputSynthesisQuotientLinear_mk, juliaFiniteSynthesis_norm,
    PositiveModuleQuotient.norm_mk]
  simp only [CStarModule.inner_zero_left, zero_add, PositiveModuleForm.formNorm,
    countableModuleFinite_inner]

def juliaInputSynthesisQuotientCLM (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) : CountableHilbertModulePreSum B F →L[ℂ] CountableHilbertModuleSum B F :=
  (juliaInputSynthesisQuotientLinear T hT hDense).mkContinuous 1 (fun q => by
    rw [juliaInputSynthesisQuotientLinear_norm]
    simp only [one_mul, le_refl])

def juliaInputSynthesisCLM (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) (hDense : DenseRange T) :
    CountableHilbertModuleSum B F →L[ℂ] CountableHilbertModuleSum B F :=
  (juliaInputSynthesisQuotientCLM T hT hDense).fromCompletion

@[simp] theorem juliaInputSynthesisCLM_mk (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (h : CountableModuleVectors F) :
    juliaInputSynthesisCLM T hT hDense (countableModuleMk (B := B) h) =
      juliaFiniteSynthesis T hT hDense (0, h) := by
  rw [countableModuleMk_apply]
  change (juliaInputSynthesisQuotientCLM T hT hDense).fromCompletion
    ((positiveModuleQuotientMk (B := B) h) : CountableHilbertModuleSum B F) = _
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- The genuine continuous Julia map E ⊕ F^∞ → F^∞. -/
def juliaCountableSynthesisCLM (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) (hDense : DenseRange T) :
    HilbertModuleSum B E (CountableHilbertModuleSum B F) →L[ℂ] CountableHilbertModuleSum B F :=
  (juliaInitialSynthesisCLM T hT hDense).comp sumFstCLM +
    (juliaInputSynthesisCLM T hT hDense).comp sumSndCLM

@[simp] theorem juliaCountableSynthesisCLM_finite (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (e : E) (h : CountableModuleVectors F) :
    juliaCountableSynthesisCLM T hT hDense (sumMk e (countableModuleMk (B := B) h)) =
      juliaFiniteSynthesis T hT hDense (e, h) := by
  change juliaFiniteSynthesis T hT hDense (e, 0) +
    juliaInputSynthesisCLM T hT hDense (countableModuleMk (B := B) h) = _
  rw [juliaInputSynthesisCLM_mk, ← map_add]
  congr 1
  apply Prod.ext <;> simp

/-- Completion preserves the proved finite-input coefficient inner identity. -/
theorem juliaCountableSynthesisCLM_inner (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (x y : HilbertModuleSum B E (CountableHilbertModuleSum B F)) :
    ⟪juliaCountableSynthesisCLM T hT hDense x,
      juliaCountableSynthesisCLM T hT hDense y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  have hc (e : E) : Continuous (fun h : CountableHilbertModuleSum B F => sumMk (B := B) e h) := by
    have hh : Continuous (fun h : CountableHilbertModuleSum B F =>
        sumInlCLM (B := B) (F := CountableHilbertModuleSum B F) e +
          sumInrCLM (B := B) (E := E) h) :=
      continuous_const.add (sumInrCLM (B := B) (E := E)).continuous
    convert hh using 1
    funext h
    apply Prod.ext
    · change e = e + 0
      exact (add_zero e).symm
    · change h = 0 + h
      exact (zero_add h).symm
  have hh : ∀ h k : CountableHilbertModuleSum B F,
      ⟪juliaCountableSynthesisCLM T hT hDense (sumMk x.fst h),
        juliaCountableSynthesisCLM T hT hDense (sumMk y.fst k)⟫_(Bᵐᵒᵖ) =
        ⟪sumMk (B := B) x.fst h, sumMk y.fst k⟫_(Bᵐᵒᵖ) := by
    intro h k
    refine Completion.induction_on₂ h k ?_ ?_
    · exact isClosed_eq
        ((CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := CountableHilbertModuleSum B F)).comp
          (((juliaCountableSynthesisCLM T hT hDense).continuous.comp
            ((hc x.fst).comp continuous_fst)).prodMk
            ((juliaCountableSynthesisCLM T hT hDense).continuous.comp
              ((hc y.fst).comp continuous_snd))))
        ((CStarModule.continuous_inner (A := Bᵐᵒᵖ)
          (E := HilbertModuleSum B E (CountableHilbertModuleSum B F))).comp
          (((hc x.fst).comp continuous_fst).prodMk ((hc y.fst).comp continuous_snd)))
    · intro q r
      obtain ⟨v, rfl⟩ := positiveModuleQuotientMk_surjective q
      obtain ⟨w, rfl⟩ := positiveModuleQuotientMk_surjective r
      change ⟪juliaCountableSynthesisCLM T hT hDense (sumMk x.fst (countableModuleMk (B := B) v)),
        juliaCountableSynthesisCLM T hT hDense (sumMk y.fst (countableModuleMk (B := B) w))⟫_(Bᵐᵒᵖ) = _
      rw [juliaCountableSynthesisCLM_finite, juliaCountableSynthesisCLM_finite]
      change ⟪juliaFiniteSynthesis T hT hDense (x.fst, v),
        juliaFiniteSynthesis T hT hDense (y.fst, w)⟫_(Bᵐᵒᵖ) =
        ⟪x.fst, y.fst⟫_(Bᵐᵒᵖ) +
          ⟪countableModuleMk (B := B) v, countableModuleMk (B := B) w⟫_(Bᵐᵒᵖ)
      rw [countableModuleMk_inner]
      exact juliaFiniteSynthesis_inner T hT hDense (x.fst, v) (y.fst, w)
  exact hh x.snd y.snd

theorem juliaCountableSynthesisCLM_norm (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (x : HilbertModuleSum B E (CountableHilbertModuleSum B F)) :
    ‖juliaCountableSynthesisCLM T hT hDense x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (juliaCountableSynthesisCLM T hT hDense x), juliaCountableSynthesisCLM_inner]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

end BC4lean.KKTheory
