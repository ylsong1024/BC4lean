import BC4lean.StandardModuleFrameCutoff
import BC4lean.StandardModuleCompactFrame
import BC4lean.HilbertModuleJuliaSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # A constructed strong resolution from dense adjointable synthesis

For a genuinely constructed dense-range synthesis map `T`, set `h = TT*`.
The positive contractions `eₙ(h)` converge strongly to the identity. The proof
does not infer dense range of `TT*` from injectivity, or assume an orthogonal
range decomposition: it proves a quantitative norm bound for `(1-eₙ(h))T`
and then uses the actual dense range of `T`. The square-root band identity
is the operator identity needed for the Parseval frame construction.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardModuleFrameResolutionLocalInstance1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardModuleFrameResolutionLocalInstance2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- Apply the actual scalar resolution to a module endomorphism. -/
def standardFrameOperatorCutoff (h : AdjointableMap B E E) (n : ℕ) :
    AdjointableMap B E E := cfc (standardFrameCutoff n) h

/-- Apply its actual residual to a module endomorphism. -/
def standardFrameOperatorResidual (h : AdjointableMap B E E) (n : ℕ) :
    AdjointableMap B E E := cfc (standardFrameResidual n) h

/-- Apply its actual square-root band to a module endomorphism. -/
def standardFrameOperatorBand (h : AdjointableMap B E E) (n : ℕ) :
    AdjointableMap B E E := cfc (standardFrameBand n) h

/-- Actual spectral-band vectors of the constructed summable synthesis. -/
def standardFrameBandVector (η : ℕ → E) (n m : ℕ) : E :=
  standardFrameOperatorBand
    ((standardModuleSynthesis (B := B) η).comp (standardModuleSynthesis η).adjoint) n (η m)

theorem standardFrameOperatorCutoff_nonneg (h : AdjointableMap B E E) (n : ℕ) :
    0 ≤ standardFrameOperatorCutoff h n :=
  cfc_nonneg (fun t _ => standardFrameCutoff_nonneg n t)

theorem standardFrameOperatorCutoff_le_one (h : AdjointableMap B E E) (n : ℕ) :
    standardFrameOperatorCutoff h n ≤ 1 :=
  cfc_le_one _ _ (fun t _ => standardFrameCutoff_le_one n t)

theorem standardFrameOperatorResidual_nonneg (h : AdjointableMap B E E) (n : ℕ) :
    0 ≤ standardFrameOperatorResidual h n :=
  cfc_nonneg (fun t _ => standardFrameResidual_nonneg n t)

theorem standardFrameOperatorResidual_adjoint (h : AdjointableMap B E E) (n : ℕ) :
    (standardFrameOperatorResidual h n).adjoint = standardFrameOperatorResidual h n :=
  (standardFrameOperatorResidual_nonneg h n).isSelfAdjoint.star_eq

theorem norm_standardFrameOperatorResidual_le_one (h : AdjointableMap B E E) (n : ℕ) :
    ‖standardFrameOperatorResidual h n‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t _
  rw [Real.norm_eq_abs, abs_of_nonneg (standardFrameResidual_nonneg n t)]
  exact standardFrameResidual_le_one n t

theorem one_sub_standardFrameOperatorCutoff (h : AdjointableMap B E E)
    (hh : 0 ≤ h) (n : ℕ) :
    1 - standardFrameOperatorCutoff h n = standardFrameOperatorResidual h n := by
  have hsa := hh.isSelfAdjoint
  change 1 - cfc (standardFrameCutoff n) h = cfc (standardFrameResidual n) h
  calc
    1 - cfc (standardFrameCutoff n) h =
        cfc (fun _ : ℝ => 1) h - cfc (standardFrameCutoff n) h := by
      rw [cfc_const_one ℝ h hsa]
    _ = cfc (fun t : ℝ => 1 - standardFrameCutoff n t) h :=
      (cfc_sub (fun _ : ℝ => 1) (standardFrameCutoff n) h
        continuous_const.continuousOn (continuous_standardFrameCutoff n).continuousOn).symm
    _ = cfc (standardFrameResidual n) h :=
      cfc_congr (fun t _ => one_sub_standardFrameCutoff n t)

/-- The actual CFC band square is exactly the difference of successive contractions. -/
theorem standardFrameOperatorBand_square (h : AdjointableMap B E E)
    (hh : 0 ≤ h) (n : ℕ) :
    standardFrameOperatorBand h n * h * standardFrameOperatorBand h n =
      standardFrameOperatorCutoff h (n + 1) - standardFrameOperatorCutoff h n := by
  have hsa := hh.isSelfAdjoint
  change cfc (standardFrameBand n) h * h * cfc (standardFrameBand n) h =
    cfc (standardFrameCutoff (n + 1)) h - cfc (standardFrameCutoff n) h
  have hb := (continuous_standardFrameBand n).continuousOn (s := spectrum ℝ h)
  have hid := continuous_id.continuousOn (s := spectrum ℝ h)
  have hmul : cfc (fun t : ℝ => standardFrameBand n t * t * standardFrameBand n t) h =
      cfc (standardFrameBand n) h * h * cfc (standardFrameBand n) h := by
    rw [cfc_mul (fun t : ℝ => standardFrameBand n t * t) (standardFrameBand n) h
      (hb.mul hid) hb,
      cfc_mul (standardFrameBand n) (fun t : ℝ => t) h hb hid, cfc_id' ℝ h hsa]
  calc
    cfc (standardFrameBand n) h * h * cfc (standardFrameBand n) h =
        cfc (fun t : ℝ => standardFrameBand n t * t * standardFrameBand n t) h := hmul.symm
    _ = cfc (fun t : ℝ => standardFrameCutoff (n + 1) t - standardFrameCutoff n t) h := by
      apply cfc_congr
      intro t ht
      have ht0 := spectrum_nonneg_of_nonneg hh ht
      calc
        standardFrameBand n t * t * standardFrameBand n t =
            t * standardFrameBand n t ^ 2 := by ring
        _ = standardFrameCutoff (n + 1) t - standardFrameCutoff n t := by
          simpa only [max_eq_right ht0] using standardFrameBand_square n t
    _ = cfc (standardFrameCutoff (n + 1)) h - cfc (standardFrameCutoff n) h :=
      cfc_sub (standardFrameCutoff (n + 1)) (standardFrameCutoff n) h
        (continuous_standardFrameCutoff (n + 1)).continuousOn
        (continuous_standardFrameCutoff n).continuousOn

private theorem standardFrameOperatorResidual_square (h : AdjointableMap B E E)
    (hh : 0 ≤ h) (n : ℕ) :
    standardFrameOperatorResidual h n * h * standardFrameOperatorResidual h n =
      cfc (fun t : ℝ => t * standardFrameResidual n t ^ 2) h := by
  have hsa := hh.isSelfAdjoint
  change cfc (standardFrameResidual n) h * h * cfc (standardFrameResidual n) h = _
  have hR := (continuous_standardFrameResidual n).continuousOn (s := spectrum ℝ h)
  have hid := continuous_id.continuousOn (s := spectrum ℝ h)
  have hmul : cfc (fun t : ℝ => standardFrameResidual n t * t * standardFrameResidual n t) h =
      cfc (standardFrameResidual n) h * h * cfc (standardFrameResidual n) h := by
    rw [cfc_mul (fun t : ℝ => standardFrameResidual n t * t) (standardFrameResidual n) h
      (hR.mul hid) hR,
      cfc_mul (standardFrameResidual n) (fun t : ℝ => t) h hR hid, cfc_id' ℝ h hsa]
  calc
    cfc (standardFrameResidual n) h * h * cfc (standardFrameResidual n) h =
        cfc (fun t : ℝ => standardFrameResidual n t * t * standardFrameResidual n t) h := hmul.symm
    _ = cfc (fun t : ℝ => t * standardFrameResidual n t ^ 2) h := by
      apply cfc_congr
      intro t _
      ring

/-- Residual times a rectangular synthesis operator decays in operator norm.
The estimate uses the genuine rectangular C*-identity and positive spectrum. -/
theorem norm_standardFrameOperatorResidual_comp_le (T : AdjointableMap B F E) (n : ℕ) :
    ‖(standardFrameOperatorResidual (T.comp T.adjoint) (n + 1)).comp T‖ ≤
      Real.sqrt (1 / ((n : ℝ) + 1)) := by
  let h := T.comp T.adjoint
  let R := standardFrameOperatorResidual h (n + 1)
  have hh : 0 ≤ h := (rectangular_adjoint_squares_nonneg T).1
  have hR : R.adjoint = R := standardFrameOperatorResidual_adjoint h (n + 1)
  have heq : (R.comp T).comp (R.comp T).adjoint = R * h * R := by
    rw [AdjointableMap.adjoint_comp, hR]
    ext x
    rfl
  have hsq : ‖R.comp T‖ ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
    change ‖(R.comp T).toCLM‖ ^ 2 ≤ _
    rw [← AdjointableMap.norm_toCLM_self_comp_adjoint]
    change ‖(R.comp T).comp (R.comp T).adjoint‖ ≤ _
    rw [heq, standardFrameOperatorResidual_square h hh (n + 1)]
    apply norm_cfc_le (by positivity)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg hh ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (sq_nonneg _))]
    exact standardFrameResidual_square_error_le n ht0
  calc
    ‖R.comp T‖ = Real.sqrt (‖R.comp T‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) := Real.sqrt_le_sqrt hsq

theorem standardFrameOperatorResidual_comp_tendsto_zero (T : AdjointableMap B F E) :
    Tendsto (fun n => ‖(standardFrameOperatorResidual (T.comp T.adjoint) (n + 1)).comp T‖)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => norm_nonneg _) (norm_standardFrameOperatorResidual_comp_le T)
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hlim

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace F] in
/-- Uniformly contractive operators converge strongly to zero once they do
so in norm on an actual dense adjointable synthesis range. -/
theorem moduleOperators_tendsto_zero_of_denseRange
    (T : AdjointableMap B F E) (hT : DenseRange T)
    (R : ℕ → AdjointableMap B E E) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hRT : Tendsto (fun n => ‖(R n).comp T‖) atTop (𝓝 0)) (y : E) :
    Tendsto (fun n => R n y) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨x, hx⟩ := hT.exists_dist_lt y (half_pos hε)
  have hlim : Tendsto (fun n => ‖(R n).comp T‖ * ‖x‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hRT.mul_const ‖x‖
  have hevent : ∀ᶠ n in atTop, ‖(R n).comp T‖ * ‖x‖ < ε / 2 :=
    (tendsto_order.mp hlim).2 (ε / 2) (half_pos hε)
  filter_upwards [hevent] with n hn
  rw [dist_zero_right]
  have hy : ‖y - T x‖ < ε / 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hx
  calc
    ‖R n y‖ = ‖R n (y - T x) + R n (T x)‖ := by
      rw [← map_add, sub_add_cancel]
    _ ≤ ‖R n (y - T x)‖ + ‖R n (T x)‖ := norm_add_le _ _
    _ ≤ ‖y - T x‖ + ‖(R n).comp T‖ * ‖x‖ := by
      apply add_le_add
      · exact ((R n).norm_apply_le _).trans (by
          simpa only [AdjointableMap.norm_def, one_mul] using
            mul_le_mul_of_nonneg_right (hR n) (norm_nonneg _))
      · exact ((R n).comp T).norm_apply_le x
    _ < ε := by linarith

/-- The constructed residual tends strongly to zero for every dense synthesis map. -/
theorem standardFrameOperatorResidual_tendsto_zero
    (T : AdjointableMap B F E) (hT : DenseRange T) (y : E) :
    Tendsto (fun n => standardFrameOperatorResidual (T.comp T.adjoint) (n + 1) y)
      atTop (𝓝 0) :=
  moduleOperators_tendsto_zero_of_denseRange T hT
    (fun n => standardFrameOperatorResidual (T.comp T.adjoint) (n + 1))
    (fun n => norm_standardFrameOperatorResidual_le_one (T.comp T.adjoint) (n + 1))
    (standardFrameOperatorResidual_comp_tendsto_zero T) y

/-- The genuine positive resolution tends strongly to the actual identity. -/
theorem standardFrameOperatorCutoff_tendsto
    (T : AdjointableMap B F E) (hT : DenseRange T) (y : E) :
    Tendsto (fun n => standardFrameOperatorCutoff (T.comp T.adjoint) (n + 1) y)
      atTop (𝓝 y) := by
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).sub
    (standardFrameOperatorResidual_tendsto_zero T hT y)
  have heq (n : ℕ) : y - standardFrameOperatorResidual (T.comp T.adjoint) (n + 1) y =
      standardFrameOperatorCutoff (T.comp T.adjoint) (n + 1) y := by
    rw [← one_sub_standardFrameOperatorCutoff _ (rectangular_adjoint_squares_nonneg T).1]
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, sub_sub_cancel]
  simpa only [sub_zero, heq] using hlim

end BC4lean.KKTheory
