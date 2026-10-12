import BC4lean.HilbertModuleJuliaSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum

/-! # Strong decay of the actual Julia residual

For contractive T with dense range, D=√(1−TT*) satisfies
‖D^n T‖²≤1/(n+1). The scalar functional-calculus bound follows from a finite
geometric sum and requires no spectral gap. Contractivity of D and density
then imply D^n x→0 for every actual module vector x.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

private theorem julia_scalar_decay_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    r * (1 - r) ^ n ≤ 1 / ((n : ℝ) + 1) := by
  let q := 1 - r
  have hq : 0 ≤ q := sub_nonneg.mpr hr1
  have hq1 : q ≤ 1 := sub_le_self _ hr
  have hs : ((n : ℝ) + 1) * q ^ n ≤ ∑ i ∈ Finset.range (n + 1), q ^ i := by
    calc
      ((n : ℝ) + 1) * q ^ n = ∑ i ∈ Finset.range (n + 1), q ^ n := by simp
      _ ≤ ∑ i ∈ Finset.range (n + 1), q ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_of_le_one hq hq1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hg : r * (∑ i ∈ Finset.range (n + 1), q ^ i) = 1 - q ^ (n + 1) := by
    simpa only [q, sub_sub_cancel] using mul_neg_geom_sum q (n + 1)
  have hm := mul_le_mul_of_nonneg_left hs hr
  have hb : r * (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ 1 := by
    rw [hg]
    exact sub_le_self _ (pow_nonneg hq _)
  apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  change r * q ^ n * ((n : ℝ) + 1) ≤ 1
  nlinarith

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The finite geometric coefficient bound is transported by the actual CFC. -/
theorem norm_positive_contraction_decay (R : A) (hR : 0 ≤ R) (hR1 : R ≤ 1) (n : ℕ) :
    ‖R * (1 - R) ^ n‖ ≤ 1 / ((n : ℝ) + 1) := by
  have hc : cfc (fun r : ℝ => r * (1 - r) ^ n) R = R * (1 - R) ^ n := by
    rw [cfc_mul (fun r : ℝ => r) (fun r : ℝ => (1 - r) ^ n) R
      continuous_id.continuousOn ((continuous_const.sub continuous_id).pow n).continuousOn,
      cfc_id' ℝ R hR.isSelfAdjoint,
      cfc_pow (fun r : ℝ => 1 - r) n R
        (continuous_const.sub continuous_id).continuousOn hR.isSelfAdjoint,
      cfc_sub (fun _ : ℝ => 1) (fun r : ℝ => r) R
        continuous_const.continuousOn continuous_id.continuousOn,
      cfc_const_one ℝ R hR.isSelfAdjoint, cfc_id' ℝ R hR.isSelfAdjoint]
  rw [← hc]
  apply norm_cfc_le (by positivity)
  intro r hr
  have hr0 : 0 ≤ r := spectrum_nonneg_of_nonneg hR hr
  have hr1 : r ≤ 1 := (CFC.le_one_iff (R := ℝ) R hR.isSelfAdjoint).mp hR1 r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr0 (pow_nonneg (sub_nonneg.mpr hr1) _))]
  exact julia_scalar_decay_bound r hr0 hr1 n

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardHilbertModuleJuliaDecayLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardHilbertModuleJuliaDecayLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance standardHilbertModuleJuliaDecayLocalInstance03 : PartialOrder (AdjointableMap B F F) := CStarAlgebra.spectralOrder _
local instance standardHilbertModuleJuliaDecayLocalInstance04 : StarOrderedRing (AdjointableMap B F F) := CStarAlgebra.spectralOrderedRing _

theorem norm_juliaTargetDefect_le (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    ‖juliaTargetDefect T‖ ≤ 1 := by
  have hDsq : juliaTargetDefect T * juliaTargetDefect T = 1 - T.comp T.adjoint :=
    CFC.sqrt_mul_sqrt_self _ (one_sub_self_comp_adjoint_nonneg T hT)
  have hn : ‖1 - T.comp T.adjoint‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (one_sub_self_comp_adjoint_nonneg T hT)).mpr
      (sub_le_self _ (rectangular_adjoint_squares_nonneg T).1)
  rw [← hDsq, (juliaTargetDefect_nonneg T).isSelfAdjoint.norm_mul_self] at hn
  nlinarith [norm_nonneg (juliaTargetDefect T)]

/-- The exact rectangular C*-identity reduces the Julia power bound to R(1−R)^n. -/
theorem juliaTargetDefect_power_comp_norm_sq (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) (n : ℕ) :
    ‖(juliaTargetDefect T ^ n).comp T‖ ^ 2 =
      ‖(T.comp T.adjoint) * (1 - T.comp T.adjoint) ^ n‖ := by
  let D := juliaTargetDefect T
  let R := T.comp T.adjoint
  have hDsq : D * D = 1 - R := CFC.sqrt_mul_sqrt_self _ (one_sub_self_comp_adjoint_nonneg T hT)
  have hR : R = 1 - D * D := by rw [hDsq]; abel
  have hcomm : Commute D R := by
    rw [hR]
    change D * (1 - D * D) = (1 - D * D) * D
    noncomm_ring
  have hstar : (D ^ n).adjoint = D ^ n := by
    change star (D ^ n) = D ^ n
    rw [star_pow, (juliaTargetDefect_nonneg T).isSelfAdjoint.star_eq]
  have he : ((D ^ n).comp T).comp ((D ^ n).comp T).adjoint = D ^ n * R * D ^ n := by
    rw [AdjointableMap.adjoint_comp, hstar]
    ext x
    rfl
  have hp : D ^ n * R * D ^ n = R * (1 - R) ^ n := by
    rw [(hcomm.pow_left n).eq, mul_assoc, ← pow_add, ← two_mul n, pow_mul, pow_two, hDsq]
  calc
    ‖(juliaTargetDefect T ^ n).comp T‖ ^ 2 =
        ‖((D ^ n).comp T).comp ((D ^ n).comp T).adjoint‖ :=
      (AdjointableMap.norm_toCLM_self_comp_adjoint ((D ^ n).comp T)).symm
    _ = ‖R * (1 - R) ^ n‖ := by rw [he, hp]

theorem juliaTargetDefect_power_comp_norm_sq_le (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) (n : ℕ) :
    ‖(juliaTargetDefect T ^ n).comp T‖ ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
  rw [juliaTargetDefect_power_comp_norm_sq T hT]
  apply norm_positive_contraction_decay _ (rectangular_adjoint_squares_nonneg T).1
  exact sub_nonneg.mp (one_sub_self_comp_adjoint_nonneg T hT)

theorem juliaTargetDefect_power_comp_norm_tendsto (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    Tendsto (fun n : ℕ => ‖(juliaTargetDefect T ^ n).comp T‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => ‖(juliaTargetDefect T ^ n).comp T‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (juliaTargetDefect_power_comp_norm_sq_le T hT)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr

theorem juliaTargetDefect_power_norm_apply_le (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (n : ℕ) (x : E) : ‖(juliaTargetDefect T ^ n) x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp only [pow_zero, AdjointableMap.one_apply, le_refl]
  | succ n ih =>
    rw [pow_succ', AdjointableMap.mul_apply]
    calc
      ‖juliaTargetDefect T ((juliaTargetDefect T ^ n) x)‖ ≤
          ‖juliaTargetDefect T‖ * ‖(juliaTargetDefect T ^ n) x‖ :=
        (juliaTargetDefect T).norm_apply_le _
      _ ≤ 1 * ‖x‖ := mul_le_mul (norm_juliaTargetDefect_le T hT) ih (norm_nonneg _) zero_le_one
      _ = ‖x‖ := one_mul _

/-- Actual Julia residual powers converge strongly to zero on every module vector. -/
theorem juliaTargetDefect_power_tendsto_zero (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (x : E) :
    Tendsto (fun n : ℕ => (juliaTargetDefect T ^ n) x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨z, hz⟩ := Metric.mem_closure_range_iff.mp (hDense x) (ε / 2) (by positivity)
  have hn : Tendsto (fun n : ℕ => ‖(juliaTargetDefect T ^ n).comp T‖ * ‖z‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using (juliaTargetDefect_power_comp_norm_tendsto T hT).mul_const ‖z‖
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds (by positivity : 0 < ε / 2)))
  refine ⟨N, ?_⟩
  intro n hnN
  rw [dist_zero_right]
  calc
    ‖(juliaTargetDefect T ^ n) x‖ =
        ‖(juliaTargetDefect T ^ n) (x - T z) + (juliaTargetDefect T ^ n) (T z)‖ := by
      rw [(juliaTargetDefect T ^ n).toCLM.map_sub, sub_add_cancel]
    _ ≤ ‖(juliaTargetDefect T ^ n) (x - T z)‖ + ‖(juliaTargetDefect T ^ n) (T z)‖ := norm_add_le _ _
    _ ≤ ‖x - T z‖ + ‖(juliaTargetDefect T ^ n).comp T‖ * ‖z‖ :=
      add_le_add (juliaTargetDefect_power_norm_apply_le T hT n _) (((juliaTargetDefect T ^ n).comp T).norm_apply_le z)
    _ < ε := by
      have hsmall := hN n hnN
      rw [dist_eq_norm] at hz
      linarith

end BC4lean.KKTheory
