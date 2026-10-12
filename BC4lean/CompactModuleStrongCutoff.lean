import BC4lean.CompactModuleOperator
import BC4lean.StandardCountableCutoff
import Mathlib.Tactic.NoncommRing

/-! # Operator-norm cutoff approximation of genuine compact module maps

The finite coordinate projections on H_B need not be compact when B is
nonunital. Their contraction bound and strong convergence nevertheless imply
operator-norm convergence after composition with a compact module map. The
proof starts with the actual rank-one span and then uses its norm closure.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped InnerProductSpace Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

private theorem moduleRankOne_sub_first (x z : F) (y : E) :
    moduleRankOne (B := B) x y - moduleRankOne z y = moduleRankOne (x - z) y := by
  ext w
  simp only [AdjointableMap.coe_sub_apply, moduleRankOne_apply]
  apply module_inner_ext_right (B := B)
  intro v
  simp only [CStarModule.inner_sub_right, CStarModule.inner_op_smul_right, mul_sub]

private theorem moduleRankOne_tendsto_first {x : ℕ → F} {z : F}
    (hx : Tendsto x atTop (𝓝 z)) (y : E) :
    Tendsto (fun n => moduleRankOne (B := B) (x n) y) atTop (𝓝 (moduleRankOne z y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (n : ℕ) :
      ‖moduleRankOne (B := B) (x n) y - moduleRankOne z y‖ ≤ ‖x n - z‖ * ‖y‖ := by
    rw [moduleRankOne_sub_first]
    exact moduleRankOne_norm_le _ _
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  simpa only [zero_mul] using (tendsto_iff_norm_sub_tendsto_zero.mp hx).mul_const ‖y‖

private theorem moduleFiniteRank_tendsto_comp_left
    (U : ℕ → AdjointableMap B F F)
    (hStrong : ∀ x : F, Tendsto (fun n => U n x) atTop (𝓝 x))
    {T : AdjointableMap B E F} (hT : T ∈ moduleFiniteRank B E F) :
    Tendsto (fun n => (U n).comp T) atTop (𝓝 T) := by
  change Tendsto (fun n => AdjointableMap.compLeftContinuousLinearMap (U n) T) atTop (𝓝 T)
  induction hT using Submodule.span_induction with
  | mem T hT =>
    rcases hT with ⟨⟨x, y⟩, rfl⟩
    simpa only [AdjointableMap.compLeftContinuousLinearMap_apply, comp_moduleRankOne] using
      moduleRankOne_tendsto_first (hStrong x) y
  | zero =>
    simpa only [map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : AdjointableMap B E F)) atTop (𝓝 0))
  | add S T _ _ hS hT =>
    simpa only [map_add] using hS.add hT
  | smul c T _ hT =>
    simpa only [map_smul] using hT.const_smul c

/-- Strongly convergent contractions converge in operator norm on the left
of every genuinely compact rectangular Hilbert-module map. -/
theorem isModuleCompact_tendsto_comp_left_of_strong_contractions
    (U : ℕ → AdjointableMap B F F)
    (hNorm : ∀ n, ‖U n‖ ≤ 1)
    (hStrong : ∀ x : F, Tendsto (fun n => U n x) atTop (𝓝 x))
    {T : AdjointableMap B E F} (hT : IsModuleCompact T) :
    Tendsto (fun n => (U n).comp T) atTop (𝓝 T) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨S, hS, hTS⟩ := (mem_moduleCompact_iff_approx T).mp hT (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (moduleFiniteRank_tendsto_comp_left U hStrong hS) (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hsmall : ‖(U n).comp S - S‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN n hn
  have hexpand : (U n).comp T - T =
      (U n).comp (T - S) + ((U n).comp S - S) + (S - T) := by
    ext x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.comp_apply]
    rw [(U n).toCLM.map_sub]
    abel
  have hcontract : ‖(U n).comp (T - S)‖ ≤ ‖T - S‖ := by
    calc
      ‖(U n).comp (T - S)‖ ≤ ‖U n‖ * ‖T - S‖ := AdjointableMap.norm_comp_le _ _
      _ ≤ 1 * ‖T - S‖ := mul_le_mul_of_nonneg_right (hNorm n) (norm_nonneg _)
      _ = ‖T - S‖ := one_mul _
  rw [dist_eq_norm, hexpand]
  calc
    ‖(U n).comp (T - S) + ((U n).comp S - S) + (S - T)‖ ≤
        ‖(U n).comp (T - S)‖ + ‖(U n).comp S - S‖ + ‖S - T‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖T - S‖ + ‖(U n).comp S - S‖ + ‖T - S‖ := by
      rw [norm_sub_rev S T]
      exact add_le_add (add_le_add hcontract (le_refl _)) (le_refl _)
    _ < ε := by linarith

/-- Taking actual adjoints gives right operator-norm convergence for a strongly
convergent sequence of selfadjoint contractions. -/
theorem isModuleCompact_tendsto_comp_right_of_strong_selfadjoint_contractions
    (U : ℕ → AdjointableMap B E E)
    (hNorm : ∀ n, ‖U n‖ ≤ 1) (hSelf : ∀ n, (U n).adjoint = U n)
    (hStrong : ∀ x : E, Tendsto (fun n => U n x) atTop (𝓝 x))
    {T : AdjointableMap B E F} (hT : IsModuleCompact T) :
    Tendsto (fun n => T.comp (U n)) atTop (𝓝 T) := by
  have hh := (AdjointableMap.adjointContinuousLinearMap (B := B) (E := F) (F := E)).continuous.tendsto
    T.adjoint
  simpa only [Function.comp_def, AdjointableMap.adjointContinuousLinearMap_apply,
    AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint, hSelf] using
      hh.comp (isModuleCompact_tendsto_comp_left_of_strong_contractions U hNorm hStrong hT.adjoint)

/-- Strongly convergent selfadjoint contractions compress every genuine compact
endomorphism in operator norm. -/
theorem isModuleCompact_tendsto_sandwich_of_strong_selfadjoint_contractions
    (U : ℕ → AdjointableMap B E E)
    (hNorm : ∀ n, ‖U n‖ ≤ 1) (hSelf : ∀ n, (U n).adjoint = U n)
    (hStrong : ∀ x : E, Tendsto (fun n => U n x) atTop (𝓝 x))
    {T : AdjointableMap B E E} (hT : IsModuleCompact T) :
    Tendsto (fun n => U n * T * U n) atTop (𝓝 T) := by
  have hleft := tendsto_iff_norm_sub_tendsto_zero.mp
    (isModuleCompact_tendsto_comp_left_of_strong_contractions U hNorm hStrong hT)
  have hright := tendsto_iff_norm_sub_tendsto_zero.mp
    (isModuleCompact_tendsto_comp_right_of_strong_selfadjoint_contractions U hNorm hSelf hStrong hT)
  change Tendsto (fun n => ‖U n * T - T‖) atTop (𝓝 0) at hleft
  change Tendsto (fun n => ‖T * U n - T‖) atTop (𝓝 0) at hright
  have hbound (n : ℕ) :
      ‖U n * T * U n - T‖ ≤ ‖T * U n - T‖ + ‖U n * T - T‖ := by
    have hexpand : U n * T * U n - T = U n * (T * U n - T) + (U n * T - T) := by
      noncomm_ring
    rw [hexpand]
    calc
      ‖U n * (T * U n - T) + (U n * T - T)‖ ≤
          ‖U n * (T * U n - T)‖ + ‖U n * T - T‖ := norm_add_le _ _
      _ ≤ ‖U n‖ * ‖T * U n - T‖ + ‖U n * T - T‖ :=
        add_le_add (norm_mul_le _ _) (le_refl _)
      _ ≤ 1 * ‖T * U n - T‖ + ‖U n * T - T‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (hNorm n) (norm_nonneg _)) (le_refl _)
      _ = ‖T * U n - T‖ + ‖U n * T - T‖ := by rw [one_mul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  simpa only [zero_add] using hright.add hleft

/-- Left coordinate cutoff approximation holds for compact maps into H_B. -/
theorem standardCountableCutoff_comp_tendsto
    {T : AdjointableMap B E (StandardCountableHilbertModule B)} (hT : IsModuleCompact T) :
    Tendsto (fun n => (standardCountableCutoff n).comp T) atTop (𝓝 T) :=
  isModuleCompact_tendsto_comp_left_of_strong_contractions standardCountableCutoff
    norm_standardCountableCutoff_le standardCountableCutoff_tendsto hT

/-- The actual adjoint of a coordinate cutoff equals that cutoff. -/
@[simp] theorem standardCountableCutoff_adjoint (n : ℕ) :
    (standardCountableCutoff (B := B) n).adjoint = standardCountableCutoff n :=
  standardCountableCutoff_star n

/-- Right coordinate cutoff approximation follows by taking actual adjoints. -/
theorem comp_standardCountableCutoff_tendsto
    {T : AdjointableMap B (StandardCountableHilbertModule B) F} (hT : IsModuleCompact T) :
    Tendsto (fun n => T.comp (standardCountableCutoff n)) atTop (𝓝 T) :=
  isModuleCompact_tendsto_comp_right_of_strong_selfadjoint_contractions standardCountableCutoff
    norm_standardCountableCutoff_le standardCountableCutoff_adjoint standardCountableCutoff_tendsto hT

/-- Cutting off both coordinates of a genuine compact endomorphism converges
in operator norm, even over a nonunital coefficient algebra. -/
theorem standardCountableCutoff_mul_mul_tendsto
    {T : AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)}
    (hT : IsModuleCompact T) :
    Tendsto (fun n => standardCountableCutoff n * T * standardCountableCutoff n)
      atTop (𝓝 T) :=
  isModuleCompact_tendsto_sandwich_of_strong_selfadjoint_contractions standardCountableCutoff
    norm_standardCountableCutoff_le standardCountableCutoff_adjoint standardCountableCutoff_tendsto hT

/-- Every prescribed positive error is attained by a genuine finite-coordinate
compression of the original compact operator. -/
theorem exists_standardCountableCutoff_norm_sub_lt
    {T : AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)}
    (hT : IsModuleCompact T) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ‖T - standardCountableCutoff n * T * standardCountableCutoff n‖ < ε := by
  obtain ⟨n, hn⟩ := (tendsto_iff_norm_sub_tendsto_zero.mp
    (standardCountableCutoff_mul_mul_tendsto hT)).eventually (gt_mem_nhds hε) |>.exists
  exact ⟨n, by simpa only [norm_sub_rev] using hn⟩

end BC4lean.KKTheory
