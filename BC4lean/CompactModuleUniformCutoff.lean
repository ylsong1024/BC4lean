import BC4lean.CompactModuleStrongCutoff
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Order.Filter.Finite

/-! # Uniform genuine compact cutoffs on norm-compact families

The actual strong-contraction cutoff converges uniformly on every norm-compact
family of genuine module compact operators. A finite metric-ball cover and the
proved two-Lipschitz error estimate give one coordinate bound for the entire
family. Neither compactness of the coordinate projections nor a spectral gap
is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

omit [StarOrderedRing B] in
/-- The true sandwich error is two-Lipschitz for every actual contraction. -/
theorem norm_moduleSandwich_error_sub_le (U T S : AdjointableMap B E E)
    (hU : ‖U‖ ≤ 1) :
    ‖(U * T * U - T) - (U * S * U - S)‖ ≤ 2 * ‖T - S‖ := by
  have hEq : (U * T * U - T) - (U * S * U - S) = U * (T - S) * U - (T - S) := by
    noncomm_ring
  have hSandwich : ‖U * (T - S) * U‖ ≤ ‖T - S‖ := by
    calc
      ‖U * (T - S) * U‖ ≤ ‖U * (T - S)‖ * ‖U‖ := norm_mul_le _ _
      _ ≤ (‖U‖ * ‖T - S‖) * ‖U‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * ‖T - S‖) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hU (norm_nonneg _)) hU
          (norm_nonneg _) (by positivity)
      _ = ‖T - S‖ := by rw [one_mul, mul_one]
  rw [hEq]
  exact (norm_sub_le _ _).trans (by linarith)

/-- One true strong-contraction cutoff bound works on an entire compact family
of actual module compact operators. -/
theorem isCompact_eventually_uniform_moduleSandwich
    (U : ℕ → AdjointableMap B E E)
    (hNorm : ∀ n, ‖U n‖ ≤ 1) (hSelf : ∀ n, (U n).adjoint = U n)
    (hStrong : ∀ x : E, Tendsto (fun n => U n x) atTop (𝓝 x))
    (K : Set (AdjointableMap B E E)) (hK : IsCompact K)
    (hCompact : ∀ T ∈ K, IsModuleCompact T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ T ∈ K, ‖U n * T * U n - T‖ < ε := by
  obtain ⟨F, hFK, hF, hCover⟩ := hK.finite_cover_balls (by positivity : 0 < ε / 4)
  have hCenters : ∀ S ∈ F, ∀ᶠ n in atTop, ‖U n * S * U n - S‖ < ε / 2 := by
    intro S hS
    exact (tendsto_iff_norm_sub_tendsto_zero.mp
      (isModuleCompact_tendsto_sandwich_of_strong_selfadjoint_contractions
        U hNorm hSelf hStrong (hCompact S (hFK hS)))).eventually
          (gt_mem_nhds (by positivity))
  have hAll : ∀ᶠ n in atTop, ∀ S ∈ F, ‖U n * S * U n - S‖ < ε / 2 :=
    (hF.eventually_all).mpr hCenters
  filter_upwards [hAll] with n hn
  intro T hT
  obtain ⟨S, hS, hTS⟩ := Set.mem_iUnion₂.mp (hCover hT)
  have hDist : ‖T - S‖ < ε / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hTS
  have hErr := norm_moduleSandwich_error_sub_le (U n) T S (hNorm n)
  calc
    ‖U n * T * U n - T‖ ≤
        ‖(U n * T * U n - T) - (U n * S * U n - S)‖ + ‖U n * S * U n - S‖ :=
      norm_le_norm_sub_add _ _
    _ < ε := by linarith [hn S hS]

/-- A norm-continuous compact family on a compact parameter space therefore
has one genuine uniform cutoff size, derived from its actual compact image. -/
theorem continuous_eventually_uniform_moduleSandwich
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (U : ℕ → AdjointableMap B E E)
    (hNorm : ∀ n, ‖U n‖ ≤ 1) (hSelf : ∀ n, (U n).adjoint = U n)
    (hStrong : ∀ x : E, Tendsto (fun n => U n x) atTop (𝓝 x))
    (T : X → AdjointableMap B E E) (hT : Continuous T)
    (hCompact : ∀ x, IsModuleCompact (T x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x, ‖U n * T x * U n - T x‖ < ε := by
  have h := isCompact_eventually_uniform_moduleSandwich U hNorm hSelf hStrong
    (Set.range T) (isCompact_range hT) (by rintro _ ⟨x, rfl⟩; exact hCompact x) hε
  filter_upwards [h] with n hn
  intro x
  exact hn (T x) ⟨x, rfl⟩

end BC4lean.KKTheory
