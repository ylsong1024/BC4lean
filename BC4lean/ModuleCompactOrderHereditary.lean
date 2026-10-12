import BC4lean.CompactModuleApproximateUnit
import BC4lean.CompactModuleOperatorCriterion
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.NoncommRing

/-! # Order heredity of the actual compact module ideal

If `0 ≤ T ≤ K` and `K` is compact, the actual square root of `T` is a
norm limit of its products with the canonical compact approximate unit.
The key estimate compares the residual star square with the residual
compression of `K`. This uses the actual compact ideal and its two-sided
approximate-unit filter; no countable generation or separability is needed.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Topology
open Filter

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance standardModuleCompactOrderHereditaryLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardModuleCompactOrderHereditaryLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- Order compression controls the squared square-root residual by the
actual right multiplication error of a positive upper bound. -/
theorem module_sqrt_residual_norm_sq_le
    (T K e : AdjointableMap B E E) (hT : 0 ≤ T) (hTK : T ≤ K) (he : ‖e‖ ≤ 1) :
    ‖CFC.sqrt T - CFC.sqrt T * e‖ ^ 2 ≤ 2 * ‖K - K * e‖ := by
  let S := CFC.sqrt T
  let R : AdjointableMap B E E := 1 - e
  have hSstar : star S = S := (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq
  have hSsq : S * S = T := CFC.sqrt_mul_sqrt_self T hT
  have hfactor : S - S * e = S * R := by
    dsimp only [R]
    noncomm_ring
  have hnormI : ‖(1 : AdjointableMap B E E)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ E‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have hnormR : ‖R‖ ≤ 2 := by
    calc
      ‖R‖ ≤ ‖(1 : AdjointableMap B E E)‖ + ‖e‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hnormI he
      _ = 2 := by norm_num
  have hstarSquare : star (S - S * e) * (S - S * e) = star R * T * R := by
    calc
      star (S - S * e) * (S - S * e) = star (S * R) * (S * R) := by rw [hfactor]
      _ = star R * (star S * S) * R := by
        rw [star_mul]
        noncomm_ring
      _ = star R * T * R := by rw [hSstar, hSsq]
  have hKfactor : star R * K * R = star R * (K - K * e) := by
    dsimp only [R]
    noncomm_ring
  calc
    ‖CFC.sqrt T - CFC.sqrt T * e‖ ^ 2 =
        ‖star (S - S * e) * (S - S * e)‖ := by
      rw [CStarRing.norm_star_mul_self, pow_two]
    _ = ‖star R * T * R‖ := by rw [hstarSquare]
    _ ≤ ‖star R * K * R‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le
        (star_left_conjugate_nonneg hT R) (star_left_conjugate_le_conjugate hTK R)
    _ = ‖star R * (K - K * e)‖ := by rw [hKfactor]
    _ ≤ ‖star R‖ * ‖K - K * e‖ := norm_mul_le _ _
    _ = ‖R‖ * ‖K - K * e‖ := by rw [norm_star]
    _ ≤ 2 * ‖K - K * e‖ :=
      mul_le_mul_of_nonneg_right hnormR (norm_nonneg _)

namespace IsModuleCompact

/-- A positive operator below an actual compact upper bound has compact
square root. The approximants are `sqrt(T) e` from the canonical compact
approximate-unit filter, and not finite-dimensional Hilbert-space maps. -/
theorem sqrt_of_nonneg_of_le {T K : AdjointableMap B E E}
    (hK : IsModuleCompact K) (hT : 0 ≤ T) (hTK : T ≤ K) :
    IsModuleCompact (CFC.sqrt T) := by
  let k : CompactModuleOperator B E := ⟨K, hK⟩
  let : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _
  have hau := CStarAlgebra.increasingApproximateUnit (CompactModuleOperator B E)
  have hlim : Tendsto (fun e : CompactModuleOperator B E => ‖k - k * e‖)
      (CStarAlgebra.approximateUnit (CompactModuleOperator B E)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := k)).sub (hau.tendsto_mul_left k)).norm
  change CFC.sqrt T ∈ (moduleCompact B E E : Set (AdjointableMap B E E))
  rw [← (moduleCompact_isClosed (B := B) (E := E) (F := E)).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨e, he, hsmall⟩ :=
    (hau.eventually_norm.and (hlim.eventually (gt_mem_nhds hδ))).exists
  change ‖(e : AdjointableMap B E E)‖ ≤ 1 at he
  change ‖K - K * (e : AdjointableMap B E E)‖ < ε ^ 2 / 2 at hsmall
  refine ⟨CFC.sqrt T * e.val, mul_mem_moduleCompact_left (CFC.sqrt T) e.property, ?_⟩
  rw [dist_eq_norm]
  have hbound := module_sqrt_residual_norm_sq_le T K e.val hT hTK he
  nlinarith [norm_nonneg (CFC.sqrt T - CFC.sqrt T * e.val)]

/-- The closed ideal of actual compact module operators is hereditary in
the spectral order of the complete adjointable endomorphism algebra. -/
theorem of_nonneg_of_le {T K : AdjointableMap B E E}
    (hK : IsModuleCompact K) (hT : 0 ≤ T) (hTK : T ≤ K) : IsModuleCompact T := by
  have hS := hK.sqrt_of_nonneg_of_le hT hTK
  rw [← CFC.sqrt_mul_sqrt_self T hT]
  exact mul_mem_moduleCompact_left (CFC.sqrt T) hS

end IsModuleCompact
end BC4lean.KKTheory
