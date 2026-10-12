import BC4lean.CountableModuleCompactColumn

/-! # Compact rectangular defects from proved column tails

For a bounded diagonal-type operator commuting with actual coordinate
cutoffs, the rectangular defect `D V - V S` has tails bounded by
`(‖D‖+‖S‖)` times the actual operator-norm tails of V. Coordinate compactness
therefore proves compactness of the complete defect.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] in
theorem moduleCompact_countable_rectangular_defect
    (D : AdjointableMap B (CountableHilbertModuleSum B F) (CountableHilbertModuleSum B F))
    (S : AdjointableMap B E E) (V : AdjointableMap B E (CountableHilbertModuleSum B F))
    (hcut : ∀ N, D.comp (countableModuleCutoff (B := B) N) =
      (countableModuleCutoff (B := B) N).comp D)
    (hcoord : ∀ n, IsModuleCompact ((countableModuleEvaluation (B := B) n).comp
      (D.comp V - V.comp S)))
    (htail : Tendsto (fun N => ‖V - (countableModuleCutoff (B := B) N).comp V‖) atTop (𝓝 0)) :
    IsModuleCompact (D.comp V - V.comp S) := by
  apply moduleCompact_countable_column_of_norm_tail_tendsto_zero _ hcoord
  have hbound (N : ℕ) :
      ‖(D.comp V - V.comp S) - (countableModuleCutoff (B := B) N).comp
        (D.comp V - V.comp S)‖ ≤
      (‖D‖ + ‖S‖) * ‖V - (countableModuleCutoff (B := B) N).comp V‖ := by
    let U := V - (countableModuleCutoff (B := B) N).comp V
    have heq : (D.comp V - V.comp S) - (countableModuleCutoff (B := B) N).comp
        (D.comp V - V.comp S) = D.comp U - U.comp S := by
      ext y
      have hc := congrArg (fun R => R (V y)) (hcut N)
      simp only [AdjointableMap.comp_apply] at hc
      simp only [U, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub]
      rw [hc]
      abel
    rw [heq]
    calc
      ‖D.comp U - U.comp S‖ ≤ ‖D.comp U‖ + ‖U.comp S‖ := norm_sub_le _ _
      _ ≤ ‖D‖ * ‖U‖ + ‖U‖ * ‖S‖ :=
        add_le_add (AdjointableMap.norm_comp_le _ _) (AdjointableMap.norm_comp_le _ _)
      _ = (‖D‖ + ‖S‖) * ‖U‖ := by ring
  have hlim : Tendsto (fun N => (‖D‖ + ‖S‖) *
      ‖V - (countableModuleCutoff (B := B) N).comp V‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using htail.const_mul (‖D‖ + ‖S‖)
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hlim

end BC4lean.KKTheory
