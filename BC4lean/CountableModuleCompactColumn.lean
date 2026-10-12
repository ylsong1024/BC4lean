import BC4lean.CountableModuleOperator
import BC4lean.CompactModuleOperator

/-! # Compact columns in the genuine countable module sum

An actual adjointable column is module-compact if every coordinate is compact
and the actual operator-norm tails tend to zero. The latter hypothesis is
necessary; compact coordinate maps by themselves do not imply a compact
column. The proof takes norm limits of the genuine finite compact columns.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace F]

/-- A finite coordinate cutoff of a compact-coordinate column is genuinely compact. -/
theorem moduleCompact_countable_cutoff_column
    (T : AdjointableMap B E (CountableHilbertModuleSum B F))
    (hT : ∀ n, IsModuleCompact ((countableModuleEvaluation (B := B) n).comp T)) (N : ℕ) :
    IsModuleCompact ((countableModuleCutoff (B := B) N).comp T) := by
  have heq : (countableModuleCutoff (B := B) N).comp T =
      ∑ n ∈ Finset.range N,
        (countableModuleInclusion (B := B) n).comp ((countableModuleEvaluation (B := B) n).comp T) := by
    ext u
    rw [AdjointableMap.comp_apply, countableModuleCutoff_apply]
    have hsum (s : Finset ℕ) :
        (∑ n ∈ s, (countableModuleInclusion (B := B) n).comp
          ((countableModuleEvaluation (B := B) n).comp T)) u =
        ∑ n ∈ s, countableModuleInclusion (B := B) n (countableModuleEvaluation (B := B) n (T u)) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert n s hn ih =>
        simp only [Finset.sum_insert hn, AdjointableMap.coe_add_apply, ih, AdjointableMap.comp_apply]
    exact (hsum _).symm
  rw [heq]
  exact (moduleCompact B E (CountableHilbertModuleSum B F)).sum_mem
    (fun n _ => (hT n).comp_left (countableModuleInclusion (B := B) n))

/-- Compact coordinates and proved operator-norm tail convergence give a compact column. -/
theorem moduleCompact_countable_column_of_norm_tail_tendsto_zero
    (T : AdjointableMap B E (CountableHilbertModuleSum B F))
    (hT : ∀ n, IsModuleCompact ((countableModuleEvaluation (B := B) n).comp T))
    (htail : Tendsto (fun N => ‖T - (countableModuleCutoff (B := B) N).comp T‖) atTop (𝓝 0)) :
    IsModuleCompact T := by
  have hlim : Tendsto (fun N => (countableModuleCutoff (B := B) N).comp T) atTop (𝓝 T) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).mpr
    simpa only [norm_sub_rev] using htail
  exact (moduleCompact_isClosed (B := B) (E := E) (F := CountableHilbertModuleSum B F)).mem_of_tendsto
    hlim (Eventually.of_forall (moduleCompact_countable_cutoff_column T hT))

end BC4lean.KKTheory
