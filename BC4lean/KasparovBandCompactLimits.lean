import BC4lean.KasparovBandCoordinates
import BC4lean.KasparovWeightedBandEstimates
import BC4lean.EquivariantCompactOperator

/-! # Identifying norm-convergent compact band series

The weighted positive sums have their genuine strong limit given by the
adjointable column. Product and error series converge in operator norm.
Uniqueness of their vector limits identifies their compact norm limits with
the corresponding products, commutators, and action errors of the column
square. Equivariant strong convergence follows from the actual module
isometries, without assuming that arbitrary ambient automorphisms preserve
strong limits.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

private def operatorEvaluation (x : E) : AdjointableMap B E E →L[ℂ] E :=
  (ContinuousLinearMap.apply ℂ E x).comp AdjointableMap.toCLMContinuousLinearMap

omit [StarOrderedRing B] [CompleteSpace E] in
private theorem operatorEvaluation_apply (x : E) (T : AdjointableMap B E E) :
    operatorEvaluation x T = T x := rfl

omit [StarOrderedRing B] [CompleteSpace E] in
private theorem finite_operator_sum_apply (W : ℕ → AdjointableMap B E E) (N : ℕ) (x : E) :
    (∑ n ∈ Finset.range N, W n) x = ∑ n ∈ Finset.range N, W n x := by
  exact map_sum (operatorEvaluation (B := B) x) W (Finset.range N)

omit [CompleteSpace E] in
/-- Genuine operator-norm limits of compact module operators are compact. -/
theorem IsModuleCompact.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → AdjointableMap B E E} {S : AdjointableMap B E E}
    (hlim : Tendsto T l (𝓝 S)) (hT : ∀ᶠ i in l, IsModuleCompact (T i)) :
    IsModuleCompact S := moduleCompact_isClosed.mem_of_tendsto hlim hT

omit [CompleteSpace E] in
/-- The actual compactness of a norm-summable operator series. -/
theorem IsModuleCompact.tsum {W : ℕ → AdjointableMap B E E}
    (hW : ∀ n, IsModuleCompact (W n)) (hsum : Summable W) :
    IsModuleCompact (∑' n, W n) := by
  apply IsModuleCompact.of_tendsto hsum.hasSum.tendsto_sum_nat
  exact Eventually.of_forall fun N =>
    (moduleCompact B E E).sum_mem (fun n _ => hW n)

omit [CompleteSpace E] in
/-- A norm-convergent right-product series identifies the actual right
product of a strongly convergent operator sum, and proves it compact. -/
theorem compact_right_product_of_summable_strong_series
    (W : ℕ → AdjointableMap B E E) (M a : AdjointableMap B E E)
    (hstrong : ∀ x, Tendsto (fun N => (∑ n ∈ Finset.range N, W n) x) atTop (𝓝 (M x)))
    (hW : ∀ n, IsModuleCompact (W n)) (hsum : Summable (fun n => W n * a)) :
    IsModuleCompact (M * a) := by
  have heq : (∑' n, W n * a) = M * a := by
    apply AdjointableMap.ext
    intro x
    have hnorm := (operatorEvaluation (B := B) x).continuous.tendsto (∑' n, W n * a) |>.comp
      hsum.hasSum.tendsto_sum_nat
    have hs := hstrong (a x)
    simp only [operatorEvaluation_apply, ← Finset.sum_mul] at hnorm
    exact tendsto_nhds_unique hnorm hs
  rw [← heq]
  exact IsModuleCompact.tsum (fun n => (hW n).comp_right a) hsum

omit [CompleteSpace E] in
/-- Commutator series converge in norm and identify the actual
commutator of the genuine strong sum. -/
theorem compact_commutator_of_summable_strong_series
    (W : ℕ → AdjointableMap B E E) (M a : AdjointableMap B E E)
    (hstrong : ∀ x, Tendsto (fun N => (∑ n ∈ Finset.range N, W n) x) atTop (𝓝 (M x)))
    (hW : ∀ n, IsModuleCompact (W n))
    (hsum : Summable (fun n => W n * a - a * W n)) :
    IsModuleCompact (M * a - a * M) := by
  have heq : (∑' n, (W n * a - a * W n)) = M * a - a * M := by
    apply AdjointableMap.ext
    intro x
    have hnorm := (operatorEvaluation (B := B) x).continuous.tendsto (∑' n, (W n * a - a * W n)) |>.comp
      hsum.hasSum.tendsto_sum_nat
    have hs := (hstrong (a x)).sub ((a.toCLM.continuous.tendsto (M x)).comp (hstrong x))
    change Tendsto (fun N => (∑ n ∈ Finset.range N, (W n * a - a * W n)) x)
      atTop (𝓝 ((∑' n, (W n * a - a * W n)) x)) at hnorm
    have htarget : Tendsto (fun N => (∑ n ∈ Finset.range N, (W n * a - a * W n)) x)
        atTop (𝓝 ((M * a - a * M) x)) := by
      simpa only [Function.comp_def, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply] using hs
    exact tendsto_nhds_unique hnorm htarget
  rw [← heq]
  exact IsModuleCompact.tsum
    (fun n => ((hW n).comp_right a).sub ((hW n).comp_left a)) hsum

section ActualAction
variable {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ B}

omit [StarOrderedRing B] [CompleteSpace E] in
/-- The actual compatible module action preserves strong operator
limits by its vector formula and continuity of the module isometry. -/
theorem EquivariantHilbertModule.tendsto_conjugateOperator_apply
    (U : EquivariantHilbertModule α E) (g : Γ)
    (T : ℕ → AdjointableMap B E E) (S : AdjointableMap B E E)
    (hstrong : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (S x))) (x : E) :
    Tendsto (fun n => U.conjugateOperator g (T n) x) atTop
      (𝓝 (U.conjugateOperator g S x)) := by
  exact (U.action g).continuous.tendsto (S (U.action g⁻¹ x)) |>.comp
    (hstrong (U.action g⁻¹ x))

omit [CompleteSpace E] in
/-- The actual module action's norm-convergent error series identifies
the equivariance error of the column-square strong limit. -/
theorem compact_action_error_of_summable_strong_series
    (U : EquivariantHilbertModule α E) (g : Γ)
    (W : ℕ → AdjointableMap B E E) (M : AdjointableMap B E E)
    (hstrong : ∀ x, Tendsto (fun N => (∑ n ∈ Finset.range N, W n) x) atTop (𝓝 (M x)))
    (hW : ∀ n, IsModuleCompact (W n))
    (hsum : Summable (fun n => U.conjugateOperator g (W n) - W n)) :
    IsModuleCompact (U.conjugateOperator g M - M) := by
  have heq : (∑' n, (U.conjugateOperator g (W n) - W n)) = U.conjugateOperator g M - M := by
    apply AdjointableMap.ext
    intro x
    have hnorm := (operatorEvaluation (B := B) x).continuous.tendsto
      (∑' n, (U.conjugateOperator g (W n) - W n)) |>.comp hsum.hasSum.tendsto_sum_nat
    have hs := (U.tendsto_conjugateOperator_apply g _ M hstrong x).sub (hstrong x)
    have hmap (N : ℕ) :
        (∑ n ∈ Finset.range N, U.conjugateOperator g (W n)) =
          U.conjugateOperator g (∑ n ∈ Finset.range N, W n) := by
      exact (map_sum (U.conjugateMapContinuousLinearMap U g) W (Finset.range N)).symm
    change Tendsto (fun N => (∑ n ∈ Finset.range N,
      (U.conjugateOperator g (W n) - W n)) x) atTop
      (𝓝 ((∑' n, (U.conjugateOperator g (W n) - W n)) x)) at hnorm
    have htarget : Tendsto (fun N => (∑ n ∈ Finset.range N,
        (U.conjugateOperator g (W n) - W n)) x) atTop
        (𝓝 ((U.conjugateOperator g M - M) x)) := by
      simpa only [Finset.sum_sub_distrib, hmap, AdjointableMap.coe_sub_apply] using hs
    exact tendsto_nhds_unique hnorm htarget
  rw [← heq]
  exact IsModuleCompact.tsum
    (fun n => ((hW n).conjugateOperator U g).sub (hW n)) hsum

end ActualAction
end BC4lean.KKTheory
