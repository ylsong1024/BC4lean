import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.ContinuousMap.Compact

/-! # Uniform finite partition approximation of continuous maps

A continuous map on a compact Hausdorff space whose values lie in the closure
of a set is uniformly approximated by finite convex combinations of constant
maps with samples in that set. The coefficients are continuous nonnegative
real functions and sum to one. This explicit form permits finite-rank samples
to be lifted to finite-rank operators on a continuous-section module.
-/

noncomputable section

namespace BC4lean.KKTheory

open Set
open scoped Topology

variable {X V ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite sum of constant vectors weighted by continuous real functions. -/
def finitePartitionCombination (s : Finset ι) (ρ : s → C(X, ℝ))
    (q : s → V) : C(X, V) :=
  ∑ j : s, ρ j • ContinuousMap.const X (q j)

@[simp]
theorem finitePartitionCombination_apply (s : Finset ι) (ρ : s → C(X, ℝ))
    (q : s → V) (x : X) :
    finitePartitionCombination s ρ q x = ∑ j : s, ρ j x • q j := by
  classical
  simp [finitePartitionCombination]

/-- Pointwise approximability on a compact Hausdorff parameter space gives a
uniform approximation by a finite continuous partition of unity. The finite
samples lie in the original set, not merely in its closure. -/
theorem exists_finite_partition_approximation [CompactSpace X] [T2Space X]
    (f : C(X, V)) (D : Set V) (hf : ∀ x, f x ∈ closure D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset X) (ρ : s → C(X, ℝ)) (q : s → V),
      (∀ j x, 0 ≤ ρ j x) ∧ (∀ x, ∑ j : s, ρ j x = 1) ∧
      (∀ j, q j ∈ D) ∧ ‖f - finitePartitionCombination s ρ q‖ < ε := by
  classical
  have hsample : ∀ x, ∃ q ∈ D, dist (f x) q < ε :=
    fun x => Metric.mem_closure_iff.mp (hf x) ε hε
  choose q hq hdist using hsample
  let U : X → Set X := fun x => f ⁻¹' Metric.ball (q x) ε
  have hU : ∀ x, IsOpen (U x) :=
    fun x => Metric.isOpen_ball.preimage f.continuous
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hdist x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hscover : (univ : Set X) ⊆ ⋃ j : s, U j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ (fun j : s => U j) (fun j => hU j)
    (locallyFinite_of_finite _) hscover
  refine ⟨s, ρ, (fun j => q j), ρ.nonneg, ?_, (fun j => hq j), ?_⟩
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  · apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro x
    have hball : (∑ᶠ j : s, ρ j x • q j) ∈ Metric.ball (f x) ε := by
      apply ρ.finsum_smul_mem_convex (g := fun j _ => q j)
        (mem_univ x) _ (convex_ball (f x) ε)
      intro j hj
      have hxj : x ∈ U j := hρ j (subset_closure hj)
      exact (dist_comm (q j) (f x)).trans_lt hxj
    have herr : ‖f x - ∑ j : s, ρ j x • q j‖ < ε := by
      simpa only [finsum_eq_sum_of_fintype, Metric.mem_ball, dist_eq_norm,
        norm_sub_rev] using hball
    simpa using herr

end BC4lean.KKTheory
