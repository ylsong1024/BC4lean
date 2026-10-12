import BC4lean.StandardCountableHilbertModule
import Mathlib.Data.Finsupp.Basic

/-! # Finite coordinate cutoffs on the genuine standard countable module

The first-n-coordinate cutoff is an actual adjointable orthogonal projection.
Its norm is at most one, and these cutoffs converge strongly to the identity
because the canonical finite coefficient vectors are dense. No compactness
claim is made for coordinate projections over a nonunital coefficient algebra.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The coordinate inclusion and evaluation have the expected delta pairing. -/
@[simp] theorem standardCountableEvaluation_inclusion (i j : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableEvaluation i (standardCountableInclusion j b) =
      if j = i then b else 0 := by
  rw [standardCountableInclusion_apply, standardCountableEvaluation_mk]
  exact Finsupp.single_apply

/-- Equality on canonical finite coefficient vectors determines an adjointable map. -/
theorem standardCountable_adjointable_ext_mk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E]
    (S T : AdjointableMap B (StandardCountableHilbertModule B) E)
    (h : ∀ x : StandardCountableVectors B, S (standardCountableMk x) = T (standardCountableMk x)) :
    S = T := by
  apply AdjointableMap.ext
  intro x
  exact congrFun (standardCountableMk_denseRange.equalizer
    S.toCLM.continuous T.toCLM.continuous (funext h)) x

private theorem countableAdjointable_sum_apply {ι : Type*} (s : Finset ι)
    (T : ι → AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
    (x : StandardCountableHilbertModule B) :
    (∑ i ∈ s, T i) x = ∑ i ∈ s, T i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, AdjointableMap.coe_add_apply, ih]

/-- The genuine orthogonal cutoff onto the first n coefficient coordinates. -/
def standardCountableCutoff (n : ℕ) :
    AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B) :=
  ∑ i ∈ Finset.range n, (standardCountableInclusion i).comp (standardCountableEvaluation i)

/-- The cutoff is the actual finite sum of its evaluated coordinate vectors. -/
theorem standardCountableCutoff_apply (n : ℕ) (x : StandardCountableHilbertModule B) :
    standardCountableCutoff n x =
      ∑ i ∈ Finset.range n, standardCountableInclusion i (standardCountableEvaluation i x) := by
  simp only [standardCountableCutoff, countableAdjointable_sum_apply, AdjointableMap.comp_apply]

/-- The square of the cutoff is exactly the finite sum of positive coordinate squares. -/
theorem standardCountableCutoff_inner_self (n : ℕ) (x : StandardCountableHilbertModule B) :
    ⟪standardCountableCutoff n x, standardCountableCutoff n x⟫_(Bᵐᵒᵖ) =
      ∑ i ∈ Finset.range n, ⟪standardCountableEvaluation i x, standardCountableEvaluation i x⟫_(Bᵐᵒᵖ) := by
  let w : StandardCountableVectors B :=
    ∑ i ∈ Finset.range n, Finsupp.single i (standardCountableEvaluation i x)
  have hw (i : ℕ) : w i = if i < n then standardCountableEvaluation i x else 0 := by
    simp [w, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.mem_range]
  have hs : w.support ⊆ Finset.range n := by
    intro i hi
    by_contra hn
    have hin : ¬i < n := by simpa only [Finset.mem_range] using hn
    exact (Finsupp.mem_support_iff.mp hi) (by rw [hw, if_neg hin])
  have hc : standardCountableCutoff n x = standardCountableMk w := by
    simp only [standardCountableCutoff_apply, w, map_sum, standardCountableInclusion_apply]
  rw [hc, standardCountableMk_inner, standardCountableFiniteInner_eq_sum w w (Finset.range n) hs]
  exact Finset.sum_congr rfl (fun i hi => by rw [hw, if_pos (Finset.mem_range.mp hi)])

/-- Cutoff acts on canonical finite vectors by the actual finitely-supported filter. -/
@[simp] theorem standardCountableCutoff_mk (n : ℕ) (x : StandardCountableVectors B) :
    standardCountableCutoff n (standardCountableMk x) =
      standardCountableMk (x.filter (fun i => i < n)) := by
  have hf : (∑ i ∈ Finset.range n, Finsupp.single i (x i)) = x.filter (fun i => i < n) := by
    ext j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.filter_apply, Finset.mem_range]
  simp only [standardCountableCutoff, countableAdjointable_sum_apply, AdjointableMap.comp_apply,
    standardCountableEvaluation_mk, standardCountableInclusion_apply]
  rw [← map_sum, hf]

@[simp] theorem standardCountableCutoff_star (n : ℕ) :
    star (standardCountableCutoff (B := B) n) = standardCountableCutoff n := by
  simp only [standardCountableCutoff, star_sum, AdjointableMap.star_eq_adjoint,
    AdjointableMap.adjoint_comp, standardCountableEvaluation, AdjointableMap.adjoint_adjoint]

@[simp] theorem standardCountableCutoff_mul_self (n : ℕ) :
    standardCountableCutoff (B := B) n * standardCountableCutoff n = standardCountableCutoff n := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.mul_apply, standardCountableCutoff_mk]
  congr 1
  ext i
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl

/-- Finite cutoffs are actual selfadjoint idempotents. -/
theorem standardCountableCutoff_isStarProjection (n : ℕ) :
    IsStarProjection (standardCountableCutoff (B := B) n) :=
  isStarProjection_iff'.mpr ⟨standardCountableCutoff_mul_self n, standardCountableCutoff_star n⟩

/-- The cutoff bound uses the C*-norm on actual adjointable operators. -/
theorem norm_standardCountableCutoff_le (n : ℕ) : ‖standardCountableCutoff (B := B) n‖ ≤ 1 :=
  IsStarProjection.norm_le _ (standardCountableCutoff_isStarProjection n)

theorem standardCountableCutoff_norm_apply_le (n : ℕ) (x : StandardCountableHilbertModule B) :
    ‖standardCountableCutoff n x‖ ≤ ‖x‖ := by
  calc
    ‖standardCountableCutoff n x‖ ≤ ‖standardCountableCutoff (B := B) n‖ * ‖x‖ :=
      (standardCountableCutoff n).norm_apply_le x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (norm_standardCountableCutoff_le n) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Every finite coefficient vector is fixed by all sufficiently large cutoffs. -/
theorem standardCountableCutoff_eventually_mk (x : StandardCountableVectors B) :
    ∃ N : ℕ, ∀ n ≥ N, standardCountableCutoff n (standardCountableMk x) = standardCountableMk x := by
  refine ⟨x.support.sup Nat.succ, ?_⟩
  intro n hn
  rw [standardCountableCutoff_mk]
  congr 1
  apply (Finsupp.filter_eq_self_iff _ _).mpr
  intro i hi
  have his : i ∈ x.support := Finsupp.mem_support_iff.mpr hi
  have hb : i + 1 ≤ x.support.sup Nat.succ := Finset.le_sup (f := Nat.succ) his
  exact lt_of_lt_of_le (Nat.lt_of_succ_le hb) hn

/-- The finite cutoffs converge strongly to the identity in the true H_B norm. -/
theorem standardCountableCutoff_tendsto (x : StandardCountableHilbertModule B) :
    Tendsto (fun n : ℕ => standardCountableCutoff n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := Metric.mem_closure_range_iff.mp
    (standardCountableMk_denseRange (B := B) x) (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := standardCountableCutoff_eventually_mk v
  refine ⟨N, ?_⟩
  intro n hn
  have hnv := hN n hn
  have hd : dist (standardCountableCutoff n x) (standardCountableMk v) ≤
      dist x (standardCountableMk v) := by
    have hs : standardCountableCutoff n x - standardCountableMk v =
        standardCountableCutoff n (x - standardCountableMk v) := by
      rw [(standardCountableCutoff n).toCLM.map_sub, hnv]
    calc
      dist (standardCountableCutoff n x) (standardCountableMk v) =
          ‖standardCountableCutoff n (x - standardCountableMk v)‖ := by rw [dist_eq_norm, hs]
      _ ≤ ‖x - standardCountableMk v‖ := standardCountableCutoff_norm_apply_le n _
      _ = dist x (standardCountableMk v) := (dist_eq_norm _ _).symm
  calc
    dist (standardCountableCutoff n x) x ≤
        dist (standardCountableCutoff n x) (standardCountableMk v) + dist (standardCountableMk v) x :=
      dist_triangle _ _ _
    _ ≤ dist x (standardCountableMk v) + dist (standardCountableMk v) x := add_le_add hd le_rfl
    _ < ε := by rw [dist_comm (standardCountableMk v) x]; linarith

end BC4lean.KKTheory
