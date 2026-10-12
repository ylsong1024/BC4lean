import BC4lean.CountableHilbertModuleSum
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Coefficient-convergent sequences in the actual countable module sum

Convergence of the partial sums of the positive B-valued coordinate squares
makes the finite coordinate truncations Cauchy in the genuine Hilbert-module
norm. Their actual limit realizes the sequence. No summability of real squared
coordinate norms is required. Mixed coefficient sums recover the inner product
of the actual limits.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

def countableModuleFiniteSection (v : ℕ → E) (s : Finset ℕ) : CountableModuleVectors E :=
  ∑ i ∈ s, Finsupp.single i (v i)

omit [NormedSpace ℂ E] in
@[simp] theorem countableModuleFiniteSection_apply (v : ℕ → E) (s : Finset ℕ) (i : ℕ) :
    countableModuleFiniteSection v s i = if i ∈ s then v i else 0 := by
  classical
  simp [countableModuleFiniteSection, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit [NormedSpace ℂ E] in
theorem countableModuleFiniteSection_support_subset (v : ℕ → E) (s : Finset ℕ) :
    (countableModuleFiniteSection v s).support ⊆ s := by
  intro i hi
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hi) (by rw [countableModuleFiniteSection_apply, if_neg hn])

theorem countableModuleFiniteSection_inner (v w : ℕ → E) (s : Finset ℕ) :
    ⟪countableModuleMk (B := B) (countableModuleFiniteSection v s),
      countableModuleMk (B := B) (countableModuleFiniteSection w s)⟫_(Bᵐᵒᵖ) =
      ∑ i ∈ s, ⟪v i, w i⟫_(Bᵐᵒᵖ) := by
  rw [countableModuleMk_inner, countableModuleFiniteInner_eq_sum _ _ s
    (countableModuleFiniteSection_support_subset v s)]
  exact Finset.sum_congr rfl (fun i hi => by simp only [countableModuleFiniteSection_apply, if_pos hi])

def countableModuleTruncation (v : ℕ → E) (n : ℕ) : CountableHilbertModuleSum B E :=
  countableModuleMk (B := B) (countableModuleFiniteSection v (Finset.range n))

@[simp] theorem countableModuleTruncation_add (v w : ℕ → E) (n : ℕ) :
    countableModuleTruncation (B := B) (v + w) n =
      countableModuleTruncation (B := B) v n + countableModuleTruncation (B := B) w n := by
  unfold countableModuleTruncation countableModuleFiniteSection
  simp only [Pi.add_apply, Finsupp.single_add, Finset.sum_add_distrib, map_add]

@[simp] theorem countableModuleTruncation_smul (c : ℂ) (v : ℕ → E) (n : ℕ) :
    countableModuleTruncation (B := B) (c • v) n = c • countableModuleTruncation (B := B) v n := by
  unfold countableModuleTruncation countableModuleFiniteSection
  simp only [Pi.smul_apply, ← Finsupp.smul_single, ← Finset.smul_sum, map_smul]

@[simp] theorem countableModuleTruncation_inner (v w : ℕ → E) (n : ℕ) :
    ⟪countableModuleTruncation (B := B) v n, countableModuleTruncation (B := B) w n⟫_(Bᵐᵒᵖ) =
      ∑ i ∈ Finset.range n, ⟪v i, w i⟫_(Bᵐᵒᵖ) := countableModuleFiniteSection_inner _ _ _

theorem countableModuleTruncation_difference_norm_sq (v : ℕ → E) {n m : ℕ} (hnm : n ≤ m) :
    ‖countableModuleTruncation (B := B) v m - countableModuleTruncation (B := B) v n‖ ^ 2 =
      ‖(∑ i ∈ Finset.range m, ⟪v i, v i⟫_(Bᵐᵒᵖ)) -
        ∑ i ∈ Finset.range n, ⟪v i, v i⟫_(Bᵐᵒᵖ)‖ := by
  classical
  have hs : countableModuleFiniteSection v (Finset.range m) -
      countableModuleFiniteSection v (Finset.range n) =
      countableModuleFiniteSection v (Finset.range m \ Finset.range n) := by
    apply sub_eq_iff_eq_add.mpr
    exact (Finset.sum_sdiff (Finset.range_mono hnm)).symm
  change ‖countableModuleMk (B := B) (countableModuleFiniteSection v (Finset.range m)) -
    countableModuleMk (B := B) (countableModuleFiniteSection v (Finset.range n))‖ ^ 2 = _
  rw [← map_sub, hs, CStarModule.norm_sq_eq (Bᵐᵒᵖ), countableModuleFiniteSection_inner,
    Finset.sum_sdiff_eq_sub (Finset.range_mono hnm)]

/-- Actual coefficient-square convergence gives Cauchy finite truncations in the
true Hilbert-module norm. -/
theorem countableModuleTruncation_cauchy (v : ℕ → E) {L : Bᵐᵒᵖ}
    (h : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ⟪v i, v i⟫_(Bᵐᵒᵖ)) atTop (𝓝 L)) :
    CauchySeq (countableModuleTruncation (B := B) v) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp h.cauchySeq (ε ^ 2) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hsq : dist (countableModuleTruncation (B := B) v m)
      (countableModuleTruncation (B := B) v n) ^ 2 < ε ^ 2 := by
    rcases le_total n m with hnm | hmn
    · rw [dist_eq_norm, countableModuleTruncation_difference_norm_sq v hnm]
      simpa only [dist_eq_norm] using hN m hm n hn
    · rw [dist_comm, dist_eq_norm, countableModuleTruncation_difference_norm_sq v hmn]
      simpa only [dist_eq_norm] using hN n hn m hm
  nlinarith [show 0 ≤ dist (countableModuleTruncation (B := B) v m) (countableModuleTruncation (B := B) v n) from dist_nonneg]

/-- The genuine countable-module realization of a coefficient-convergent sequence. -/
def countableModuleSequenceSum (v : ℕ → E) : CountableHilbertModuleSum B E :=
  limUnder atTop (countableModuleTruncation (B := B) v)

theorem countableModuleTruncation_tendsto (v : ℕ → E) {L : Bᵐᵒᵖ}
    (h : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ⟪v i, v i⟫_(Bᵐᵒᵖ)) atTop (𝓝 L)) :
    Tendsto (countableModuleTruncation (B := B) v) atTop (𝓝 (countableModuleSequenceSum (B := B) v)) :=
  (countableModuleTruncation_cauchy v h).tendsto_limUnder

/-- Actual mixed coefficient convergence computes the inner product of the actual sums. -/
theorem countableModuleSequenceSum_inner (v w : ℕ → E) {Lv Lw Lvw : Bᵐᵒᵖ}
    (hv : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ⟪v i, v i⟫_(Bᵐᵒᵖ)) atTop (𝓝 Lv))
    (hw : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ⟪w i, w i⟫_(Bᵐᵒᵖ)) atTop (𝓝 Lw))
    (hvw : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ⟪v i, w i⟫_(Bᵐᵒᵖ)) atTop (𝓝 Lvw)) :
    ⟪countableModuleSequenceSum (B := B) v, countableModuleSequenceSum (B := B) w⟫_(Bᵐᵒᵖ) = Lvw := by
  have ht := (CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := CountableHilbertModuleSum B E)).tendsto
    (countableModuleSequenceSum (B := B) v, countableModuleSequenceSum (B := B) w) |>.comp
      ((countableModuleTruncation_tendsto v hv).prodMk_nhds (countableModuleTruncation_tendsto w hw))
  simp only [Function.comp_def, countableModuleTruncation_inner] at ht
  exact tendsto_nhds_unique ht hvw

variable [CompleteSpace E]

/-- The actual limit has the prescribed coordinate, by eventual exact evaluation
of its finite truncations. -/
theorem countableModuleEvaluation_sequenceSum (v : ℕ → E) {L : Bᵐᵒᵖ}
    (h : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, ⟪v j, v j⟫_(Bᵐᵒᵖ)) atTop (𝓝 L))
    (i : ℕ) : countableModuleEvaluation (B := B) i (countableModuleSequenceSum (B := B) v) = v i := by
  have ht := (countableModuleEvaluation (B := B) (E := E) i).toCLM.continuous.tendsto
    (countableModuleSequenceSum (B := B) v) |>.comp (countableModuleTruncation_tendsto v h)
  have hc : Tendsto (fun n => countableModuleEvaluation (B := B) i
      (countableModuleTruncation (B := B) v n)) atTop (𝓝 (v i)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    simp only [countableModuleTruncation, countableModuleEvaluation_mk,
      countableModuleFiniteSection_apply, Finset.mem_range, if_pos (by omega : i < n)]
  exact tendsto_nhds_unique ht hc

/-- The finite-versus-infinite pairing is the actual finite coefficient sum. -/
theorem countableModuleMk_inner_sequenceSum (u : CountableModuleVectors E) (v : ℕ → E)
    {L : Bᵐᵒᵖ}
    (h : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, ⟪v j, v j⟫_(Bᵐᵒᵖ)) atTop (𝓝 L)) :
    ⟪countableModuleMk (B := B) u, countableModuleSequenceSum (B := B) v⟫_(Bᵐᵒᵖ) =
      ∑ i ∈ u.support, ⟪u i, v i⟫_(Bᵐᵒᵖ) := by
  rw [countableModuleMk_inner_right]
  exact Finset.sum_congr rfl (fun i _ => by rw [countableModuleEvaluation_sequenceSum v h])

end BC4lean.KKTheory
