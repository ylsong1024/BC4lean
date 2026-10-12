import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NoncommRing

/-! # Prerequisites for quasicentral approximate units

This file constructs positive contractive finite-error approximate units and
an actual approximate-unit sequence for a separable C⋆-algebra. It also proves
internal commutator convergence and the weak-to-norm finite convexification
step used in the usual quasicentral approximate-unit argument.

Internal commutator convergence concerns elements of the algebra whose unit
is being approximated. It does not establish convergence against arbitrary
elements of an ambient algebra containing that algebra as an ideal. The
ambient-ideal weak commutator convergence and Kasparov technical theorem are
not asserted here.
-/

noncomputable section

namespace BC4lean.KKTheory

open Set Filter TopologicalSpace
open scoped Topology

section CStarPrerequisites

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Right approximate-unit errors extend from a dense set with a uniform
constant when the candidate units are contractions. -/
theorem norm_right_unit_error_le (e a b : A) (he : ‖e‖ ≤ 1) :
    ‖a * e - a‖ ≤ 2 * ‖a - b‖ + ‖b * e - b‖ := by
  have hmul : ‖(a - b) * e‖ ≤ ‖a - b‖ := by
    calc
      ‖(a - b) * e‖ ≤ ‖a - b‖ * ‖e‖ := norm_mul_le _ _
      _ ≤ ‖a - b‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = ‖a - b‖ := mul_one _
  calc
    ‖a * e - a‖ = ‖((a - b) * e + (b * e - b)) + (b - a)‖ := by
      congr 1
      noncomm_ring
    _ ≤ (‖(a - b) * e‖ + ‖b * e - b‖) + ‖b - a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * ‖a - b‖ + ‖b * e - b‖ := by
      rw [norm_sub_rev b a]
      linarith

/-- The corresponding estimate for left approximate-unit errors. -/
theorem norm_left_unit_error_le (e a b : A) (he : ‖e‖ ≤ 1) :
    ‖e * a - a‖ ≤ 2 * ‖a - b‖ + ‖e * b - b‖ := by
  have hmul : ‖e * (a - b)‖ ≤ ‖a - b‖ := by
    calc
      ‖e * (a - b)‖ ≤ ‖e‖ * ‖a - b‖ := norm_mul_le _ _
      _ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = ‖a - b‖ := one_mul _
  calc
    ‖e * a - a‖ = ‖(e * (a - b) + (e * b - b)) + (b - a)‖ := by
      congr 1
      noncomm_ring
    _ ≤ (‖e * (a - b)‖ + ‖e * b - b‖) + ‖b - a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * ‖a - b‖ + ‖e * b - b‖ := by
      rw [norm_sub_rev b a]
      linarith

variable [PartialOrder A] [StarOrderedRing A]

/-- Finite convex combinations retain positivity and contractivity. -/
theorem positive_contraction_finite_convex_combination {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (u : κ → A) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, ‖u i‖ ≤ 1) :
    0 ≤ ∑ i, w i • u i ∧ ‖∑ i, w i • u i‖ ≤ 1 := by
  have hmem : (∑ i, w i • u i) ∈ Ici (0 : A) ∩ Metric.closedBall 0 1 :=
    ((convex_Ici (0 : A)).inter (convex_closedBall (0 : A) 1)).sum_mem
      (fun i _ => hw0 i) hw1 (fun i _ => ⟨hu0 i, by simpa using hu1 i⟩)
  exact ⟨hmem.1, by simpa using hmem.2⟩

/-- A positive contraction can approximate the identity on any specified
finite family on both sides. This is an actual choice from Mathlib's proper
canonical C⋆-algebra approximate-unit filter. -/
theorem exists_positive_contraction_approximate_on (s : Finset A) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ e : A, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧
      ∀ a ∈ s, ‖a * e - a‖ < ε ∧ ‖e * a - a‖ < ε := by
  classical
  let l := CStarAlgebra.approximateUnit A
  have hau := CStarAlgebra.increasingApproximateUnit A
  have hleft (a : A) : ∀ᶠ e in l, ‖a * e - a‖ < ε := by
    have hlim : Tendsto (fun e : A => ‖a * e - a‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((hau.tendsto_mul_left a).sub (tendsto_const_nhds (x := a))).norm
    exact hlim.eventually (gt_mem_nhds hε)
  have hright (a : A) : ∀ᶠ e in l, ‖e * a - a‖ < ε := by
    have hlim : Tendsto (fun e : A => ‖e * a - a‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((hau.tendsto_mul_right a).sub (tendsto_const_nhds (x := a))).norm
    exact hlim.eventually (gt_mem_nhds hε)
  have herr : ∀ᶠ e in l, ∀ a ∈ s, ‖a * e - a‖ < ε ∧ ‖e * a - a‖ < ε :=
    (eventually_all_finset s).mpr (fun a _ => (hleft a).and (hright a))
  exact (hau.eventually_nonneg.and (hau.eventually_norm.and herr)).exists

/-- Two-sided approximate-unit convergence implies internal commutator
convergence, without any separability hypothesis. -/
theorem tendsto_internal_commutator_approximateUnit (a : A) :
    Tendsto (fun e : A => e * a - a * e)
      (CStarAlgebra.approximateUnit A) (𝓝 0) := by
  have hau := CStarAlgebra.increasingApproximateUnit A
  simpa only [sub_self] using (hau.tendsto_mul_right a).sub (hau.tendsto_mul_left a)

/-- Every separable, possibly nonunital C⋆-algebra admits a sequence of positive
contractions that approximates every algebra element on both sides. -/
theorem exists_positive_contractive_approximate_unit_sequence [SeparableSpace A] :
    ∃ u : ℕ → A, (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ a, Tendsto (fun n => a * u n) atTop (𝓝 a)) ∧
      (∀ a, Tendsto (fun n => u n * a) atTop (𝓝 a)) := by
  classical
  let d := denseSeq A
  have hd : DenseRange d := denseRange_denseSeq A
  have hchoice : ∀ n : ℕ, ∃ e : A, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧
      ∀ j ≤ n, ‖d j * e - d j‖ < 1 / ((n : ℝ) + 1) ∧
        ‖e * d j - d j‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨e, he0, he1, herr⟩ := exists_positive_contraction_approximate_on
      ((Finset.range (n + 1)).image d) (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨e, he0, he1, fun j hj => herr (d j) ?_⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩
  choose u hu0 hu1 huerr using hchoice
  refine ⟨u, hu0, hu1, ?_, ?_⟩
  · intro a
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hd a (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (show 0 < ε / 2 by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max j N, fun n hn => ?_⟩
    have hjn : j ≤ n := (le_max_left j N).trans hn
    have hNn : N ≤ n := (le_max_right j N).trans hn
    have hsample := (huerr n j hjn).1
    have herror := norm_right_unit_error_le (u n) a (d j) (hu1 n)
    rw [dist_eq_norm] at hj ⊢
    have htail := hN n hNn
    linarith
  · intro a
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hd a (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (show 0 < ε / 2 by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max j N, fun n hn => ?_⟩
    have hjn : j ≤ n := (le_max_left j N).trans hn
    have hNn : N ≤ n := (le_max_right j N).trans hn
    have hsample := (huerr n j hjn).2
    have herror := norm_left_unit_error_le (u n) a (d j) (hu1 n)
    rw [dist_eq_norm] at hj ⊢
    have htail := hN n hNn
    linarith

/-- The sequence above can simultaneously be chosen internally quasicentral.
The commutator test element is in the same algebra as the sequence. -/
theorem exists_internally_quasicentral_approximate_unit_sequence [SeparableSpace A] :
    ∃ u : ℕ → A, (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ a, Tendsto (fun n => a * u n) atTop (𝓝 a)) ∧
      (∀ a, Tendsto (fun n => u n * a) atTop (𝓝 a)) ∧
      (∀ a, Tendsto (fun n => u n * a - a * u n) atTop (𝓝 0)) := by
  obtain ⟨u, hu0, hu1, hleft, hright⟩ :=
    exists_positive_contractive_approximate_unit_sequence (A := A)
  refine ⟨u, hu0, hu1, hleft, hright, fun a => ?_⟩
  simpa only [sub_self] using (hright a).sub (hleft a)

end CStarPrerequisites

section WeakConvexification

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {l : Filter ι} [l.NeBot]

/-- A weakly null family has zero in the norm closure of the real convex hull
of every eventual tail. This is the Hahn–Banach convexification step. -/
theorem zero_mem_closure_convexHull_of_weak_tendsto (v : ι → V)
    (hv : Tendsto (fun i => toWeakSpace ℝ V (v i)) l (𝓝 0))
    (s : Set ι) (hs : s ∈ l) :
    (0 : V) ∈ closure (convexHull ℝ (v '' s)) := by
  have hweak : toWeakSpace ℝ V (0 : V) ∈
      closure (toWeakSpace ℝ V '' convexHull ℝ (v '' s)) := by
    apply mem_closure_of_tendsto (by simpa using hv)
    filter_upwards [hs] with i hi
    exact ⟨v i, subset_convexHull ℝ (v '' s) ⟨i, hi, rfl⟩, rfl⟩
  rw [← (convex_convexHull ℝ (v '' s)).toWeakSpace_closure ℝ] at hweak
  obtain ⟨x, hx, hx0⟩ := hweak
  have : x = 0 := (toWeakSpace ℝ V).injective hx0
  simpa only [this] using hx

/-- Weakly null vectors have finite convex combinations of any eventual
tail with arbitrarily small norm. Samples and coefficients are explicit. -/
theorem exists_finite_convex_combination_norm_lt_of_weak_tendsto (v : ι → V)
    (hv : Tendsto (fun i => toWeakSpace ℝ V (v i)) l (𝓝 0))
    (s : Set ι) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (j : κ → ι),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, j i ∈ s) ∧
        ‖∑ i, w i • v (j i)‖ < ε := by
  classical
  obtain ⟨x, hx, hnorm⟩ := Metric.mem_closure_iff.mp
    (zero_mem_closure_convexHull_of_weak_tendsto v hv s hs) ε hε
  obtain ⟨κ, hκ, w, z, hw0, hw1, hz, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hx
  let : Fintype κ := hκ
  change ∀ i, ∃ j ∈ s, v j = z i at hz
  choose j hj hjz using hz
  refine ⟨κ, hκ, w, j, hw0, hw1, hj, ?_⟩
  have hsum' : ∑ i, w i • v (j i) = x := by
    calc
      ∑ i, w i • v (j i) = ∑ i, w i • z i :=
        Finset.sum_congr rfl (fun i _ => by rw [hjz i])
      _ = x := hsum
  simpa only [hsum', dist_zero_left] using hnorm

end WeakConvexification

end BC4lean.KKTheory
