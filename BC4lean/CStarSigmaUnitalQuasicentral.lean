import BC4lean.NormalizedQuasicentralApproximateUnit

/-! # Quasicentral selection from a genuine countable approximate unit

Sigma-unital coefficient algebras need not be separable. A specified genuine
countable approximate unit supplies the coefficient tests. Small errors on
those tests imply two-sided convergence on every coefficient by multiplication,
without a dense countable sequence of all algebra elements.
-/

noncomputable section
namespace BC4lean.KKTheory.NormalizedQuasicentral

open Filter
open scoped Topology

section TestErrorBounds
variable {R : Type*} [NonUnitalNormedRing R]

/-- Right approximate-unit errors are controlled by one actual approximate
unit test, with a contractive selected coefficient. -/
theorem norm_right_unit_error_via_test (u a q : R) (hu : ‖u‖ ≤ 1) :
    ‖a * u - a‖ ≤ 2 * ‖a - a * q‖ + ‖a‖ * ‖q * u - q‖ := by
  have heq : a * u - a = (a - a * q) * u + a * (q * u - q) - (a - a * q) := by
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖(a - a * q) * u‖ + ‖a * (q * u - q)‖ + ‖a - a * q‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖a - a * q‖ * ‖u‖ + ‖a‖ * ‖q * u - q‖ + ‖a - a * q‖ := by
      gcongr <;> exact norm_mul_le _ _
    _ ≤ ‖a - a * q‖ * 1 + ‖a‖ * ‖q * u - q‖ + ‖a - a * q‖ := by gcongr
    _ = _ := by ring

/-- The corresponding left approximate-unit error bound. -/
theorem norm_left_unit_error_via_test (u a q : R) (hu : ‖u‖ ≤ 1) :
    ‖u * a - a‖ ≤ 2 * ‖a - q * a‖ + ‖a‖ * ‖u * q - q‖ := by
  have heq : u * a - a = u * (a - q * a) + (u * q - q) * a - (a - q * a) := by
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖u * (a - q * a)‖ + ‖(u * q - q) * a‖ + ‖a - q * a‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖u‖ * ‖a - q * a‖ + ‖u * q - q‖ * ‖a‖ + ‖a - q * a‖ := by
      gcongr <;> exact norm_mul_le _ _
    _ ≤ 1 * ‖a - q * a‖ + ‖u * q - q‖ * ‖a‖ + ‖a - q * a‖ := by gcongr
    _ = _ := by ring

end TestErrorBounds

variable {A J Γ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [Nonempty Γ] [Countable Γ]

/-- Recursive selections from genuine convex order tails give an increasing
positive contractive quasicentral coefficient approximate-unit sequence,
asymptotically invariant under a countable family of coefficient
automorphisms. The ambient algebra need not be separable. -/
theorem exists_monotone_sequence_from_countable_approximateUnit
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι) (a : ℕ → A)
    (hnormal : ∀ n, ∀ j : J, ∃ k : J, ι k = a n * ι j - ι j * a n)
    (hnormalStar : ∀ n, ∀ j : J, ∃ k : J,
      ι k = star (a n) * ι j - ι j * star (a n))
    (q : ℕ → J)
    (hqleft : ∀ j, Tendsto (fun n => j * q n) atTop (𝓝 j))
    (hqright : ∀ j, Tendsto (fun n => q n * j) atTop (𝓝 j))
    (α : Γ → J ≃⋆ₐ[ℂ] J) :
    ∃ u : ℕ → J, u 0 = 0 ∧ Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ n, star (u n) = u n) ∧
      (∀ j : J, Tendsto (fun n => j * u n) atTop (𝓝 j)) ∧
      (∀ j : J, Tendsto (fun n => u n * j) atTop (𝓝 j)) ∧
      (∀ k : ℕ, Tendsto (fun n => ι (u n) * a k - a k * ι (u n)) atTop (𝓝 0)) ∧
      (∀ g : Γ, Tendsto (fun n => α g (u n) - u n) atTop (𝓝 0)) := by
  classical
  let dJ := q
  obtain ⟨γ, hγ⟩ := exists_surjective_nat Γ
  let P := {p : J // 0 ≤ p ∧ ‖p‖ < 1}
  have hchoice : ∀ (n : ℕ) (p : P), ∃ e : J, (p : J) ≤ e ∧ 0 ≤ e ∧ ‖e‖ < 1 ∧
      star e = e ∧
      (∀ k ≤ n, ‖ι e * a k - a k * ι e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖α (γ k) e - e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖dJ k * e - dJ k‖ < 1 / ((n : ℝ) + 1) ∧
        ‖e * dJ k - dJ k‖ < 1 / ((n : ℝ) + 1)) := by
    intro n p
    obtain ⟨e, hep, he0, he1, hestar, heA, heΓ, heJ⟩ :=
      exists_positive_strict_contraction_finite_errors_above ι hι p.val p.property.1 p.property.2
        ((Finset.range (n + 1)).image a) ((Finset.range (n + 1)).image (fun k => α (γ k)))
        ((Finset.range (n + 1)).image dJ)
        (fun b hb => by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
          exact hnormal k)
        (fun b hb => by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
          exact hnormalStar k)
        (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨e, hep, he0, he1, hestar,
      fun k hk => heA _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heΓ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heJ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)⟩
  choose v hvAbove hv0 hv1 _hvStar hvA hvΓ hvJ using hchoice
  let uRec : ℕ → P := Nat.rec ⟨0, by simp⟩
    (fun n p => ⟨v n p, hv0 n p, hv1 n p⟩)
  let u : ℕ → J := fun n => (uRec n).val
  have hu0 (n : ℕ) : 0 ≤ u n := (uRec n).property.1
  have hu1 (n : ℕ) : ‖u n‖ ≤ 1 := (uRec n).property.2.le
  have hustar (n : ℕ) : star (u n) = u n := (IsSelfAdjoint.of_nonneg (hu0 n)).star_eq
  have huMono : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    exact hvAbove n (uRec n)
  have huA (n k : ℕ) (hk : k ≤ n) :
      ‖ι (u (n + 1)) * a k - a k * ι (u (n + 1))‖ < 1 / ((n : ℝ) + 1) :=
    hvA n (uRec n) k hk
  have huΓ (n k : ℕ) (hk : k ≤ n) :
      ‖α (γ k) (u (n + 1)) - u (n + 1)‖ < 1 / ((n : ℝ) + 1) :=
    hvΓ n (uRec n) k hk
  have huJ (n k : ℕ) (hk : k ≤ n) :
      ‖dJ k * u (n + 1) - dJ k‖ < 1 / ((n : ℝ) + 1) ∧
        ‖u (n + 1) * dJ k - dJ k‖ < 1 / ((n : ℝ) + 1) :=
    hvJ n (uRec n) k hk
  refine ⟨u, rfl, huMono, hu0, hu1, hustar, ?_, ?_, ?_, ?_⟩
  · intro j
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hq : Tendsto (fun k => ‖j - j * q k‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((tendsto_const_nhds (x := j)).sub (hqleft j)).norm
    obtain ⟨k, hk⟩ := (hq.eventually (gt_mem_nhds (by positivity : 0 < ε / 4))).exists
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / (2 * (‖j‖ + 1)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := (huJ n k hkn).1
    have herror := norm_right_unit_error_via_test (u (n + 1)) j (q k) (hu1 (n + 1))
    have htail := hN n hNn
    have hprod : ‖j‖ * ‖q k * u (n + 1) - q k‖ < ε / 2 := by
      have h := (lt_div_iff₀ (show 0 < 2 * (‖j‖ + 1) by positivity)).mp
        (hsample.trans htail)
      nlinarith [norm_nonneg (q k * u (n + 1) - q k)]
    rw [dist_eq_norm]
    linarith
  · intro j
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hq : Tendsto (fun k => ‖j - q k * j‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((tendsto_const_nhds (x := j)).sub (hqright j)).norm
    obtain ⟨k, hk⟩ := (hq.eventually (gt_mem_nhds (by positivity : 0 < ε / 4))).exists
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / (2 * (‖j‖ + 1)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := (huJ n k hkn).2
    have herror := norm_left_unit_error_via_test (u (n + 1)) j (q k) (hu1 (n + 1))
    have htail := hN n hNn
    have hprod : ‖j‖ * ‖u (n + 1) * q k - q k‖ < ε / 2 := by
      have h := (lt_div_iff₀ (show 0 < 2 * (‖j‖ + 1) by positivity)).mp
        (hsample.trans htail)
      nlinarith [norm_nonneg (u (n + 1) * q k - q k)]
    rw [dist_eq_norm]
    linarith
  · intro k
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    rw [dist_zero_right]
    exact (huA n k hkn).trans (hN n hNn)
  · intro g
    obtain ⟨k, rfl⟩ := hγ g
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    rw [dist_zero_right]
    exact (huΓ n k hkn).trans (hN n hNn)


end BC4lean.KKTheory.NormalizedQuasicentral
