import BC4lean.KasparovCountableSelection

/-! # Summable square-root band controls

One finite-family CFC modulus is chosen at every stage. Each endpoint
is selected with the smaller of the two neighboring moduli. Consequently
the commutator and action error of the positive increment is small enough
for its actual square root, with a geometric output budget.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

omit [Nontrivial A] in
/-- The neighboring-stage tolerance properties discharged by the actual
finite CFC modulus construction. -/
structure IsKasparovBandControlTolerance (t : ℕ → A) (τ : ℕ → ℝ) : Prop where
  positive : ∀ n, 0 < τ n
  budget : ∀ n, τ n ≤ kasparovSelectionBudget n
  commutator : ∀ n k, k ≤ n → ∀ a c : A, 0 ≤ c - a → ‖c - a‖ ≤ 1 →
    ‖a * t k - t k * a‖ < τ n → ‖c * t k - t k * c‖ < τ (n + 1) →
    ‖CFC.sqrt (c - a) * t k - t k * CFC.sqrt (c - a)‖ < kasparovSelectionBudget n
  action : ∀ n (α : A ≃⋆ₐ[ℂ] A) (a c : A), 0 ≤ c - a → ‖c - a‖ ≤ 1 →
    ‖α a - a‖ < τ n → ‖α c - c‖ < τ (n + 1) →
    ‖α (CFC.sqrt (c - a)) - CFC.sqrt (c - a)‖ < kasparovSelectionBudget n

/-- The finite CFC moduli determine explicit neighboring-stage endpoint
tolerances. Both endpoint errors then control the actual band square root. -/
theorem exists_kasparov_band_control_tolerances (t : ℕ → A) :
    ∃ τ : ℕ → ℝ, (∀ n, 0 < τ n) ∧ (∀ n, τ n ≤ kasparovSelectionBudget n) ∧
      (∀ n k, k ≤ n → ∀ a c : A, 0 ≤ c - a → ‖c - a‖ ≤ 1 →
        ‖a * t k - t k * a‖ < τ n →
        ‖c * t k - t k * c‖ < τ (n + 1) →
        ‖CFC.sqrt (c - a) * t k - t k * CFC.sqrt (c - a)‖ < kasparovSelectionBudget n) ∧
      (∀ n (α : A ≃⋆ₐ[ℂ] A) (a c : A), 0 ≤ c - a → ‖c - a‖ ≤ 1 →
        ‖α a - a‖ < τ n → ‖α c - c‖ < τ (n + 1) →
        ‖α (CFC.sqrt (c - a)) - CFC.sqrt (c - a)‖ < kasparovSelectionBudget n) := by
  classical
  choose η hη hcomm hauto using fun n : ℕ =>
    exists_finite_sqrt_selection_modulus ((Finset.range (n + 1)).image t)
      (kasparovSelectionBudget n) (kasparovSelectionBudget_pos n)
  let τ : ℕ → ℝ := fun n => min (kasparovSelectionBudget n) (min (η n) (η (n - 1)) / 4)
  have hτ0 (n : ℕ) : 0 < τ n := lt_min (kasparovSelectionBudget_pos n)
    (div_pos (lt_min (hη n) (hη (n - 1))) (by norm_num))
  have hτ1 (n : ℕ) : τ n ≤ kasparovSelectionBudget n := min_le_left _ _
  have hnear (n : ℕ) : τ n + τ (n + 1) ≤ η n / 2 := by
    have hleft : τ n ≤ η n / 4 :=
      (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    have hright : τ (n + 1) ≤ η n / 4 := by
      simpa only [τ, Nat.add_sub_cancel] using
        (min_le_right (kasparovSelectionBudget (n + 1)) _).trans
          (div_le_div_of_nonneg_right (min_le_right (η (n + 1)) (η ((n + 1) - 1)))
            (by norm_num : (0 : ℝ) ≤ 4))
    linarith
  refine ⟨τ, hτ0, hτ1, ?_, ?_⟩
  · intro n k hk a c hac0 hac1 ha hc
    apply hcomm n (t k)
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)
      (c - a) hac0 hac1
    have heq : (c - a) * t k - t k * (c - a) =
        (c * t k - t k * c) - (a * t k - t k * a) := by noncomm_ring
    rw [heq]
    have he := norm_sub_le (c * t k - t k * c) (a * t k - t k * a)
    have hb := hnear n
    have hp := hη n
    linarith
  · intro n α a c hac0 hac1 ha hc
    apply hauto n α (c - a) hac0 hac1
    have heq : α (c - a) - (c - a) = (α c - c) - (α a - a) := by
      rw [map_sub]
      abel
    rw [heq]
    have he := norm_sub_le (α c - c) (α a - a)
    have hb := hnear n
    have hp := hη n
    linarith

theorem exists_kasparov_bandControlTolerance (t : ℕ → A) :
    ∃ τ, IsKasparovBandControlTolerance t τ := by
  obtain ⟨τ, hτ0, hτ1, hcomm, haction⟩ := exists_kasparov_band_control_tolerances t
  exact ⟨τ, hτ0, hτ1, hcomm, haction⟩

omit [Nontrivial A] in
/-- Positive contractive increasing endpoints have positive contractive
increments. This does not compare square roots in operator order. -/
theorem positive_contractive_increment (a c : A) (ha0 : 0 ≤ a)
    (hac : a ≤ c) (hc1 : ‖c‖ ≤ 1) : 0 ≤ c - a ∧ ‖c - a‖ ≤ 1 :=
  ⟨sub_nonneg.mpr hac,
    (CStarAlgebra.norm_le_norm_of_nonneg_of_le (sub_nonneg.mpr hac)
      (sub_le_self c ha0)).trans hc1⟩

omit [Nontrivial A] in
/-- The band error controls imply genuine norm summability for each
fixed ambient test. -/
theorem summable_band_commutators (e t : ℕ → A) (k : ℕ)
    (hband : ∀ n, k ≤ n →
      ‖CFC.sqrt (e (n + 1) - e n) * t k -
        t k * CFC.sqrt (e (n + 1) - e n)‖ < kasparovSelectionBudget n) :
    Summable (fun n => CFC.sqrt (e (n + 1) - e n) * t k -
      t k * CFC.sqrt (e (n + 1) - e n)) :=
  summable_of_diagonal_selection_bound _ k (fun n _ hk => hband n hk)

omit [Nontrivial A] in
/-- The action errors of actual square-root bands are norm-summable by
the same countable diagonal comparison. -/
theorem summable_band_action_errors (e : ℕ → A) (α : A ≃⋆ₐ[ℂ] A) (k : ℕ)
    (hband : ∀ n, k ≤ n →
      ‖α (CFC.sqrt (e (n + 1) - e n)) - CFC.sqrt (e (n + 1) - e n)‖ <
        kasparovSelectionBudget n) :
    Summable (fun n => α (CFC.sqrt (e (n + 1) - e n)) -
      CFC.sqrt (e (n + 1) - e n)) :=
  summable_of_diagonal_selection_bound _ k (fun n _ hk => hband n hk)

end BC4lean.KKTheory
