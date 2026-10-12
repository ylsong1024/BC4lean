import BC4lean.KasparovAugmentedAlgebra
import BC4lean.CFCAlmostCommute
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Paired countable selection for the discrete technical theorem

At each stage the first coefficient is selected in the augmented first
algebra. The compact coefficient is selected afterwards, so its genuine
approximate-unit tests include the products of that already selected
coefficient with the E₂ and discrete-family values. Both sequences are
increasing. Geometric budgets give actual norm-summable error series.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

/-- The common summable budget for the countable diagonal construction. -/
def kasparovSelectionBudget (n : ℕ) : ℝ := ((1 : ℝ) / 2) ^ n

theorem kasparovSelectionBudget_pos (n : ℕ) : 0 < kasparovSelectionBudget n := by
  exact pow_pos (by norm_num) n

theorem kasparovSelectionBudget_summable : Summable kasparovSelectionBudget :=
  summable_geometric_two

theorem kasparovSelectionBudget_tendsto :
    Tendsto kasparovSelectionBudget atTop (𝓝 0) :=
  kasparovSelectionBudget_summable.tendsto_atTop_zero

/-- Every fixed test enters the finite diagonal and then has errors
bounded by the actual geometric budget. -/
theorem tendsto_of_diagonal_selection_bound
    {V : Type*} [NormedAddCommGroup V] (z : ℕ → V) (v : V) (k : ℕ)
    (hz : ∀ n, 1 ≤ n → k ≤ n → ‖z n - v‖ < kasparovSelectionBudget n) :
    Tendsto z atTop (𝓝 v) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (kasparovSelectionBudget_tendsto.eventually (gt_mem_nhds hε))
  refine ⟨max 1 (max k N), fun n hn => ?_⟩
  have hn1 := (le_max_left 1 (max k N)).trans hn
  have hnk := (le_max_left k N).trans ((le_max_right 1 (max k N)).trans hn)
  have hnN := (le_max_right k N).trans ((le_max_right 1 (max k N)).trans hn)
  rw [dist_eq_norm]
  exact (hz n hn1 hnk).trans (hN n hnN)

/-- Each error controlled on a countable diagonal is actually summable;
the omitted finite beginning is allowed by the comparison theorem. -/
theorem summable_of_diagonal_selection_bound
    {V : Type*} [NormedAddCommGroup V] [CompleteSpace V] (z : ℕ → V) (k : ℕ)
    (hz : ∀ n, 1 ≤ n → k ≤ n → ‖z n‖ < kasparovSelectionBudget n) : Summable z := by
  apply kasparovSelectionBudget_summable.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max 1 k)] with n hn
  exact (hz n ((le_max_left 1 k).trans hn) ((le_max_right 1 k).trans hn)).le

section FiniteModuli
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

private theorem exists_positive_common_lower_bound {ι : Type*} (s : Finset ι)
    (δ : ι → ℝ) (hδ : ∀ i ∈ s, 0 < δ i) :
    ∃ η : ℝ, 0 < η ∧ ∀ i ∈ s, η ≤ δ i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi hs =>
    obtain ⟨η, hη, hηs⟩ := hs (fun j hj => hδ j (Finset.mem_insert_of_mem hj))
    refine ⟨min (δ i) η, lt_min (hδ i (Finset.mem_insert_self _ _)) hη, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hηs j hj)

/-- A single positive tolerance controls square-root commutators for an
actual finite family and square-root errors for every star automorphism. -/
theorem exists_finite_sqrt_selection_modulus (s : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      (∀ b ∈ s, ∀ a : A, 0 ≤ a → ‖a‖ ≤ 1 →
        ‖a * b - b * a‖ < η → ‖CFC.sqrt a * b - b * CFC.sqrt a‖ < ε) ∧
      (∀ (α : A ≃⋆ₐ[ℂ] A) (a : A), 0 ≤ a → ‖a‖ ≤ 1 →
        ‖α a - a‖ < η → ‖α (CFC.sqrt a) - CFC.sqrt a‖ < ε) := by
  choose δ hδ hcomm using fun b : A => exists_cfc_sqrt_commutator_modulus b ε hε
  obtain ⟨η₁, hη₁, hηs⟩ := exists_positive_common_lower_bound s δ (fun b _ => hδ b)
  obtain ⟨η₂, hη₂, hauto⟩ := exists_cfc_sqrt_automorphism_modulus (A := A) ε hε
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_, ?_⟩
  · intro b hb a ha0 ha1 hab
    exact hcomm b a ha0 ha1 (hab.trans_le ((min_le_left _ _).trans (hηs b hb)))
  · intro α a ha0 ha1 ha
    exact hauto α a ha0 ha1 (ha.trans_le (min_le_right _ _))

end FiniteModuli

universe uA
section PairSelection
variable {A : Type uA} {Γ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
  [Nonempty Γ] [Countable Γ]
variable (U K : NonUnitalStarSubalgebra ℂ A)
  [hUclosed : IsClosed (U : Set A)] [hKclosed : IsClosed (K : Set A)]

local instance : PartialOrder U := CStarAlgebra.spectralOrder _
local instance : Preorder U := (CStarAlgebra.spectralOrder U).toPreorder
local instance : LE U := (CStarAlgebra.spectralOrder U).toLE
local instance : StarOrderedRing U := CStarAlgebra.spectralOrderedRing _
local instance : PartialOrder K := CStarAlgebra.spectralOrder _
local instance : Preorder K := (CStarAlgebra.spectralOrder K).toPreorder
local instance : LE K := (CStarAlgebra.spectralOrder K).toLE
local instance : StarOrderedRing K := CStarAlgebra.spectralOrderedRing _

/-- The concrete output of the recursive paired selection. The compact
products are tested after the current first coefficient is chosen. -/
structure IsKasparovCountableSelection
    (δ t b : ℕ → A) (qU : ℕ → U) (qK : ℕ → K)
    (γ : ℕ → Γ) (αU : Γ → U ≃⋆ₐ[ℂ] U) (αK : Γ → K ≃⋆ₐ[ℂ] K)
    (τ : ℕ → ℝ) (u : ℕ → U) (e : ℕ → K) : Prop where
  zeroU : u 0 = 0
  zeroK : e 0 = 0
  monotoneU : Monotone u
  monotoneK : Monotone e
  nonnegU : ∀ n, 0 ≤ u n
  nonnegK : ∀ n, 0 ≤ e n
  strictU : ∀ n, ‖u n‖ < 1
  strictK : ∀ n, ‖e n‖ < 1
  testsU : ∀ n, 1 ≤ n → ∀ k ≤ n,
    ‖qU k * u n - qU k‖ < kasparovSelectionBudget n ∧
      ‖u n * qU k - qU k‖ < kasparovSelectionBudget n
  testsK : ∀ n, 1 ≤ n → ∀ k ≤ n,
    ‖qK k * e n - qK k‖ < kasparovSelectionBudget n ∧
      ‖e n * qK k - qK k‖ < kasparovSelectionBudget n
  commutatorU : ∀ n, 1 ≤ n → ∀ k ≤ n,
    ‖(u n : A) * δ k - δ k * (u n : A)‖ < kasparovSelectionBudget n
  commutatorK : ∀ n, 1 ≤ n → ∀ k ≤ n,
    ‖(e n : A) * t k - t k * (e n : A)‖ < τ n
  actionU : ∀ n, 1 ≤ n → ∀ k ≤ n,
    ‖αU (γ k) (u n) - u n‖ < kasparovSelectionBudget n
  actionK : ∀ n, 1 ≤ n → ∀ k ≤ n, ‖αK (γ k) (e n) - e n‖ < τ n
  products_left : ∀ n, 1 ≤ n → ∀ k ≤ n,
    ‖(e n : A) * ((u n : A) * b k) - (u n : A) * b k‖ <
      (kasparovSelectionBudget n) ^ 2 / (‖b k‖ + 1)
  products_right : ∀ n, 1 ≤ n → ∀ k ≤ n,
    ‖(b k * (u n : A)) * (e n : A) - b k * (u n : A)‖ <
      (kasparovSelectionBudget n) ^ 2 / (‖b k‖ + 1)

/-- The genuine finite normalized selections construct both sequences
recursively, including the stage-dependent compact product tests. -/
theorem exists_kasparov_countable_selection
    (hK : IsClosedTwoSidedStarIdeal K)
    (δ t b : ℕ → A) (qU : ℕ → U) (qK : ℕ → K)
    (hnormal : ∀ k, ∀ a ∈ U, δ k * a - a * δ k ∈ U)
    (hproducts : ∀ a ∈ U, ∀ k, a * b k ∈ K ∧ b k * a ∈ K)
    (αU : Γ → U ≃⋆ₐ[ℂ] U) (αK : Γ → K ≃⋆ₐ[ℂ] K)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n) :
    ∃ (γ : ℕ → Γ) (u : ℕ → U) (e : ℕ → K), Function.Surjective γ ∧
      IsKasparovCountableSelection U K δ t b qU qK γ αU αK τ u e := by
  classical
  obtain ⟨γ, hγ⟩ := exists_surjective_nat Γ
  let P := {p : U × K // (0 ≤ p.1 ∧ ‖p.1‖ < 1) ∧ (0 ≤ p.2 ∧ ‖p.2‖ < 1)}
  let good (n : ℕ) (p : P) (z : U × K) : Prop :=
    p.val.1 ≤ z.1 ∧ p.val.2 ≤ z.2 ∧
    (0 ≤ z.1 ∧ ‖z.1‖ < 1) ∧ (0 ≤ z.2 ∧ ‖z.2‖ < 1) ∧
    (∀ k ≤ n, ‖qU k * z.1 - qU k‖ < kasparovSelectionBudget n ∧
      ‖z.1 * qU k - qU k‖ < kasparovSelectionBudget n) ∧
    (∀ k ≤ n, ‖qK k * z.2 - qK k‖ < kasparovSelectionBudget n ∧
      ‖z.2 * qK k - qK k‖ < kasparovSelectionBudget n) ∧
    (∀ k ≤ n, ‖(z.1 : A) * δ k - δ k * (z.1 : A)‖ < kasparovSelectionBudget n) ∧
    (∀ k ≤ n, ‖(z.2 : A) * t k - t k * (z.2 : A)‖ < τ n) ∧
    (∀ k ≤ n, ‖αU (γ k) z.1 - z.1‖ < kasparovSelectionBudget n) ∧
    (∀ k ≤ n, ‖αK (γ k) z.2 - z.2‖ < τ n) ∧
    (∀ k ≤ n, ‖(z.2 : A) * ((z.1 : A) * b k) - (z.1 : A) * b k‖ <
      (kasparovSelectionBudget n) ^ 2 / (‖b k‖ + 1)) ∧
    (∀ k ≤ n, ‖(b k * (z.1 : A)) * (z.2 : A) - b k * (z.1 : A)‖ <
      (kasparovSelectionBudget n) ^ 2 / (‖b k‖ + 1))
  have hmem {V : Type uA} [DecidableEq V] (f : ℕ → V) (k n : ℕ) (hk : k ≤ n) :
      f k ∈ (Finset.range (n + 1)).image f :=
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩
  have hchoice (n : ℕ) (p : P) : ∃ z : U × K, good n p z := by
    obtain ⟨v, hpv, hv0, hv1, _, hvδ, hvα, hvq⟩ :=
      NormalizedQuasicentral.exists_positive_strict_contraction_finite_errors_above
        (NonUnitalStarSubalgebraClass.subtype U) Subtype.coe_injective
        p.val.1 p.property.1.1 p.property.1.2
        ((Finset.range (n + 1)).image δ) ((Finset.range (n + 1)).image (fun k => αU (γ k)))
        ((Finset.range (n + 1)).image qU)
        (by
          intro a ha j
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
          exact ⟨⟨_, hnormal k j j.property⟩, rfl⟩)
        (by
          intro a ha j
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
          exact ⟨⟨_, star_normalizes_starSubalgebra U (δ k) (hnormal k) j j.property⟩, rfl⟩)
        (kasparovSelectionBudget n) (kasparovSelectionBudget_pos n)
    let L : ℕ → K := fun k => ⟨(v : A) * b k, (hproducts v v.property k).1⟩
    let R : ℕ → K := fun k => ⟨b k * (v : A), (hproducts v v.property k).2⟩
    let C : ℝ := 1 + ∑ k ∈ Finset.range (n + 1), ‖b k‖
    have hC : 0 < C := by
      dsimp [C]
      have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (n + 1)) => norm_nonneg (b k))
      linarith
    let ε : ℝ := min (τ n) (min (kasparovSelectionBudget n)
      ((kasparovSelectionBudget n) ^ 2 / C))
    have hε : 0 < ε := lt_min (hτ n)
      (lt_min (kasparovSelectionBudget_pos n) (div_pos (sq_pos_of_pos (kasparovSelectionBudget_pos n)) hC))
    obtain ⟨w, hpw, hw0, hw1, _, hwt, hwα, hwq⟩ :=
      NormalizedQuasicentral.exists_positive_strict_contraction_finite_errors_above
        (NonUnitalStarSubalgebraClass.subtype K) Subtype.coe_injective
        p.val.2 p.property.2.1 p.property.2.2
        ((Finset.range (n + 1)).image t) ((Finset.range (n + 1)).image (fun k => αK (γ k)))
        (((Finset.range (n + 1)).image qK) ∪
          (((Finset.range (n + 1)).image L) ∪ ((Finset.range (n + 1)).image R)))
        (fun a _ j => ⟨⟨_, K.sub_mem (hK.left_mul a j.property) (hK.right_mul a j.property)⟩, rfl⟩)
        (fun a _ j => ⟨⟨_, K.sub_mem (hK.left_mul (star a) j.property)
          (hK.right_mul (star a) j.property)⟩, rfl⟩) ε hε
    have hετ : ε ≤ τ n := min_le_left _ _
    have hεbudget : ε ≤ kasparovSelectionBudget n :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hεproducts (k : ℕ) (hk : k ≤ n) :
        ε ≤ (kasparovSelectionBudget n) ^ 2 / (‖b k‖ + 1) := by
      have hb : ‖b k‖ + 1 ≤ C := by
        dsimp [C]
        have h := Finset.single_le_sum (fun j _ => norm_nonneg (b j))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
        linarith
      exact ((min_le_right _ _).trans (min_le_right _ _)).trans
        (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hb)
    refine ⟨(v, w), hpv, hpw, ⟨hv0, hv1⟩, ⟨hw0, hw1⟩,
      (fun k hk => hvq _ (hmem qU k n hk)), ?_,
      (fun k hk => hvδ _ (hmem δ k n hk)),
      (fun k hk => (hwt _ (hmem t k n hk)).trans_le hετ),
      (fun k hk => hvα _ (hmem (fun j => αU (γ j)) k n hk)),
      (fun k hk => (hwα _ (hmem (fun j => αK (γ j)) k n hk)).trans_le hετ), ?_, ?_⟩
    · intro k hk
      have h := hwq _ (Finset.mem_union_left _ (hmem qK k n hk))
      exact ⟨h.1.trans_le hεbudget, h.2.trans_le hεbudget⟩
    · intro k hk
      have h := hwq _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (hmem L k n hk)))
      exact h.2.trans_le (hεproducts k hk)
    · intro k hk
      have h := hwq _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (hmem R k n hk)))
      exact h.1.trans_le (hεproducts k hk)
  choose z hz using hchoice
  let recP : ℕ → P := Nat.rec ⟨(0, 0), by simp⟩
    (fun n p => ⟨z (n + 1) p, (hz (n + 1) p).2.2.1, (hz (n + 1) p).2.2.2.1⟩)
  let u : ℕ → U := fun n => (recP n).val.1
  let e : ℕ → K := fun n => (recP n).val.2
  have hstage (n : ℕ) (hn : 1 ≤ n) : good n (recP (n - 1)) (u n, e n) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [u, e, recP, Nat.succ_sub_one, Nat.rec_add_one] using hz (m + 1) (recP m)
  refine ⟨γ, u, e, hγ, ?_⟩
  constructor
  · rfl
  · rfl
  · exact monotone_nat_of_le_succ fun n => (hz (n + 1) (recP n)).1
  · exact monotone_nat_of_le_succ fun n => (hz (n + 1) (recP n)).2.1
  · exact fun n => (recP n).property.1.1
  · exact fun n => (recP n).property.2.1
  · exact fun n => (recP n).property.1.2
  · exact fun n => (recP n).property.2.2
  · exact fun n hn => (hstage n hn).2.2.2.2.1
  · exact fun n hn => (hstage n hn).2.2.2.2.2.1
  · exact fun n hn => (hstage n hn).2.2.2.2.2.2.1
  · exact fun n hn => (hstage n hn).2.2.2.2.2.2.2.1
  · exact fun n hn => (hstage n hn).2.2.2.2.2.2.2.2.1
  · exact fun n hn => (hstage n hn).2.2.2.2.2.2.2.2.2.1
  · exact fun n hn => (hstage n hn).2.2.2.2.2.2.2.2.2.2.1
  · exact fun n hn => (hstage n hn).2.2.2.2.2.2.2.2.2.2.2

namespace IsKasparovCountableSelection
variable {U K}
  {δ t b : ℕ → A} {qU : ℕ → U} {qK : ℕ → K}
  {γ : ℕ → Γ} {αU : Γ → U ≃⋆ₐ[ℂ] U} {αK : Γ → K ≃⋆ₐ[ℂ] K}
  {τ : ℕ → ℝ} {u : ℕ → U} {e : ℕ → K}
  (h : IsKasparovCountableSelection U K δ t b qU qK γ αU αK τ u e)

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] [Nonempty Γ] [Countable Γ] in
include h in
/-- The selected first sequence is a genuine two-sided approximate unit,
derived from its diagonal tests on the original countable AU. -/
theorem approximateUnitU
    (hqleft : ∀ a, Tendsto (fun n => a * qU n) atTop (𝓝 a))
    (hqright : ∀ a, Tendsto (fun n => qU n * a) atTop (𝓝 a)) (a : U) :
    Tendsto (fun n => a * u n) atTop (𝓝 a) ∧
      Tendsto (fun n => u n * a) atTop (𝓝 a) :=
  tendsto_twoSided_mul_of_approximateUnit_tests u qU (fun n => (h.strictU n).le) a
    (hqleft a) (hqright a)
    (fun k => tendsto_of_diagonal_selection_bound _ _ k (fun n hn hk => (h.testsU n hn k hk).1))
    (fun k => tendsto_of_diagonal_selection_bound _ _ k (fun n hn hk => (h.testsU n hn k hk).2))

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] [Nonempty Γ] [Countable Γ] in
include h in
/-- The selected compact sequence is a genuine two-sided approximate
unit, including on compact coefficients not listed in the diagonal. -/
theorem approximateUnitK
    (hqleft : ∀ a, Tendsto (fun n => a * qK n) atTop (𝓝 a))
    (hqright : ∀ a, Tendsto (fun n => qK n * a) atTop (𝓝 a)) (a : K) :
    Tendsto (fun n => a * e n) atTop (𝓝 a) ∧
      Tendsto (fun n => e n * a) atTop (𝓝 a) :=
  tendsto_twoSided_mul_of_approximateUnit_tests e qK (fun n => (h.strictK n).le) a
    (hqleft a) (hqright a)
    (fun k => tendsto_of_diagonal_selection_bound _ _ k (fun n hn hk => (h.testsK n hn k hk).1))
    (fun k => tendsto_of_diagonal_selection_bound _ _ k (fun n hn hk => (h.testsK n hn k hk).2))

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] [Nonempty Γ] [Countable Γ] in
include h in
theorem commutatorU_summable (k : ℕ) :
    Summable (fun n => (u n : A) * δ k - δ k * (u n : A)) :=
  summable_of_diagonal_selection_bound _ k (fun n hn hk => h.commutatorU n hn k hk)

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] [Nonempty Γ] [Countable Γ] in
include h in
theorem actionU_summable (k : ℕ) :
    Summable (fun n => αU (γ k) (u n) - u n) :=
  summable_of_diagonal_selection_bound _ k (fun n hn hk => h.actionU n hn k hk)

end IsKasparovCountableSelection
end PairSelection
end BC4lean.KKTheory
