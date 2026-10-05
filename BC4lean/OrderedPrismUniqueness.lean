import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Max

/-! # Uniqueness of staircase barycentric coordinates

The original weights and total upper mass determine the split uniquely. This
finite-index proof applies to any chart and any valid cut, including zero
coordinates and cuts between consecutive labels.
-/
noncomputable section
open scoped BigOperators
namespace BC4lean.OrderedPrismWeights

/-- An ordered staircase split is recovered from its combined weights and upper
mass by the explicit min/max formula. The cut need not be a vertex label. -/
theorem upper_eq_of_staircase_cut {ι : Type*} (L : Finset ι) (label : ι → ℕ)
    (hinj : Set.InjOn label (L : Set ι)) (u l w : ι → ℝ)
    (hu : ∀ j ∈ L, 0 ≤ u j) (hl : ∀ j ∈ L, 0 ≤ l j)
    (hw : ∀ j ∈ L, w j = u j + l j) (k : ℕ)
    (hbelow : ∀ j ∈ L, label j < k → u j = 0)
    (habove : ∀ j ∈ L, k < label j → l j = 0)
    (T : ℝ) (hT : ∑ j ∈ L, u j = T) (v : ι) (hv : v ∈ L) :
    u v = min (w v) (max 0 (T - ∑ j ∈ L.filter (fun j => label v < label j), w j)) := by
  classical
  let H := L.filter (fun j => label v < label j)
  have hHL : H ⊆ L := Finset.filter_subset _ _
  have hvH : v ∉ H := by simp [H]
  have hIL : insert v H ⊆ L := Finset.insert_subset hv hHL
  have hsumle : u v + ∑ j ∈ H, u j ≤ T := by
    rw [← Finset.sum_insert hvH, ← hT]
    exact Finset.sum_le_sum_of_subset_of_nonneg hIL (fun j hj _ => hu j hj)
  have hwv : 0 ≤ w v := by rw [hw v hv]; exact add_nonneg (hu v hv) (hl v hv)
  have huwv : u v ≤ w v := by rw [hw v hv]; exact le_add_of_nonneg_right (hl v hv)
  have hhigh (hk : k ≤ label v) : ∑ j ∈ H, w j = ∑ j ∈ H, u j := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hjL, hjv⟩ := Finset.mem_filter.mp hj
    rw [hw j hjL, habove j hjL (by omega), add_zero]
  rcases lt_trichotomy (label v) k with hvk | hvk | hvk
  · have hz : u v = 0 := hbelow v hv hvk
    have hsum : ∑ j ∈ H, u j = T := by
      rw [← hT]
      apply Finset.sum_subset hHL
      intro j hj hn
      have hn' : ¬label v < label j := by
        intro hjv
        exact hn (Finset.mem_filter.mpr ⟨hj, hjv⟩)
      exact hbelow j hj (by omega)
    have hle : T ≤ ∑ j ∈ H, w j := by
      rw [← hsum]
      apply Finset.sum_le_sum
      intro j hj
      rw [hw j (hHL hj)]
      exact le_add_of_nonneg_right (hl j (hHL hj))
    change u v = min (w v) (max 0 (T - ∑ j ∈ H, w j))
    rw [hz, max_eq_left (sub_nonpos.mpr hle), min_eq_right hwv]
  · have hsum : u v + ∑ j ∈ H, u j = T := by
      rw [← Finset.sum_insert hvH, ← hT]
      apply Finset.sum_subset hIL
      intro j hj hn
      have hjne : j ≠ v := by intro h; subst j; exact hn (Finset.mem_insert_self _ _)
      have hn' : ¬label v < label j := by
        intro h
        exact hn (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hj, h⟩))
      have hjlabel : label j ≠ label v := by
        intro he
        exact hjne (hinj hj hv he)
      exact hbelow j hj (by omega)
    have hres : T - ∑ j ∈ H, w j = u v := by
      rw [hhigh (by omega)]
      linarith
    change u v = min (w v) (max 0 (T - ∑ j ∈ H, w j))
    rw [hres, max_eq_right (hu v hv), min_eq_right huwv]
  · have hlv : l v = 0 := habove v hv hvk
    have he : w v = u v := by rw [hw v hv, hlv, add_zero]
    have hle : w v ≤ T - ∑ j ∈ H, w j := by
      rw [he, hhigh (Nat.le_of_lt hvk)]
      linarith
    change u v = min (w v) (max 0 (T - ∑ j ∈ H, w j))
    rw [min_eq_left (hle.trans (le_max_right _ _)), he]

/-- Two staircase splits with the same old coordinates and upper mass coincide,
even when their cuts differ. -/
theorem staircase_split_unique {ι : Type*} (L : Finset ι) (label : ι → ℕ)
    (hinj : Set.InjOn label (L : Set ι)) (u l u' l' w : ι → ℝ)
    (hu : ∀ j ∈ L, 0 ≤ u j) (hl : ∀ j ∈ L, 0 ≤ l j)
    (hu' : ∀ j ∈ L, 0 ≤ u' j) (hl' : ∀ j ∈ L, 0 ≤ l' j)
    (hw : ∀ j ∈ L, w j = u j + l j)
    (hw' : ∀ j ∈ L, w j = u' j + l' j)
    (k k' : ℕ)
    (hbelow : ∀ j ∈ L, label j < k → u j = 0)
    (habove : ∀ j ∈ L, k < label j → l j = 0)
    (hbelow' : ∀ j ∈ L, label j < k' → u' j = 0)
    (habove' : ∀ j ∈ L, k' < label j → l' j = 0)
    (hT : ∑ j ∈ L, u j = ∑ j ∈ L, u' j) :
    ∀ v ∈ L, u v = u' v ∧ l v = l' v := by
  intro v hv
  have he : u v = u' v := by
    rw [upper_eq_of_staircase_cut L label hinj u l w hu hl hw k hbelow habove
      _ rfl v hv,
      upper_eq_of_staircase_cut L label hinj u' l' w hu' hl' hw' k' hbelow' habove'
        _ hT.symm v hv]
  exact ⟨he, by linarith [hw v hv, hw' v hv]⟩

/-- The canonical finite min/max formula fills exactly the requested upper mass,
up to the total available nonnegative weight. -/
theorem sum_min_max_higher {ι : Type*} (L : Finset ι) (label : ι → ℕ)
    (hinj : Set.InjOn label (L : Set ι)) (w : ι → ℝ)
    (hw : ∀ j ∈ L, 0 ≤ w j) (T : ℝ) (hT : 0 ≤ T) :
    ∑ v ∈ L, min (w v) (max 0 (T - ∑ j ∈ L.filter (fun j => label v < label j), w j)) =
      min T (∑ j ∈ L, w j) := by
  classical
  revert hinj hw
  induction L using Finset.strongInductionOn with | _ L ih
  intro hinj hw
  by_cases hL : L = ∅
  · subst L
    simp [min_eq_right hT]
  obtain ⟨v, hv, hmin⟩ := L.exists_min_image label (Finset.nonempty_iff_ne_empty.mpr hL)
  have hinj' : Set.InjOn label ((L.erase v) : Set ι) :=
    fun _ hj _ hk he => hinj (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) he
  have hw' : ∀ j ∈ L.erase v, 0 ≤ w j :=
    fun j hj => hw j (Finset.mem_of_mem_erase hj)
  have hfilters (j : ι) (hj : j ∈ L.erase v) :
      (L.erase v).filter (fun k => label j < label k) =
        L.filter (fun k => label j < label k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hk⟩, hjk⟩
      exact ⟨hk, hjk⟩
    · rintro ⟨hk, hjk⟩
      refine ⟨⟨?_, hk⟩, hjk⟩
      intro hkv
      subst k
      have h := hmin j (Finset.mem_of_mem_erase hj)
      omega
  have hvfilter : L.filter (fun j => label v < label j) = L.erase v := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hj, hlt⟩
      exact ⟨fun he => by subst j; omega, hj⟩
    · rintro ⟨hne, hj⟩
      have hle := hmin j hj
      have hlabel : label v ≠ label j := by
        intro he
        exact hne (hinj hv hj he).symm
      exact ⟨hj, by omega⟩
  have hsum := ih (L.erase v) (Finset.erase_ssubset hv) hinj' hw'
  have hsum' :
      ∑ j ∈ L.erase v, min (w j)
        (max 0 (T - ∑ k ∈ L.filter (fun k => label j < label k), w k)) =
        min T (∑ j ∈ L.erase v, w j) := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hfilters j hj]
  rw [← Finset.sum_erase_add L _ hv, hsum', hvfilter,
    ← Finset.sum_erase_add L w hv]
  let S := ∑ j ∈ L.erase v, w j
  change min T S + min (w v) (max 0 (T - S)) = min T (S + w v)
  by_cases hTS : T ≤ S
  · rw [min_eq_left hTS, max_eq_left (sub_nonpos.mpr hTS),
      min_eq_right (hw v hv), add_zero, min_eq_left (by linarith [hw v hv])]
  · have hST : S ≤ T := le_of_lt (lt_of_not_ge hTS)
    rw [min_eq_right hST, max_eq_right (sub_nonneg.mpr hST)]
    by_cases hTw : T ≤ S + w v
    · rw [min_eq_right (by linarith : T - S ≤ w v), min_eq_left hTw]
      linarith
    · rw [min_eq_left (by linarith : w v ≤ T - S), min_eq_right (by linarith)]

/-- Normalized input weights yield precisely the desired upper mass. -/
theorem sum_min_max_higher_of_le {ι : Type*} (L : Finset ι) (label : ι → ℕ)
    (hinj : Set.InjOn label (L : Set ι)) (w : ι → ℝ)
    (hw : ∀ j ∈ L, 0 ≤ w j) (T : ℝ) (hT : 0 ≤ T)
    (hbound : T ≤ ∑ j ∈ L, w j) :
    ∑ v ∈ L, min (w v) (max 0 (T - ∑ j ∈ L.filter (fun j => label v < label j), w j)) = T := by
  rw [sum_min_max_higher L label hinj w hw T hT, min_eq_left hbound]

/-- The explicit formula always has a staircase cut: at most one label can
receive both an upper and a lower nonzero coordinate. -/
theorem exists_min_max_staircase_cut {ι : Type*} (L : Finset ι) (label : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ j ∈ L, 0 ≤ w j) (T : ℝ) :
    ∃ k : ℕ,
      (∀ v ∈ L, label v < k →
        min (w v) (max 0 (T - ∑ j ∈ L.filter (fun j => label v < label j), w j)) = 0) ∧
      (∀ v ∈ L, k < label v →
        w v - min (w v) (max 0 (T - ∑ j ∈ L.filter (fun j => label v < label j), w j)) = 0) := by
  classical
  let u (v : ι) := min (w v)
    (max 0 (T - ∑ j ∈ L.filter (fun j => label v < label j), w j))
  let U := L.filter (fun v => u v ≠ 0)
  by_cases hU : U.Nonempty
  · obtain ⟨v, hv, hmin⟩ := U.exists_min_image label hU
    obtain ⟨hvL, hvu⟩ := Finset.mem_filter.mp hv
    refine ⟨label v, ?_, ?_⟩
    · intro j hj hjv
      change u j = 0
      by_contra hne
      have h := hmin j (Finset.mem_filter.mpr ⟨hj, hne⟩)
      omega
    · intro j hj hvj
      let H := L.filter (fun x => label v < label x)
      let J := L.filter (fun x => label j < label x)
      have hT : (∑ x ∈ H, w x) < T := by
        apply lt_of_not_ge
        intro hle
        apply hvu
        change min (w v) (max 0 (T - ∑ x ∈ H, w x)) = 0
        rw [max_eq_left (sub_nonpos.mpr hle), min_eq_right (hw v hvL)]
      have hjJ : j ∉ J := by simp [J]
      have hIH : insert j J ⊆ H := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_filter.mpr ⟨hj, hvj⟩
        · obtain ⟨hxL, hjx⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hxL, lt_trans hvj hjx⟩
      have hle : w j + ∑ x ∈ J, w x ≤ ∑ x ∈ H, w x := by
        rw [← Finset.sum_insert hjJ]
        exact Finset.sum_le_sum_of_subset_of_nonneg hIH
          (fun x hx _ => hw x (Finset.mem_filter.mp hx).1)
      have hbound : w j ≤ max 0 (T - ∑ x ∈ J, w x) := by
        apply le_trans _ (le_max_right _ _)
        linarith
      change w j - min (w j) (max 0 (T - ∑ x ∈ J, w x)) = 0
      rw [min_eq_left hbound, sub_self]
  · refine ⟨(L.sup label) + 1, ?_, ?_⟩
    · intro v hv _
      change u v = 0
      by_contra hne
      exact hU ⟨v, Finset.mem_filter.mpr ⟨hv, hne⟩⟩
    · intro v hv hlt
      have hle : label v ≤ L.sup label := Finset.le_sup hv
      omega

/-- Equal projected heights in different integer slabs force the shared
endpoint. Nonnegative normalized barycentric masses then identify its two
representations coordinate by coordinate. -/
theorem adjacent_slab_weights {ι : Type*} (L : Finset ι)
    (l u l' u' : ι → ℝ)
    (hl : ∀ v ∈ L, 0 ≤ l v) (hu : ∀ v ∈ L, 0 ≤ u v)
    (hl' : ∀ v ∈ L, 0 ≤ l' v) (hu' : ∀ v ∈ L, 0 ≤ u' v)
    (hsum : ∑ v ∈ L, (l v + u v) = 1)
    (_hsum' : ∑ v ∈ L, (l' v + u' v) = 1)
    (hbase : ∀ v ∈ L, l v + u v = l' v + u' v)
    (n m : ℕ) (hnm : n < m) (H : ℝ)
    (hH : H = (n : ℝ) + ∑ v ∈ L, u v)
    (hH' : H = (m : ℝ) + ∑ v ∈ L, u' v) :
    m = n + 1 ∧ H = (m : ℝ) ∧
      ∀ v ∈ L, l v = 0 ∧ u' v = 0 ∧ u v = l' v := by
  have hln : 0 ≤ ∑ v ∈ L, l v := Finset.sum_nonneg hl
  have hun : 0 ≤ ∑ v ∈ L, u v := Finset.sum_nonneg hu
  have hl'n : 0 ≤ ∑ v ∈ L, l' v := Finset.sum_nonneg hl'
  have hu'n : 0 ≤ ∑ v ∈ L, u' v := Finset.sum_nonneg hu'
  rw [Finset.sum_add_distrib] at hsum _hsum'
  have hmn : (m : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hmnNat : m ≤ n + 1 := by exact_mod_cast hmn
  have he : m = n + 1 := by omega
  have heR : (m : ℝ) = (n : ℝ) + 1 := by exact_mod_cast he
  have hHeight : H = (m : ℝ) := by linarith
  have hlsum : ∑ v ∈ L, l v = 0 := by linarith
  have hu'sum : ∑ v ∈ L, u' v = 0 := by linarith
  have hlzero := (Finset.sum_eq_zero_iff_of_nonneg hl).mp hlsum
  have hu'zero := (Finset.sum_eq_zero_iff_of_nonneg hu').mp hu'sum
  refine ⟨he, hHeight, ?_⟩
  intro v hv
  exact ⟨hlzero v hv, hu'zero v hv, by linarith [hbase v hv, hlzero v hv, hu'zero v hv]⟩

end BC4lean.OrderedPrismWeights
