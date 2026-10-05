import BC4lean.ControlledTelescopeHomotopy
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Tactic.Positivity

/-! # Continuous height bounds from local stage control
Bump functions attain one locally, so their locally finite weighted sum
majorizes a usable stage bound at every point.
-/
noncomputable section
open scoped BigOperators unitInterval
open Set Topology
namespace BC4lean.ClosedStageTelescope
variable {X : Type*} [TopologicalSpace X]
variable (E : ℕ → Set X) (hm : Monotone E)

include hm in
/-- Local stage bounds can be replaced by one continuous real height bound. -/
theorem exists_height_bound {ι : Type*} [NormalSpace (Telescope E)]
    [ParacompactSpace (Telescope E)] (n₀ : ℕ)
    (C : I × Telescope E → X) (U : ι → Set (Telescope E))
    (ho : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)
    (N : ι → ℕ) (hcontrol : ∀ i p, p ∈ U i → ∀ t, C (t,p) ∈ E (N i)) :
    ∃ q : C(Telescope E, ℝ), (∀ p, p.val.2 ≤ q p) ∧
      (∀ p, (n₀ : ℝ) ≤ q p) ∧ (∀ t p, C (t,p) ∈ E ⌊q p⌋₊) := by
  classical
  obtain ⟨b, hb⟩ := BumpCovering.exists_isSubordinate isClosed_univ U ho
    (by rw [hcover])
  let S (p : Telescope E) : ℝ := ∑ᶠ i, b i p * ((N i : ℝ) + 1)
  have hcS : Continuous S :=
    (continuous_finsum (fun i => (b i).continuous.mul continuous_const))
      (b.locallyFinite.subset (fun i => Function.support_mul_subset_left _ _))
  have hS0 (p : Telescope E) : 0 ≤ S p :=
    finsum_nonneg (fun i => mul_nonneg (b.nonneg i p)
      (by positivity))
  let q : C(Telescope E, ℝ) :=
    ⟨fun p => p.val.2 + (n₀ : ℝ) + S p,
      ((continuous_snd.comp continuous_subtype_val).add continuous_const).add hcS⟩
  have hp0 (p : Telescope E) : 0 ≤ p.val.2 := by
    obtain ⟨n, _, ht⟩ := p.property
    exact (Nat.cast_nonneg n).trans ht.1
  refine ⟨q, ?_, ?_, ?_⟩
  · intro p
    change p.val.2 ≤ p.val.2 + (n₀ : ℝ) + S p
    exact le_add_of_nonneg_right (Nat.cast_nonneg n₀) |>.trans
      (le_add_of_nonneg_right (hS0 p))
  · intro p
    change (n₀ : ℝ) ≤ p.val.2 + (n₀ : ℝ) + S p
    linarith [hp0 p, hS0 p]
  · intro t p
    let i := b.ind p (mem_univ p)
    have hi : b i p = 1 := b.ind_apply p (mem_univ p)
    have hpi : p ∈ U i := hb i (by
      change p ∈ closure (Function.support (b i))
      exact subset_closure (by simp [Function.mem_support, hi]))
    have hfin : (Function.support (fun j => b j p * ((N j : ℝ)+1))).Finite :=
      (b.point_finite p).subset (fun j hj =>
        (mul_ne_zero_iff.mp hj).1)
    have hle : (N i : ℝ)+1 ≤ S p := by
      dsimp only [S]
      rw [finsum_eq_sum_of_support_subset _ hfin.coe_toFinset.ge]
      have him : i ∈ hfin.toFinset := by
        simp only [Set.Finite.mem_toFinset, Function.mem_support]
        rw [hi, one_mul]
        positivity
      have hs : b i p * ((N i : ℝ)+1) ≤
          ∑ j ∈ hfin.toFinset, b j p * ((N j : ℝ)+1) :=
        Finset.single_le_sum (fun j _ =>
        mul_nonneg (b.nonneg j p) (add_nonneg (Nat.cast_nonneg (N j)) zero_le_one)) him
      simpa [hi] using hs
    apply hm (Nat.le_floor (show (N i : ℝ) ≤ q p from by
      change (N i : ℝ) ≤ p.val.2 + (n₀ : ℝ) + S p
      linarith [hp0 p, Nat.cast_nonneg (α := ℝ) n₀]))
    exact hcontrol i p hpi t

include hm in
/-- Compact local control supplies the open cover needed for a height bound. -/
theorem exists_height_bound_of_compact_control
    [LocallyCompactSpace (Telescope E)] [NormalSpace (Telescope E)]
    [ParacompactSpace (Telescope E)] (n₀ : ℕ) (C : I × Telescope E → X)
    (hcompact : ∀ K : Set (Telescope E), IsCompact K →
      ∃ N, ∀ t p, p ∈ K → C (t,p) ∈ E N) :
    ∃ q : C(Telescope E, ℝ), (∀ p, p.val.2 ≤ q p) ∧
      (∀ p, (n₀ : ℝ) ≤ q p) ∧ (∀ t p, C (t,p) ∈ E ⌊q p⌋₊) := by
  classical
  choose K hKc hKn using (fun p : Telescope E => exists_compact_mem_nhds p)
  choose N hN using (fun p : Telescope E => hcompact (K p) (hKc p))
  apply exists_height_bound E hm n₀ C (fun p => interior (K p))
    (fun _ => isOpen_interior) _ N
    (fun p y hy t => hN p t y (interior_subset hy))
  apply eq_univ_of_forall
  intro p
  exact mem_iUnion.mpr ⟨p, mem_interior_iff_mem_nhds.mpr (hKn p)⟩

end BC4lean.ClosedStageTelescope
