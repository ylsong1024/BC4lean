import BC4lean.ProbabilitySimplex
import BC4lean.ProperActions

/-! # Properness of the probability-simplex action

Compact sets of probability functions are uniformly concentrated on a finite
set of coordinates. This bounds all compact transporters by a finite set.
-/

noncomputable section
open scoped BigOperators Pointwise Classical

namespace BC4lean.ProperActions.ProbabilitySimplex

variable {Γ : Type*}

/-- On a compact set of probability functions, a single finite set carries more than half the mass. -/
theorem compact_half_mass {K : Set (ProbabilitySimplex Γ)} (hK : IsCompact K) :
    ∃ s : Finset Γ, ∀ p ∈ K, (1 / 2 : ℝ) < ∑ g ∈ s, p.1 g := by
  classical
  let U (s : Finset Γ) : Set (ProbabilitySimplex Γ) := {p | (1 / 2 : ℝ) < ∑ g ∈ s, p.1 g}
  have ho (s : Finset Γ) : IsOpen (U s) :=
    isOpen_lt continuous_const (continuous_finsetSum s fun g _ =>
      (continuous_apply g).comp continuous_subtype_val)
  have hc : K ⊆ ⋃ s, U s := by
    intro p _
    obtain ⟨s, hs⟩ := exists_half_mass p
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U ho hc
  refine ⟨S.biUnion id, fun p hp => ?_⟩
  obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp (hS hp)
  apply lt_of_lt_of_le hps
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun g hg => Finset.mem_biUnion.mpr ⟨s, hs, hg⟩) (fun g _ _ => p.2.1 g)

/-- Two finite sets each carrying more than half the mass must intersect. -/
theorem half_mass_inter (p : ProbabilitySimplex Γ) (s t : Finset Γ)
    (hs : (1 / 2 : ℝ) < ∑ g ∈ s, p.1 g) (ht : (1 / 2 : ℝ) < ∑ g ∈ t, p.1 g) :
    (s ∩ t).Nonempty := by
  classical
  by_contra h
  have hd : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp h)
  have hle := sum_le_one p (s ∪ t)
  rw [Finset.sum_union hd] at hle
  linarith

variable [Group Γ]

/-- Translation preserves the mass assigned to a finite set. -/
theorem sum_translate_image (g : Γ) (p : ProbabilitySimplex Γ) (s : Finset Γ) :
    ∑ x ∈ s.image (fun y => g * y), (g • p).1 x = ∑ y ∈ s, p.1 y := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel h)]
  simp

/-- Compact subsets have finite transporters under left translation. -/
theorem finite_compact_transporter {K L : Set (ProbabilitySimplex Γ)}
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : Γ | (g • K ∩ L).Nonempty}.Finite := by
  classical
  obtain ⟨s, hs⟩ := compact_half_mass hK
  obtain ⟨t, ht⟩ := compact_half_mass hL
  apply ((t.product s).image (fun p => p.1 * p.2⁻¹)).finite_toSet.subset
  intro g hg
  obtain ⟨q, hq, hqL⟩ := hg
  obtain ⟨p, hp, rfl⟩ := hq
  have himage : (1 / 2 : ℝ) < ∑ x ∈ s.image (fun y => g * y), (g • p).1 x := by
    rw [sum_translate_image]
    exact hs p hp
  obtain ⟨x, hx⟩ := half_mass_inter (g • p) (s.image (fun y => g * y)) t himage (ht _ hqL)
  obtain ⟨hx, hxt⟩ := Finset.mem_inter.mp hx
  obtain ⟨y, hys, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨(g * y,y), Finset.mem_product.mpr ⟨hxt,hys⟩, by simp⟩

/-- The simplex action is properly discontinuous. -/
theorem properlyDiscontinuous : ProperlyDiscontinuousSMul Γ (ProbabilitySimplex Γ) :=
  properlyDiscontinuousSMul_iff.mpr (fun hK hL => finite_compact_transporter hK hL)

/-- For countable discrete groups the probability simplex is a proper Γ-space. -/
theorem proper [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] :
    ProperSMul Γ (ProbabilitySimplex Γ) :=
  properlyDiscontinuousSMul_iff_properSMul.mp properlyDiscontinuous

end BC4lean.ProperActions.ProbabilitySimplex
