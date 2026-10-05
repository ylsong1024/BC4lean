import BC4lean.LabeledPrismInverseWeights
import BC4lean.LabeledTelescopePrisms
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Continuous cylinder inverse weights in a common finite ambient chart -/
noncomputable section
open scoped BigOperators
namespace BC4lean.ProperActions.LabeledPrismInverse
open LabeledOrbitRealization LabeledTelescopePrisms
variable {Γ : Type*} [Group Γ]

def taggedWeights (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (v : LabeledOrbitVertex Γ) : ℝ := by
  classical
  exact ∑ u ∈ s.vertices,
    ((if v = vertex n u then lowerWeight s w t u else 0) +
      (if v = vertex (n + 1) u then upperWeight s w t u else 0))

theorem taggedWeights_lower (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (u : LabeledOrbitVertex Γ)
    (hu : u ∈ s.vertices) : taggedWeights n s w t (vertex n u) = lowerWeight s w t u := by
  classical
  simp only [taggedWeights, (vertex_injective n).eq_iff, vertex_ne_vertex_succ,
    if_false, add_zero, Finset.sum_ite_eq, if_pos hu]

theorem taggedWeights_upper (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (u : LabeledOrbitVertex Γ)
    (hu : u ∈ s.vertices) : taggedWeights n s w t (vertex (n + 1) u) = upperWeight s w t u := by
  classical
  have hn (v : LabeledOrbitVertex Γ) : vertex (n + 1) u ≠ vertex n v :=
    (vertex_ne_vertex_succ n v u).symm
  simp only [taggedWeights, hn, if_false, zero_add, (vertex_injective (n + 1)).eq_iff,
    Finset.sum_ite_eq, if_pos hu]

theorem taggedWeights_nonneg (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (v : LabeledOrbitVertex Γ) :
    0 ≤ taggedWeights n s w t v := by
  classical
  unfold taggedWeights
  apply Finset.sum_nonneg
  intro u _
  exact add_nonneg (by split <;> first | exact lowerWeight_nonneg s w t u | exact le_rfl)
    (by split <;> first | exact upperWeight_nonneg s w t u | exact le_rfl)

theorem taggedWeights_eq_zero_of_not_mem (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (v : LabeledOrbitVertex Γ)
    (hv : v ∉ (boxSimplex n s).vertices) : taggedWeights n s w t v = 0 := by
  classical
  unfold taggedWeights
  apply Finset.sum_eq_zero
  intro u hu
  have hl : v ≠ vertex n u := by
    intro he
    apply hv
    change v ∈ boxVertices n s
    rw [he]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  have hh : v ≠ vertex (n + 1) u := by
    intro he
    apply hv
    change v ∈ boxVertices n s
    rw [he]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  simp only [if_neg hl, if_neg hh, add_zero]

theorem taggedWeights_mass (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) :
    ∑ v ∈ (boxSimplex n s).vertices, taggedWeights n s w t v = 1 := by
  classical
  unfold taggedWeights
  rw [Finset.sum_comm]
  have he (u : LabeledOrbitVertex Γ) (hu : u ∈ s.vertices) :
      ∑ v ∈ (boxSimplex n s).vertices,
        ((if v = vertex n u then lowerWeight s w t u else 0) +
          (if v = vertex (n + 1) u then upperWeight s w t u else 0)) = w.val u := by
    have hl : vertex n u ∈ (boxSimplex n s).vertices :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    have hh : vertex (n + 1) u ∈ (boxSimplex n s).vertices :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    rw [Finset.sum_add_distrib]
    simpa only [Finset.sum_ite_eq', if_pos hl, if_pos hh] using recombine s w t u
  rw [Finset.sum_congr rfl he]
  exact w.property.2.2

def inverseBoxChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (p : LabeledSimplexCoordinates Γ s × ℝ) : LabeledSimplexCoordinates Γ (boxSimplex n s) :=
  ⟨taggedWeights n s p.1 p.2,
    taggedWeights_nonneg n s p.1 p.2,
    taggedWeights_eq_zero_of_not_mem n s p.1 p.2,
    taggedWeights_mass n s p.1 p.2⟩

theorem continuous_inverseBoxChart (n : ℕ) (s : LabeledOrbitSimplex Γ) :
    Continuous (inverseBoxChart n s) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  unfold taggedWeights
  apply continuous_finsetSum
  intro u _
  have hlow : Continuous (fun p : LabeledSimplexCoordinates Γ s × ℝ =>
      if v = vertex n u then lowerWeight s p.1 p.2 u else 0) := by
    by_cases h : v = vertex n u
    · simpa only [if_pos h] using continuous_lowerWeight s u
    · simp only [if_neg h]
      exact continuous_const
  have hupp : Continuous (fun p : LabeledSimplexCoordinates Γ s × ℝ =>
      if v = vertex (n + 1) u then upperWeight s p.1 p.2 u else 0) := by
    by_cases h : v = vertex (n + 1) u
    · simpa only [if_pos h] using continuous_upperWeight s u
    · simp only [if_neg h]
      exact continuous_const
  exact hlow.add hupp

end BC4lean.ProperActions.LabeledPrismInverse
