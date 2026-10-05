import BC4lean.LabeledPrismInverse

/-! # Projection recovers every finite geometric cylinder chart -/
noncomputable section
open scoped BigOperators Classical
namespace BC4lean.ProperActions.LabeledPrismInverse
open LabeledOrbitRealization LabeledTelescopePrisms LabeledPrismProjection
variable {Γ : Type*} [Group Γ]

/-- Finite tagged masses integrate vertex functions by their two endpoint values. -/
theorem taggedWeights_integral (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (f : LabeledOrbitVertex Γ → ℝ) :
    (∑ v ∈ (boxSimplex n s).vertices, taggedWeights n s w t v * f v) =
      ∑ u ∈ s.vertices,
        (lowerWeight s w t u * f (vertex n u) +
          upperWeight s w t u * f (vertex (n + 1) u)) := by
  unfold taggedWeights
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  have hl : vertex n u ∈ (boxSimplex n s).vertices :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  have hh : vertex (n + 1) u ∈ (boxSimplex n s).vertices :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  simp_rw [add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', if_pos hl, if_pos hh]

/-- Adding lower and upper coordinates recovers the original barycentric point. -/
theorem baseCoordinates_inverseBoxChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (u : LabeledOrbitVertex Γ) :
    baseCoordinates (chart (boxSimplex n s) (inverseBoxChart n s (w, t))) u = w.val u := by
  rw [baseCoordinates, weightedSum_eq_chart]
  change (∑ v ∈ (boxSimplex n s).vertices, taggedWeights n s w t v *
    (if forgetVertex v = u then 1 else 0)) = _
  rw [taggedWeights_integral]
  simp only [forget_vertex]
  simp_rw [← add_mul, recombine, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hu
  · rfl
  · exact (w.property.2.1 u hu).symm

/-- The height average of inverse coordinates is exactly the original height. -/
theorem height_inverseBoxChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : unitInterval) :
    height (chart (boxSimplex n s) (inverseBoxChart n s (w, (t : ℝ)))) =
      (n : ℝ) + (t : ℝ) := by
  rw [height, weightedSum_eq_chart]
  change (∑ v ∈ (boxSimplex n s).vertices, taggedWeights n s w t v *
    (heightVertex v : ℝ)) = _
  rw [taggedWeights_integral]
  simp only [height_vertex, Nat.cast_add, Nat.cast_one]
  have he (u : LabeledOrbitVertex Γ) :
      lowerWeight s w t u * (n : ℝ) + upperWeight s w t u * ((n : ℝ) + 1) =
        w.val u * n + upperWeight s w t u := by
    calc
      _ = (lowerWeight s w t u + upperWeight s w t u) * n + upperWeight s w t u := by ring
      _ = _ := by rw [recombine]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, w.property.2.2, sum_upperWeight]
  simp

variable [Countable Γ]

/-- The forward geometric projection is a left inverse on every finite cylinder chart. -/
theorem projection_inverseCylinderChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s ∈ LabeledOrbitSimplex.exhaustion n)
    (p : LabeledSimplexCoordinates Γ s × unitInterval) :
    (projection (inverseCylinderChart n s hs p)).val =
      (chart s p.1, (n : ℝ) + (p.2 : ℝ)) := by
  apply Prod.ext
  · apply Subtype.ext
    funext u
    exact baseCoordinates_inverseBoxChart n s p.1 p.2 u
  · exact height_inverseBoxChart n s p.1 p.2


/-- Every point of the actual geometric telescope has prism coordinates. -/
theorem projection_surjective : Function.Surjective (projection (Γ := Γ)) := by
  intro p
  obtain ⟨n, hn, ht⟩ := p.property
  let s := supportSimplex p.val.1
  let w : LabeledSimplexCoordinates Γ s :=
    ⟨p.val.1.val, mem_coordinates_supportSimplex p.val.1⟩
  let t : unitInterval := ⟨p.val.2 - (n : ℝ), by constructor <;> linarith [ht.1, ht.2]⟩
  have hs : s ∈ LabeledOrbitSimplex.exhaustion n := hn
  refine ⟨inverseCylinderChart n s hs (w, t), Subtype.ext ?_⟩
  rw [projection_inverseCylinderChart n s hs (w, t)]
  apply Prod.ext
  · rfl
  · change (n : ℝ) + (p.val.2 - (n : ℝ)) = p.val.2
    ring

end BC4lean.ProperActions.LabeledPrismInverse

