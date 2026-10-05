import BC4lean.LabeledPrismInverseChart
import BC4lean.LabeledPrismProjection
import BC4lean.OrderedPrismUniqueness

/-! # The actual staircase inverse on each finite cylinder chart -/
noncomputable section
open scoped BigOperators
namespace BC4lean.ProperActions.LabeledPrismInverse
open LabeledOrbitRealization LabeledTelescopePrisms
variable {Γ : Type*} [Group Γ]

theorem sum_upperWeight (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s)
    (t : unitInterval) : ∑ v ∈ s.vertices, upperWeight s w t v = (t : ℝ) := by
  have hb : (t : ℝ) ≤ ∑ v ∈ s.vertices, w.val v := by
    rw [w.property.2.2]
    exact t.property.2
  exact BC4lean.OrderedPrismWeights.sum_min_max_higher_of_le s.vertices Prod.fst
    s.labels_injective w.val (fun v _ => w.property.1 v) t t.property.1 hb

variable [Countable Γ]

theorem inverseBoxChart_allowed (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s ∈ LabeledOrbitSimplex.exhaustion n)
    (w : LabeledSimplexCoordinates Γ s) (t : unitInterval) :
    supportSimplex (chart (boxSimplex n s) (inverseBoxChart n s (w, (t : ℝ)))) ∈
      LabeledTelescopePrisms.allowed := by
  classical
  obtain ⟨k, hupper, hlower⟩ := BC4lean.OrderedPrismWeights.exists_min_max_staircase_cut
    s.vertices Prod.fst w.val (fun v _ => w.property.1 v) (t : ℝ)
  refine ⟨n, k, s, hs, ?_⟩
  intro v hv
  have hne := (mem_supportSimplex _ v).mp hv
  change taggedWeights n s w t v ≠ 0 at hne
  have hb : v ∈ (boxSimplex n s).vertices := by
    by_contra hb
    exact hne (taggedWeights_eq_zero_of_not_mem n s w t v hb)
  change v ∈ boxVertices n s at hb
  rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    rw [taggedWeights_lower n s w t u hu] at hne
    have huk : u.1 ≤ k := by
      by_contra hn
      exact hne (hlower u hu (lt_of_not_ge hn))
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, huk⟩, rfl⟩)
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    rw [taggedWeights_upper n s w t u hu] at hne
    have hku : k ≤ u.1 := by
      by_contra hn
      exact hne (hupper u hu (lt_of_not_ge hn))
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hku⟩, rfl⟩)

/-- The inverse on one finite old chart times its geometric unit cylinder. -/
def inverseCylinderChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s ∈ LabeledOrbitSimplex.exhaustion n)
    (p : LabeledSimplexCoordinates Γ s × unitInterval) :
    LabeledPrismProjection.PrismRealization (Γ := Γ) :=
  ⟨chart (boxSimplex n s) (inverseBoxChart n s (p.1, (p.2 : ℝ))),
    inverseBoxChart_allowed n s hs p.1 p.2⟩

theorem continuous_inverseCylinderChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s ∈ LabeledOrbitSimplex.exhaustion n) :
    Continuous (inverseCylinderChart n s hs) := by
  have hc : Continuous (fun p : LabeledSimplexCoordinates Γ s × unitInterval =>
      (p.1, (p.2 : ℝ))) := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_chart _).comp ((continuous_inverseBoxChart n s).comp hc)).subtype_mk _

end BC4lean.ProperActions.LabeledPrismInverse
