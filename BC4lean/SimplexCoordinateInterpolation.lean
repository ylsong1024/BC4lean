import BC4lean.LabeledOrbitRealization
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Ring

/-! # Coordinate inclusions and interpolation in a common finite simplex chart -/
noncomputable section
open scoped Classical unitInterval

namespace BC4lean.ProperActions.LabeledOrbitSimplex
variable {Γ : Type*} [Group Γ]

/-- Inclusion of a face chart in any containing finite simplex chart. -/
def coordinateInclusion (s t : LabeledOrbitSimplex Γ) (h : s.vertices ⊆ t.vertices)
    (w : LabeledSimplexCoordinates Γ s) : LabeledSimplexCoordinates Γ t := by
  refine ⟨w.val, w.property.1, ?_, ?_⟩
  · intro v hv
    exact w.property.2.1 v (fun hs => hv (h hs))
  · rw [← Finset.sum_subset h (fun v _ hv => w.property.2.1 v hv)]
    exact w.property.2.2

@[simp] theorem coordinateInclusion_val (s t : LabeledOrbitSimplex Γ)
    (h : s.vertices ⊆ t.vertices) (w : LabeledSimplexCoordinates Γ s) :
    (s.coordinateInclusion t h w).val = w.val := rfl

theorem continuous_coordinateInclusion (s t : LabeledOrbitSimplex Γ)
    (h : s.vertices ⊆ t.vertices) : Continuous (s.coordinateInclusion t h) :=
  continuous_subtype_val.subtype_mk _

@[simp] theorem chart_coordinateInclusion (s t : LabeledOrbitSimplex Γ)
    (h : s.vertices ⊆ t.vertices) (w : LabeledSimplexCoordinates Γ s) :
    LabeledOrbitRealization.chart t (s.coordinateInclusion t h w) =
      LabeledOrbitRealization.chart s w := rfl

/-- Convex interpolation of two vectors in a single finite simplex chart. -/
def coordinateInterpolationWeights (s : LabeledOrbitSimplex Γ)
    (p : I × (LabeledSimplexCoordinates Γ s × LabeledSimplexCoordinates Γ s))
    (v : LabeledOrbitVertex Γ) : ℝ :=
  (1 - (p.1 : ℝ)) * p.2.1.val v + (p.1 : ℝ) * p.2.2.val v

theorem coordinateInterpolationWeights_mem (s : LabeledOrbitSimplex Γ)
    (p : I × (LabeledSimplexCoordinates Γ s × LabeledSimplexCoordinates Γ s)) :
    coordinateInterpolationWeights s p ∈ LabeledSimplexCoordinates Γ s := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.1.property.2) (p.2.1.property.1 v))
      (mul_nonneg p.1.property.1 (p.2.2.property.1 v))
  · intro v hv
    simp only [coordinateInterpolationWeights, p.2.1.property.2.1 v hv,
      p.2.2.property.2.1 v hv, mul_zero, add_zero]
  · change (∑ v ∈ s.vertices,
      ((1 - (p.1 : ℝ)) * p.2.1.val v + (p.1 : ℝ) * p.2.2.val v)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      p.2.1.property.2.2, p.2.2.property.2.2]
    ring

/-- Continuous interpolation into the common chart. -/
def coordinateInterpolation (s : LabeledOrbitSimplex Γ) :
    I × (LabeledSimplexCoordinates Γ s × LabeledSimplexCoordinates Γ s) →
      LabeledSimplexCoordinates Γ s :=
  fun p => ⟨coordinateInterpolationWeights s p, s.coordinateInterpolationWeights_mem p⟩

theorem continuous_coordinateInterpolation (s : LabeledOrbitSimplex Γ) :
    Continuous s.coordinateInterpolation := by
  have ht : Continuous (fun p : I ×
      (LabeledSimplexCoordinates Γ s × LabeledSimplexCoordinates Γ s) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hw₀ (v : LabeledOrbitVertex Γ) : Continuous (fun p : I ×
      (LabeledSimplexCoordinates Γ s × LabeledSimplexCoordinates Γ s) => p.2.1.val v) :=
    (continuous_apply v).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hw₁ (v : LabeledOrbitVertex Γ) : Continuous (fun p : I ×
      (LabeledSimplexCoordinates Γ s × LabeledSimplexCoordinates Γ s) => p.2.2.val v) :=
    (continuous_apply v).comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact ((continuous_const.sub ht).mul (hw₀ v)).add (ht.mul (hw₁ v))

@[simp] theorem coordinateInterpolation_zero (s : LabeledOrbitSimplex Γ)
    (w₀ w₁ : LabeledSimplexCoordinates Γ s) : s.coordinateInterpolation (0, (w₀, w₁)) = w₀ := by
  apply Subtype.ext
  funext v
  simp [coordinateInterpolation, coordinateInterpolationWeights]

@[simp] theorem coordinateInterpolation_one (s : LabeledOrbitSimplex Γ)
    (w₀ w₁ : LabeledSimplexCoordinates Γ s) : s.coordinateInterpolation (1, (w₀, w₁)) = w₁ := by
  apply Subtype.ext
  funext v
  simp [coordinateInterpolation, coordinateInterpolationWeights]

end BC4lean.ProperActions.LabeledOrbitSimplex
