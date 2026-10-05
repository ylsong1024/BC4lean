import BC4lean.LabeledOrbitRealization
import BC4lean.FixedLabeledOrbitSimplices
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Ring

/-! # Affine contraction of a finite fixed simplex into its fixed extension

The map below stays in one larger finite chart. It is not a global contraction
of the realization and supplies no CW attachment witnesses.
-/
noncomputable section
open scoped Classical unitInterval

namespace BC4lean.ProperActions.LabeledOrbitSimplex
variable {Γ : Type*} [Group Γ]

/-- Chart coordinates on a subgroup-fixed simplex are subgroup invariant. -/
theorem fixed_coordinates_invariant (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ)
    (hs : ∀ h : H, (h : Γ) • s = s) (w : LabeledSimplexCoordinates Γ s)
    (h : H) (v : LabeledOrbitVertex Γ) : w.val ((h : Γ) • v) = w.val v := by
  by_cases hv : v ∈ s.vertices
  · rw [(s.smul_eq_iff_vertices h).mp (hs h) v hv]
  · have hgv : (h : Γ) • v ∉ s.vertices := by
      intro hg
      exact hv (((s.stabilizes_iff_smul_eq h).mpr (hs h) v).mpr hg)
    rw [w.property.2.1 v hv, w.property.2.1 _ hgv]

/-- Affine barycentric weights from a chart to its fresh-vertex extension. -/
def fixedAffineWeights (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ)
    (p : I × LabeledSimplexCoordinates Γ s) (v : LabeledOrbitVertex Γ) : ℝ :=
  (1 - (p.1 : ℝ)) * p.2.val v +
    (p.1 : ℝ) * (if v = s.freshFixedVertex H then 1 else 0)

/-- The affine weights have nonnegative coordinates, finite chart support and mass one. -/
theorem fixedAffineWeights_mem (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (p : I × LabeledSimplexCoordinates Γ s) :
    fixedAffineWeights H s p ∈ LabeledSimplexCoordinates Γ (s.fixedExtension H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    apply add_nonneg
    · exact mul_nonneg (sub_nonneg.mpr p.1.property.2) (p.2.property.1 v)
    · apply mul_nonneg p.1.property.1
      split_ifs <;> norm_num
  · intro v hv
    have hnot : v ∉ s.vertices := fun h => hv (s.vertices_subset_fixedExtension H h)
    have hne : v ≠ s.freshFixedVertex H := by
      intro he
      apply hv
      rw [he]
      exact s.freshFixedVertex_mem_fixedExtension H
    simp only [fixedAffineWeights, p.2.property.2.1 v hnot, if_neg hne,
      mul_zero, add_zero]
  · change (∑ v ∈ (s.fixedExtension H).vertices,
      ((1 - (p.1 : ℝ)) * p.2.val v +
        (p.1 : ℝ) * (if v = s.freshFixedVertex H then 1 else 0))) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hw : (∑ v ∈ (s.fixedExtension H).vertices, p.2.val v) = 1 := by
      rw [s.fixedExtension_vertices H, Finset.sum_insert (s.freshFixedVertex_not_mem H)]
      rw [p.2.property.2.1 _ (s.freshFixedVertex_not_mem H), p.2.property.2.2]
      simp
    have hd : (∑ v ∈ (s.fixedExtension H).vertices,
        (if v = s.freshFixedVertex H then (1 : ℝ) else 0)) = 1 := by
      simp
    rw [hw, hd]
    ring

/-- The chart-level affine map to the fresh-vertex extension. -/
def fixedAffineChart (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ) :
    I × LabeledSimplexCoordinates Γ s → LabeledSimplexCoordinates Γ (s.fixedExtension H) :=
  fun p => ⟨fixedAffineWeights H s p, s.fixedAffineWeights_mem H p⟩

theorem continuous_fixedAffineChart (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) : Continuous (s.fixedAffineChart H) := by
  have ht : Continuous (fun p : I × LabeledSimplexCoordinates Γ s => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hw (v : LabeledOrbitVertex Γ) :
      Continuous (fun p : I × LabeledSimplexCoordinates Γ s => p.2.val v) :=
    (continuous_apply v).comp (continuous_subtype_val.comp continuous_snd)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact ((continuous_const.sub ht).mul (hw v)).add (ht.mul continuous_const)

@[simp] theorem fixedAffineChart_zero (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s) :
    (s.fixedAffineChart H (0, w)).val = w.val := by
  funext v
  simp [fixedAffineChart, fixedAffineWeights]

@[simp] theorem fixedAffineChart_one (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s) :
    (s.fixedAffineChart H (1, w)).val =
      (fun v => if v = s.freshFixedVertex H then 1 else 0) := by
  funext v
  simp [fixedAffineChart, fixedAffineWeights]

/-- The canonical terminal coordinate vector, concentrated at the fresh vertex. -/
def freshVertexCoordinates (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ) :
    LabeledSimplexCoordinates Γ (s.fixedExtension H) := by
  refine ⟨(fun v => if v = s.freshFixedVertex H then 1 else 0), ?_, ?_, ?_⟩
  · intro v
    change 0 ≤ (if v = s.freshFixedVertex H then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · intro v hv
    have hne : v ≠ s.freshFixedVertex H := by
      intro he
      apply hv
      rw [he]
      exact s.freshFixedVertex_mem_fixedExtension H
    simp [hne]
  · simp

@[simp] theorem fixedAffineChart_one_eq (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s) :
    s.fixedAffineChart H (1, w) = s.freshVertexCoordinates H := by
  apply Subtype.ext
  exact s.fixedAffineChart_one H w

/-- The starting endpoint agrees with the original simplex in the realization. -/
@[simp] theorem chart_fixedAffineChart_zero (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s) :
    LabeledOrbitRealization.chart (s.fixedExtension H) (s.fixedAffineChart H (0, w)) =
      LabeledOrbitRealization.chart s w := by
  apply Subtype.ext
  exact s.fixedAffineChart_zero H w

/-- Every affine coordinate vector is invariant under the subgroup. -/
theorem fixedAffineChart_invariant (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (hs : ∀ h : H, (h : Γ) • s = s)
    (p : I × LabeledSimplexCoordinates Γ s) (h : H) (v : LabeledOrbitVertex Γ) :
    (s.fixedAffineChart H p).val ((h : Γ) • v) = (s.fixedAffineChart H p).val v :=
  (s.fixedExtension H).fixed_coordinates_invariant H (s.fixedExtension_fixed H hs)
    (s.fixedAffineChart H p) h v

end BC4lean.ProperActions.LabeledOrbitSimplex
