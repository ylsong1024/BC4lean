import BC4lean.LabeledOrbitRealization
import Mathlib.Topology.UnitInterval

/-! # Explicit inverse coefficients for staircase prisms

This module gives the actual finite min/max formulas in each cylinder chart.
Normalization and allowed-support geometry are separate from coordinate continuity.
-/
noncomputable section
open scoped BigOperators
namespace BC4lean.ProperActions.LabeledPrismInverse
open LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

def higherMass (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s)
    (v : LabeledOrbitVertex Γ) : ℝ :=
  ∑ u ∈ s.vertices.filter (fun u => v.1 < u.1), w.val u

def upperWeight (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s)
    (t : ℝ) (v : LabeledOrbitVertex Γ) : ℝ :=
  min (w.val v) (max 0 (t - higherMass s w v))

def lowerWeight (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s)
    (t : ℝ) (v : LabeledOrbitVertex Γ) : ℝ := w.val v - upperWeight s w t v

theorem upperWeight_nonneg (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s)
    (t : ℝ) (v : LabeledOrbitVertex Γ) : 0 ≤ upperWeight s w t v :=
  le_min (w.property.1 v) (le_max_left _ _)

theorem lowerWeight_nonneg (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s)
    (t : ℝ) (v : LabeledOrbitVertex Γ) : 0 ≤ lowerWeight s w t v :=
  sub_nonneg.mpr (min_le_left _ _)

theorem recombine (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s)
    (t : ℝ) (v : LabeledOrbitVertex Γ) : lowerWeight s w t v + upperWeight s w t v = w.val v :=
  sub_add_cancel _ _

theorem upperWeight_eq_zero_of_not_mem (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (v : LabeledOrbitVertex Γ)
    (hv : v ∉ s.vertices) : upperWeight s w t v = 0 := by
  unfold upperWeight
  rw [w.property.2.1 v hv]
  exact min_eq_left (le_max_left _ _)

theorem lowerWeight_eq_zero_of_not_mem (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : ℝ) (v : LabeledOrbitVertex Γ)
    (hv : v ∉ s.vertices) : lowerWeight s w t v = 0 := by
  unfold lowerWeight
  rw [w.property.2.1 v hv, upperWeight_eq_zero_of_not_mem s w t v hv, sub_self]

theorem continuous_higherMass (s : LabeledOrbitSimplex Γ) (v : LabeledOrbitVertex Γ) :
    Continuous (fun w : LabeledSimplexCoordinates Γ s => higherMass s w v) := by
  classical
  apply continuous_finsetSum
  intro u _
  exact (continuous_apply u).comp continuous_subtype_val

theorem continuous_upperWeight (s : LabeledOrbitSimplex Γ) (v : LabeledOrbitVertex Γ) :
    Continuous (fun p : LabeledSimplexCoordinates Γ s × ℝ => upperWeight s p.1 p.2 v) := by
  have hw : Continuous (fun p : LabeledSimplexCoordinates Γ s × ℝ => p.1.val v) :=
    (continuous_apply v).comp (continuous_subtype_val.comp continuous_fst)
  have hh : Continuous (fun p : LabeledSimplexCoordinates Γ s × ℝ => higherMass s p.1 v) :=
    (continuous_higherMass s v).comp continuous_fst
  exact hw.min (continuous_const.max (continuous_snd.sub hh))

theorem continuous_lowerWeight (s : LabeledOrbitSimplex Γ) (v : LabeledOrbitVertex Γ) :
    Continuous (fun p : LabeledSimplexCoordinates Γ s × ℝ => lowerWeight s p.1 p.2 v) := by
  have hw : Continuous (fun p : LabeledSimplexCoordinates Γ s × ℝ => p.1.val v) :=
    (continuous_apply v).comp (continuous_subtype_val.comp continuous_fst)
  exact hw.sub (continuous_upperWeight s v)

end BC4lean.ProperActions.LabeledPrismInverse
