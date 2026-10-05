import BC4lean.FiniteJoinShift

noncomputable section
open scoped Classical unitInterval
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- Relabeling does not disturb invariant barycentric coordinates. -/
theorem partialShift_invariant (k : ℕ) (x : LabeledOrbitRealization Γ) (g : Γ)
    (hx : ∀ v, x.val (g • v) = x.val v) (v : LabeledOrbitVertex Γ) :
    (partialShift k x).val (g • v) = (partialShift k x).val v :=
  shiftedWeights_invariant k x.val g hx v

/-- Each affine shift stage preserves invariant coordinates. -/
theorem consecutiveShift_invariant (k : ℕ) (p : LabeledOrbitRealization Γ × I) (g : Γ)
    (hx : ∀ v, p.1.val (g • v) = p.1.val v) (v : LabeledOrbitVertex Γ) :
    (consecutiveShift k p).val (g • v) = (consecutiveShift k p).val v := by
  change (1 - (p.2 : ℝ)) * shiftedWeights (k+1) p.1.val (g • v) +
    (p.2 : ℝ) * shiftedWeights k p.1.val (g • v) = _
  rw [shiftedWeights_invariant (k+1) p.1.val g hx v,
    shiftedWeights_invariant k p.1.val g hx v]
  rfl

/-- Every finite shift homotopy preserves subgroup invariant coordinates. -/
theorem finiteShiftHomotopy_invariant (k : ℕ) (p : LabeledOrbitRealization Γ × I) (g : Γ)
    (hx : ∀ v, p.1.val (g • v) = p.1.val v) (v : LabeledOrbitVertex Γ) :
    (finiteShiftHomotopy k p).val (g • v) = (finiteShiftHomotopy k p).val v := by
  induction k with
  | zero => exact consecutiveShift_invariant 0 (p.1, joinShiftParameter 0 p.2) g hx v
  | succ k ih =>
    simp only [finiteShiftHomotopy]
    split_ifs
    · exact consecutiveShift_invariant (k+1) (p.1, joinShiftParameter (k+1) p.2) g hx v
    · exact ih

/-- Once a truncation is above a chart, all later truncations agree on that chart. -/
theorem finiteShiftHomotopy_chart_eq_of_le {m n : ℕ} (hmn : m ≤ n)
    (s : LabeledOrbitSimplex Γ) (hs : ∀ v ∈ s.vertices, v.1 < m+1)
    (w : LabeledSimplexCoordinates Γ s) (t : I) :
    finiteShiftHomotopy n (chart s w, t) = finiteShiftHomotopy m (chart s w, t) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [finiteShiftHomotopy_succ_chart_eq n s (fun v hv =>
      lt_of_lt_of_le (hs v hv) (by omega)) w t]
    exact ih

end BC4lean.ProperActions.LabeledOrbitRealization
