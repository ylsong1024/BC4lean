import BC4lean.LabeledShiftInterpolation
import BC4lean.JoinShiftTime

noncomputable section
open scoped Classical unitInterval
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- A shift stage extended constantly before and after its own fixed time interval. -/
def timedConsecutiveShift (k : ℕ) (p : LabeledOrbitRealization Γ × I) :
    LabeledOrbitRealization Γ := consecutiveShift k (p.1, joinShiftParameter k p.2)

theorem continuous_timedConsecutiveShift (k : ℕ) :
    Continuous (timedConsecutiveShift (Γ := Γ) k) :=
  (continuous_consecutiveShift k).comp
    (continuous_fst.prodMk ((continuous_joinShiftParameter k).comp
      (continuous_subtype_val.comp continuous_snd)))

/-- Finite descending shift with absolute stage times, independent of its truncation. -/
def finiteShiftHomotopy : ℕ → LabeledOrbitRealization Γ × I → LabeledOrbitRealization Γ
  | 0 => timedConsecutiveShift 0
  | n+1 => fun p => if (p.2 : ℝ) ≤ 1 / ((n : ℝ) + 2)
      then timedConsecutiveShift (n+1) p else finiteShiftHomotopy n p

/-- A finite truncation is constant before its highest stage starts. -/
theorem finiteShiftHomotopy_initial (n : ℕ) (p : LabeledOrbitRealization Γ × I)
    (ht : (p.2 : ℝ) ≤ 1 / ((n : ℝ) + 2)) :
    finiteShiftHomotopy n p = partialShift (n+1) p.1 := by
  induction n with
  | zero =>
    simp only [finiteShiftHomotopy, timedConsecutiveShift,
      joinShiftParameter_zero_of_le 0 (by simpa using ht), consecutiveShift_zero]
  | succ n _ =>
    have hcut : (p.2 : ℝ) ≤ 1 / ((n : ℝ) + 2) := ht.trans
      (one_div_le_one_div_of_le (by positivity) (by simp only [Nat.cast_add, Nat.cast_one]; linarith))
    simp only [finiteShiftHomotopy, if_pos hcut, timedConsecutiveShift]
    rw [joinShiftParameter_zero_of_le (n+1) ht, consecutiveShift_zero]

theorem continuous_finiteShiftHomotopy (n : ℕ) :
    Continuous (finiteShiftHomotopy (Γ := Γ) n) := by
  induction n with
  | zero => exact continuous_timedConsecutiveShift 0
  | succ n ih =>
    apply (continuous_timedConsecutiveShift (n+1)).if_le ih
      (continuous_subtype_val.comp continuous_snd) continuous_const
    intro p hp
    change (p.2 : ℝ) = 1 / ((n : ℝ) + 2) at hp
    rw [finiteShiftHomotopy_initial n p hp.le]
    unfold timedConsecutiveShift
    rw [joinShiftParameter_one_of_ge (n+1) (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hp.ge), consecutiveShift_one]

@[simp] theorem finiteShiftHomotopy_zero (n : ℕ) (x : LabeledOrbitRealization Γ) :
    finiteShiftHomotopy n (x, 0) = partialShift (n+1) x :=
  finiteShiftHomotopy_initial n _ (by positivity)

@[simp] theorem finiteShiftHomotopy_one (n : ℕ) (x : LabeledOrbitRealization Γ) :
    finiteShiftHomotopy n (x, 1) = partialShift 0 x := by
  induction n with
  | zero =>
    simp only [finiteShiftHomotopy, timedConsecutiveShift]
    rw [joinShiftParameter_one_of_ge 0 (by norm_num), consecutiveShift_one]
  | succ n ih =>
    have hcut : ¬ (1 : ℝ) ≤ 1 / ((n : ℝ) + 2) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [le_div_iff₀ (by linarith)]
      linarith
    change (if (1 : ℝ) ≤ 1 / ((n : ℝ) + 2) then
      timedConsecutiveShift (n+1) (x, 1) else finiteShiftHomotopy n (x, 1)) = _
    rw [if_neg hcut]
    exact ih

/-- Adding a stage above all labels does not alter any time on the finite chart. -/
theorem finiteShiftHomotopy_succ_chart_eq (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : ∀ v ∈ s.vertices, v.1 < n+1) (w : LabeledSimplexCoordinates Γ s) (t : I) :
    finiteShiftHomotopy (n+1) (chart s w, t) = finiteShiftHomotopy n (chart s w, t) := by
  change (if (t : ℝ) ≤ 1 / ((n : ℝ) + 2) then
    timedConsecutiveShift (n+1) (chart s w, t) else
    finiteShiftHomotopy n (chart s w, t)) = _
  split_ifs with ht
  · rw [finiteShiftHomotopy_initial n _ ht, partialShift_chart_eq (n+1) s hs w]
    exact consecutiveShift_chart_eq (n+1) s hs w (joinShiftParameter (n+1) t)
  · rfl

end BC4lean.ProperActions.LabeledOrbitRealization
