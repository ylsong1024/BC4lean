import BC4lean.FiniteJoinShift
import BC4lean.LabeledOrbitRealizationAction

/-! # Global descending-label homotopy

Finite truncations stabilize exactly on each finite simplex. The resulting
global map is continuous in the weak topology, with no pointwise choice of a
fresh vertex used as a continuity argument.
-/
noncomputable section
open scoped unitInterval
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

theorem finiteShiftHomotopy_large_chart_eq (n m : ℕ) (hnm : n ≤ m)
    (s : LabeledOrbitSimplex Γ) (hs : ∀ v ∈ s.vertices, v.1 < n+1)
    (w : LabeledSimplexCoordinates Γ s) (t : I) :
    finiteShiftHomotopy m (chart s w, t) = finiteShiftHomotopy n (chart s w, t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ]
    exact (finiteShiftHomotopy_succ_chart_eq (n+k) s
      (fun v hv => lt_of_lt_of_le (hs v hv) (by omega)) w t).trans (ih (by omega))

/-- Choose any sufficiently large finite truncation. Its value is independent
of the chosen bound by exact chart stabilization. -/
def globalShift (p : LabeledOrbitRealization Γ × I) : LabeledOrbitRealization Γ :=
  finiteShiftHomotopy (supportSimplex p.1).freshLabel p

theorem globalShift_chart_eq (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (t : I) :
    globalShift (chart s w, t) = finiteShiftHomotopy s.freshLabel (chart s w, t) := by
  let x := chart s w
  let r := supportSimplex x
  let z : LabeledSimplexCoordinates Γ r := ⟨x.val, mem_coordinates_supportSimplex x⟩
  have hz : chart r z = x := rfl
  have h₁ := finiteShiftHomotopy_large_chart_eq r.freshLabel
    (max r.freshLabel s.freshLabel) (le_max_left _ _) r
    (fun v hv => Nat.lt_trans (r.label_lt_freshLabel hv) (Nat.lt_succ_self _)) z t
  have h₂ := finiteShiftHomotopy_large_chart_eq s.freshLabel
    (max r.freshLabel s.freshLabel) (le_max_right _ _) s
    (fun v hv => Nat.lt_trans (s.label_lt_freshLabel hv) (Nat.lt_succ_self _)) w t
  rw [hz] at h₁
  exact h₁.symm.trans h₂

theorem continuous_globalShift : Continuous (globalShift (Γ := Γ)) := by
  apply (continuous_product_iff _).mpr
  intro s
  have hc := (continuous_finiteShiftHomotopy (Γ := Γ) s.freshLabel).comp
    ((continuous_chart s).prodMap continuous_id)
  convert hc using 1
  funext p
  exact globalShift_chart_eq s p.1 p.2

@[simp] theorem globalShift_zero (x : LabeledOrbitRealization Γ) :
    globalShift (x, 0) = x := by
  unfold globalShift
  rw [finiteShiftHomotopy_zero]
  let s := supportSimplex x
  let w : LabeledSimplexCoordinates Γ s := ⟨x.val, mem_coordinates_supportSimplex x⟩
  exact partialShift_chart_eq (s.freshLabel+1) s
    (fun v hv => Nat.lt_trans (s.label_lt_freshLabel hv) (Nat.lt_succ_self _)) w

@[simp] theorem globalShift_one (x : LabeledOrbitRealization Γ) :
    globalShift (x, 1) = partialShift 0 x := finiteShiftHomotopy_one _ x

end BC4lean.ProperActions.LabeledOrbitRealization
