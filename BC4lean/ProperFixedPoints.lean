import BC4lean.ProperActions

/-! # Subgroup fixed points of proper discrete-group actions

The empty-fixed-point condition for infinite subgroups follows from properness.
Contractibility of fixed points for finite subgroups is additional data, not a
consequence of properness.
-/
namespace BC4lean.ProperActions

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

/-- The fixed-point space carries the subspace topology when `X` is topological. -/
abbrev FixedPointSpace (H : Subgroup Γ) (X : Type*) [MulAction Γ X] :=
  ↥(MulAction.fixedPoints H X)

/-- A point is fixed by a subgroup exactly when that subgroup lies in its stabilizer. -/
theorem mem_fixedPoints_iff_le_stabilizer (H : Subgroup Γ) (x : X) :
    x ∈ MulAction.fixedPoints H X ↔ H ≤ MulAction.stabilizer Γ x := by
  constructor
  · intro hx g hg
    exact hx ⟨g, hg⟩
  · intro hx g
    exact hx g.property

/-- Passing to a smaller subgroup enlarges the fixed-point set. -/
theorem fixedPoints_antitone {H K : Subgroup Γ} (hHK : H ≤ K) :
    MulAction.fixedPoints K X ⊆ MulAction.fixedPoints H X := by
  intro x hx
  exact (mem_fixedPoints_iff_le_stabilizer H x).mpr
    (hHK.trans ((mem_fixedPoints_iff_le_stabilizer K x).mp hx))

/-- Every point is fixed by the trivial subgroup. -/
theorem fixedPoints_bot : MulAction.fixedPoints (⊥ : Subgroup Γ) X = Set.univ := by
  ext x
  simp

section Topology
variable [TopologicalSpace X] [ContinuousConstSMul Γ X] [T2Space X]

/-- Fixed-point sets of subgroups are closed in a Hausdorff space. -/
theorem isClosed_fixedPoints (H : Subgroup Γ) : IsClosed (MulAction.fixedPoints H X) := by
  rw [MulAction.fixed_eq_iInter_fixedBy]
  apply isClosed_iInter
  intro h
  exact isClosed_eq (continuous_const_smul (h : Γ)) continuous_id

/-- Subgroup fixed-point spaces of LCH spaces are locally compact. -/
theorem fixedPointSpace_locallyCompact [LocallyCompactSpace X] (H : Subgroup Γ) :
    LocallyCompactSpace (FixedPointSpace H X) :=
  (isClosed_fixedPoints (X := X) H).locallyCompactSpace
end Topology

section Proper
variable [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace X] [ProperSMul Γ X]

/-- A subgroup fixing a point in a proper discrete-group action is finite. -/
theorem finite_subgroup_of_fixedPoint {H : Subgroup Γ} {x : X}
    (hx : x ∈ MulAction.fixedPoints H X) : (H : Set Γ).Finite :=
  (finite_stabilizer (Γ := Γ) x).subset
    ((mem_fixedPoints_iff_le_stabilizer H x).mp hx)

/-- Infinite subgroups have empty fixed-point sets in proper discrete-group actions. -/
theorem fixedPoints_eq_empty_of_infinite (H : Subgroup Γ) [Infinite H] :
    MulAction.fixedPoints H X = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have : Finite H := (finite_subgroup_of_fixedPoint hx).to_subtype
  exact not_finite H

/-- The topological fixed-point space is empty for an infinite subgroup. -/
theorem fixedPointSpace_isEmpty (H : Subgroup Γ) [Infinite H] :
    IsEmpty (FixedPointSpace H X) :=
  Set.isEmpty_coe_sort.mpr (fixedPoints_eq_empty_of_infinite H)
end Proper

end BC4lean.ProperActions
