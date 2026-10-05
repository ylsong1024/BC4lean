import BC4lean.LabeledOrbitCW
import BC4lean.JoinFixedContraction
import BC4lean.CellularHomotopy

/-! # The cellular mapping property of the concrete weak join -/
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {A : Type u} [TopologicalSpace A] [MulAction Γ A] [ContinuousConstSMul Γ A]

/-- Every finite-isotropy equivariant CW source maps to the concrete join,
with all such maps equivariantly homotopic. -/
theorem EquivariantCWComplex.labeledJoin_homotopyTerminal
    (c : EquivariantCWComplex (topologicalAction Γ A)) :
    HomotopyTerminalFor Γ A (LabeledOrbitRealization Γ) :=
  c.homotopyTerminal LabeledOrbitRealization.fixedPointCriterion

/-- Properness and the cellular mapping property hold for every discrete group. -/
theorem labeledJoin_proper_universal_target
    (c : EquivariantCWComplex (topologicalAction Γ A)) :
    ProperSMul Γ (LabeledOrbitRealization Γ) ∧
      HomotopyTerminalFor Γ A (LabeledOrbitRealization Γ) :=
  ⟨LabeledOrbitRealization.proper, c.labeledJoin_homotopyTerminal⟩

/-- The explicitly realized join carries actual finite-isotropy CW data,
is proper, and has precisely the required subgroup fixed-point spaces. -/
theorem labeledJoin_universal_proper_CW_model :
    Nonempty (EquivariantCWComplex (topologicalAction Γ (LabeledOrbitRealization Γ))) ∧
      ProperSMul Γ (LabeledOrbitRealization Γ) ∧
      FixedPointCriterion Γ (LabeledOrbitRealization Γ) :=
  ⟨⟨LabeledOrbitRealization.equivariantCWComplex⟩,
    LabeledOrbitRealization.proper,LabeledOrbitRealization.fixedPointCriterion⟩

/-- Every genuine equivariant CW model with the same fixed-point criterion
is equivariantly homotopy equivalent to the explicitly constructed join. -/
theorem EquivariantCWComplex.labeledJoin_unique
    (c : EquivariantCWComplex (topologicalAction Γ A))
    (h : FixedPointCriterion Γ A) :
    Nonempty (EquivariantHomotopyEquiv Γ A (LabeledOrbitRealization Γ)) :=
  c.fixedPointCriterion_unique LabeledOrbitRealization.equivariantCWComplex h
    LabeledOrbitRealization.fixedPointCriterion
end BC4lean.ProperActions
