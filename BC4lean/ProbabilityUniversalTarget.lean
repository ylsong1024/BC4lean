import BC4lean.ProbabilityFixedPoints
import BC4lean.ProbabilityProperAction
import BC4lean.ProperActionPullback
import BC4lean.CellularHomotopy

/-! # A concrete proper target for the cellular mapping theorem

This module does not equip the probability simplex with a CW structure and
does not assert that it is locally compact. It constructs the target and
proves the mapping property for equivariant CW sources.
-/

namespace BC4lean.ProperActions

universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {A : Type u} [TopologicalSpace A] [MulAction Γ A] [ContinuousConstSMul Γ A]

/-- Every finite-isotropy equivariant CW complex maps to the explicit probability simplex,
uniquely up to equivariant homotopy. -/
theorem EquivariantCWComplex.probability_homotopyTerminal
    (c : EquivariantCWComplex (topologicalAction Γ A)) :
    HomotopyTerminalFor Γ A (ProbabilitySimplex Γ) :=
  c.homotopyTerminal ProbabilitySimplex.fixedPointCriterion

omit [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- For countable Γ, the explicit target has a countable base. -/
theorem ProbabilitySimplex.secondCountable [Countable Γ] :
    SecondCountableTopology (ProbabilitySimplex Γ) := inferInstance

/-- For a countable group, the concrete target is proper and has the full cellular mapping property. -/
theorem probability_proper_universal_target [Countable Γ]
    (c : EquivariantCWComplex (topologicalAction Γ A)) :
    ProperSMul Γ (ProbabilitySimplex Γ) ∧ HomotopyTerminalFor Γ A (ProbabilitySimplex Γ) :=
  ⟨ProbabilitySimplex.proper, c.probability_homotopyTerminal⟩

/-- A Hausdorff finite-isotropy equivariant CW space has a proper action for countable Γ.
Hausdorffness remains an explicit premise until it is derived from the categorical CW data. -/
theorem EquivariantCWComplex.proper_of_t2 [Countable Γ] [T2Space A]
    (c : EquivariantCWComplex (topologicalAction Γ A)) : ProperSMul Γ A := by
  let : ProperSMul Γ (ProbabilitySimplex Γ) := ProbabilitySimplex.proper
  let : ContinuousSMul Γ A := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  obtain ⟨f⟩ := c.probability_homotopyTerminal.1
  exact f.properSMul

end BC4lean.ProperActions
