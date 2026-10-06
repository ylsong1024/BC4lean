import BC4lean.ModuleCreationMap
import BC4lean.ScalarCreationCycleCounterexample
import BC4lean.StandardKasparovCycle

/-! # The creation compactness counterexample in the constructed interior tensor

The first actual cycle is the standard scalar module ℂ_ℂ with operator zero;
the second is the genuine graded infinite Hilbert sum and odd unitary flip.
Creation by 1 in the actual completed interior tensor has adjoint square equal
to the identity of the second module. That identity is not module compact.
The proved compact-ideal composition law would make the adjoint square compact
if creation were compact. The contradiction uses the actual completed tensor
and its proved adjoint identity.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped ComplexOrder ScalarHilbertModule ScalarCreationCycleCounterexample

namespace InteriorCreationCycleCounterexample

abbrev Pair := ScalarCreationCycleCounterexample.Pair
abbrev scalarAction := ScalarCreationCycleCounterexample.scalarAction

/-- The second module's identity is genuinely noncompact. -/
theorem pairIdentity_not_moduleCompact :
    ¬ IsModuleCompact (1 : AdjointableMap ℂ Pair Pair) := by
  intro h
  have hC := ScalarHilbertModule.isCompactOperator_of_isModuleCompact h
  have hH := (hC.comp_clm
    (sumInl (B := ℂ) (E := ScalarCreationCycleCounterexample.H)
      (F := ScalarCreationCycleCounterexample.H)).toCLM).clm_comp
    (sumFst (B := ℂ) (E := ScalarCreationCycleCounterexample.H)
      (F := ScalarCreationCycleCounterexample.H)).toCLM
  exact l2Nat_identity_not_compact hH

/-- Both input objects are genuine full scalar Kasparov cycles. -/
def firstCycle : KasparovCycle scalarAction scalarAction ℂᵐᵒᵖ :=
  standardIdentityCycle scalarAction

/-- Creation into the actual completed interior tensor attached to the two cycles. -/
def creationAtOne : AdjointableMap ℂ Pair
    (UniformSpace.Completion
      (PreHilbertModuleTensor (E := ℂᵐᵒᵖ)
        ScalarCreationCycleCounterexample.secondCycle.representation)) :=
  moduleCreationMap ScalarCreationCycleCounterexample.secondCycle.representation
    (MulOpposite.op 1)

/-- Its actual adjoint square is the second module's identity. -/
theorem creationAtOne_adjoint_comp : creationAtOne.adjoint.comp creationAtOne = 1 := by
  rw [creationAtOne, moduleCreationMap_adjoint_comp, standard_module_inner, star_one, one_mul]
  change ScalarCreationCycleCounterexample.scalarRepresentation Pair 1 = 1
  ext y
  simp only [ScalarCreationCycleCounterexample.scalarRepresentation_apply,
    AdjointableMap.one_apply, one_smul]

/-- Creation fails compactness even for the full cycle hypotheses, in the
constructed general completed interior tensor. -/
theorem creationAtOne_not_moduleCompact : ¬ IsModuleCompact creationAtOne := by
  intro h
  have hsq := h.comp_left creationAtOne.adjoint
  rw [creationAtOne_adjoint_comp] at hsq
  exact pairIdentity_not_moduleCompact hsq

/-- The concrete first and second full cycles, and the exact noncompact creation map. -/
theorem fullCycleCounterexample :
    ∃ (c : KasparovCycle scalarAction scalarAction ℂᵐᵒᵖ)
      (d : KasparovCycle scalarAction scalarAction Pair),
      c.operator = 0 ∧ d.IsDegenerate ∧ ¬ IsModuleCompact creationAtOne :=
  ⟨firstCycle, ScalarCreationCycleCounterexample.secondCycle, rfl,
    ScalarCreationCycleCounterexample.secondCycle_isDegenerate,
    creationAtOne_not_moduleCompact⟩

end InteriorCreationCycleCounterexample
end BC4lean.KKTheory
