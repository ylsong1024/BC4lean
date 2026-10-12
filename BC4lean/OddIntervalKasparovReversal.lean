import BC4lean.FullCliffordParityHomotopy
import BC4lean.IntervalKasparovReversal

/-! # Reversing genuine full odd arbitrary-module interval homotopies

The actual reversed coefficient-module structures and compact rank-one
transport are reused. Odd cycles have no module grading to transport.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, B)ᵐᵒᵖ M] [CStarModule C(unitInterval, B)ᵐᵒᵖ M]
  [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

/-- Reverse an actual cycle over continuous interval coefficients on an
arbitrary complete module, transporting all compact defects honestly. -/
def intervalReversed (c : OddKasparovCycle α (β.continuousSections (X := unitInterval)) M) :
    OddKasparovCycle α (β.continuousSections (X := unitInterval)) (IntervalReversedModule B M) where
  countablyGenerated := c.countablyGenerated.intervalReversed
  groupAction := c.groupAction.intervalReversed
  representation := intervalReversedOperatorHom.comp c.representation
  representation_equivariant g a := by
    change c.groupAction.intervalReversed.conjugateOperator g
      (intervalReversedOperator (c.representation a)) =
        intervalReversedOperator (c.representation (α.automorphism g a))
    rw [c.groupAction.intervalReversed_conjugateOperator, c.representation_equivariant]
  operator := intervalReversedOperator c.operator
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((intervalReversedOperator c.operator -
      star (intervalReversedOperator c.operator)) * intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      intervalReversedOperator_star] using (c.selfadjoint_mod_compact a).intervalReversed
  square_mod_compact a := by
    change IsModuleCompact ((intervalReversedOperator c.operator *
      intervalReversedOperator c.operator - 1) * intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      intervalReversedOperator_one] using (c.square_mod_compact a).intervalReversed
  commutator_compact a := by
    change IsModuleCompact (intervalReversedOperator c.operator *
      intervalReversedOperator (c.representation a) -
        intervalReversedOperator (c.representation a) * intervalReversedOperator c.operator)
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub] using
      (c.commutator_compact a).intervalReversed
  equivariance_mod_compact g a := by
    change IsModuleCompact ((c.groupAction.intervalReversed.conjugateOperator g
      (intervalReversedOperator c.operator) - intervalReversedOperator c.operator) *
        intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      c.groupAction.intervalReversed_conjugateOperator] using
        (c.equivariance_mod_compact g a).intervalReversed

end OddKasparovCycle

namespace OddKasparovCycleIso

/-- Reversal of an arbitrary interval cycle identifies every part of the
completed fibre cycle with the original cycle at the reflected parameter. -/
def intervalReversedFibre
    (c : OddKasparovCycle α (β.continuousSections (X := unitInterval)) M) (t : unitInterval) :
    OddKasparovCycleIso (c.intervalReversed.fibre t) (c.fibre (unitInterval.symm t)) where
  moduleEquiv := intervalReversedFibreEquiv t
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange
      (B := B) (M := IntervalReversedModule B M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_action_mk, intervalReversedFibreEquiv_mk,
        intervalReversedFibreEquiv_mk, OddKasparovCycle.fibre_action_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange
      (B := B) (M := IntervalReversedModule B M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_representation_mk, intervalReversedFibreEquiv_mk,
        intervalReversedFibreEquiv_mk, OddKasparovCycle.fibre_representation_mk]
      rfl
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange
      (B := B) (M := IntervalReversedModule B M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_operator_mk, intervalReversedFibreEquiv_mk,
        intervalReversedFibreEquiv_mk, OddKasparovCycle.fibre_operator_mk]
      rfl

/-- Directly identify a specified reflected fibre using the actual native
evaluation unitary, retaining the full action, representation and operator. -/
def intervalReversedFibreAt
    (c : OddKasparovCycle α (β.continuousSections (X := unitInterval)) M)
    (t s : unitInterval) (hs : unitInterval.symm t = s) :
    OddKasparovCycleIso (c.intervalReversed.fibre t) (c.fibre s) where
  moduleEquiv := intervalReversedFibreEquivAt t s hs
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [OddKasparovCycle.fibre_action_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, OddKasparovCycle.fibre_action_mk]
    rfl
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [OddKasparovCycle.fibre_representation_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, OddKasparovCycle.fibre_representation_mk]
    rfl
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [OddKasparovCycle.fibre_operator_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, OddKasparovCycle.fibre_operator_mk]
    rfl

end OddKasparovCycleIso

namespace FullOddKasparovHomotopy

set_option maxHeartbeats 800000 in
/-- Symmetry is represented by a single genuine reversed interval cycle on
the actual twisted arbitrary module, with actual whole-cycle endpoint unitaries. -/
def symm {c d : BundledOddKasparovCycle α β} (h : FullOddKasparovHomotopy c d) :
    FullOddKasparovHomotopy d c where
  intervalCycle := BundledOddKasparovCycle.of h.intervalCycle.cycle.intervalReversed
  sourceIso := (OddKasparovCycleIso.intervalReversedFibreAt
    h.intervalCycle.cycle 0 1 unitInterval.symm_zero).trans h.targetIso
  targetIso := (OddKasparovCycleIso.intervalReversedFibreAt
    h.intervalCycle.cycle 1 0 unitInterval.symm_one).trans h.sourceIso

end FullOddKasparovHomotopy
end BC4lean.KKTheory
