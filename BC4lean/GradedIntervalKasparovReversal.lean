import BC4lean.IntervalKasparovReversal
import BC4lean.GradedIntervalKasparovFibre
import BC4lean.FullGradedKasparovHomotopy

/-! # Reversal with the genuine pointwise coefficient grading

The proved arbitrary-module reversal construction is retained. The actual
semilinear grading commutes with coefficient reversal; its twisted inner
law descends without treating it as a coefficient-linear endomorphism.
All genuine graded cycle defects are transported by the actual compact
operator reversal map. Direct fibre evaluation identifies the full cycles.
-/

noncomputable section
universe uΓ uA uB uM uE
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {M : Type uM} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, B)ᵐᵒᵖ M] [CStarModule C(unitInterval, B)ᵐᵒᵖ M]
  [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

theorem intervalReversal_op_grading_commute (δ : CStarGrading B)
    (a : C(unitInterval, B)ᵐᵒᵖ) :
    opStarAlgEquiv intervalReversalCoefficient
      (opStarAlgEquiv δ.continuousSections.automorphism a) =
    opStarAlgEquiv δ.continuousSections.automorphism
      (opStarAlgEquiv intervalReversalCoefficient a) := by
  apply MulOpposite.unop_injective
  ext t
  rfl

/-- Genuine semilinear grading on the reversed coefficient module. -/
def GradedHilbertModule.gradedIntervalReversed
    (J : GradedHilbertModule (δB.continuousSections (X := unitInterval)) M) :
    GradedHilbertModule (δB.continuousSections (X := unitInterval))
      (IntervalReversedModule B M) where
  grading := J.grading
  involutive := J.involutive
  inner_grading x y := by
    change opStarAlgEquiv intervalReversalCoefficient
      ⟪J.grading (intervalReversedToOriginal x), J.grading (intervalReversedToOriginal y)⟫_
        (C(unitInterval, B)ᵐᵒᵖ) =
      opStarAlgEquiv δB.continuousSections.automorphism
        (opStarAlgEquiv intervalReversalCoefficient
          ⟪intervalReversedToOriginal x, intervalReversedToOriginal y⟫_
            (C(unitInterval, B)ᵐᵒᵖ))
    rw [J.inner_grading, intervalReversal_op_grading_commute]

namespace GradedKasparovCycle

/-- Reverse an actual cycle over continuous interval coefficients on an
arbitrary complete module, transporting all compact defects honestly. -/
def intervalReversed (c : GradedKasparovCycle α (β.continuousSections (X := unitInterval)) δA δB.continuousSections M) :
    GradedKasparovCycle α (β.continuousSections (X := unitInterval)) δA δB.continuousSections (IntervalReversedModule B M) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading := c.coefficientAction_preservesGrading
  countablyGenerated := c.countablyGenerated.intervalReversed
  grading := c.grading.gradedIntervalReversed
  groupAction := c.groupAction.intervalReversed
  grading_preserved := c.grading_preserved
  representation := intervalReversedOperatorHom.comp c.representation
  representation_graded a := c.representation_graded a
  representation_equivariant g a := by
    change c.groupAction.intervalReversed.conjugateOperator g
      (intervalReversedOperator (c.representation a)) =
        intervalReversedOperator (c.representation (α.automorphism g a))
    rw [c.groupAction.intervalReversed_conjugateOperator, c.representation_equivariant]
  operator := intervalReversedOperator c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((intervalReversedOperator c.operator - star (intervalReversedOperator c.operator)) *
      intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      intervalReversedOperator_star] using (c.selfadjoint_mod_compact a).intervalReversed
  square_mod_compact a := by
    change IsModuleCompact ((intervalReversedOperator c.operator * intervalReversedOperator c.operator - 1) *
      intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      intervalReversedOperator_one] using (c.square_mod_compact a).intervalReversed
  commutator_compact a := by
    change IsModuleCompact (intervalReversedOperator c.operator * intervalReversedOperator (c.representation a) -
      intervalReversedOperator (c.representation (δA.automorphism a)) * intervalReversedOperator c.operator)
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub] using
      (c.commutator_compact a).intervalReversed
  equivariance_mod_compact g a := by
    change IsModuleCompact ((c.groupAction.intervalReversed.conjugateOperator g (intervalReversedOperator c.operator) -
      intervalReversedOperator c.operator) * intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      c.groupAction.intervalReversed_conjugateOperator] using
        (c.equivariance_mod_compact g a).intervalReversed

end GradedKasparovCycle

namespace GradedKasparovCycleIso

/-- The specified reflected fibre has an actual whole-cycle unitary built
by direct evaluation, without a cast of completed fibre module structures. -/
def intervalReversedFibreAt
    (c : GradedKasparovCycle α (β.continuousSections (X := unitInterval)) δA δB.continuousSections M)
    (t s : unitInterval) (hs : unitInterval.symm t = s) :
    GradedKasparovCycleIso (c.intervalReversed.fibre t) (c.fibre s) where
  moduleEquiv := intervalReversedFibreEquivAt t s hs
  grading_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [GradedKasparovCycle.fibre_grading_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, GradedKasparovCycle.fibre_grading_mk]
    rfl
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [GradedKasparovCycle.fibre_action_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, GradedKasparovCycle.fibre_action_mk]
    rfl
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [GradedKasparovCycle.fibre_representation_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, GradedKasparovCycle.fibre_representation_mk]
    rfl
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [GradedKasparovCycle.fibre_operator_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, GradedKasparovCycle.fibre_operator_mk]
    rfl

end GradedKasparovCycleIso

namespace FullGradedKasparovHomotopy

private def gradedReversalIntervalCycle
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy.{uΓ, uA, uB, uE} c d) :
    BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (β.continuousSections (X := unitInterval))
      δA (δB.continuousSections (X := unitInterval)) :=
  BundledGradedKasparovCycle.of h.intervalCycle.cycle.intervalReversed

private def gradedReversalSourceIso
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy.{uΓ, uA, uB, uE} c d) :
    GradedKasparovCycleIso ((gradedReversalIntervalCycle h).cycle.fibre (0 : unitInterval))
      d.cycle := by
  change GradedKasparovCycleIso
    (h.intervalCycle.cycle.intervalReversed.fibre (0 : unitInterval)) d.cycle
  exact GradedKasparovCycleIso.trans
    (c := h.intervalCycle.cycle.intervalReversed.fibre (0 : unitInterval))
    (d := h.intervalCycle.cycle.fibre (1 : unitInterval))
    (k := d.cycle)
    (E := HilbertModuleFibre B (IntervalReversedModule B h.intervalCycle.carrier)
      (0 : unitInterval))
    (F := HilbertModuleFibre B h.intervalCycle.carrier (1 : unitInterval))
    (G := d.carrier)
    (GradedKasparovCycleIso.intervalReversedFibreAt
      (M := h.intervalCycle.carrier) h.intervalCycle.cycle 0 1 unitInterval.symm_zero)
    h.targetIso

private def gradedReversalTargetIso
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy.{uΓ, uA, uB, uE} c d) :
    GradedKasparovCycleIso ((gradedReversalIntervalCycle h).cycle.fibre (1 : unitInterval))
      c.cycle := by
  change GradedKasparovCycleIso
    (h.intervalCycle.cycle.intervalReversed.fibre (1 : unitInterval)) c.cycle
  exact GradedKasparovCycleIso.trans
    (c := h.intervalCycle.cycle.intervalReversed.fibre (1 : unitInterval))
    (d := h.intervalCycle.cycle.fibre (0 : unitInterval))
    (k := c.cycle)
    (E := HilbertModuleFibre B (IntervalReversedModule B h.intervalCycle.carrier)
      (1 : unitInterval))
    (F := HilbertModuleFibre B h.intervalCycle.carrier (0 : unitInterval))
    (G := c.carrier)
    (GradedKasparovCycleIso.intervalReversedFibreAt
      (M := h.intervalCycle.carrier) h.intervalCycle.cycle 1 0 unitInterval.symm_one)
    h.sourceIso

/-- A single actual reversed interval witness proves symmetry. -/
def symm {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy.{uΓ, uA, uB, uE} c d) :
    FullGradedKasparovHomotopy.{uΓ, uA, uB, uE} d c where
  intervalCycle := gradedReversalIntervalCycle h
  sourceIso := gradedReversalSourceIso h
  targetIso := gradedReversalTargetIso h

end FullGradedKasparovHomotopy
end BC4lean.KKTheory
