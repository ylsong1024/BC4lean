import BC4lean.KasparovCycleTransport
import BC4lean.GradedKasparovCycleIso

/-! # Whole Hilbert-module transport of genuine graded cycles

Both algebra gradings remain explicit. The same actual module unitary
transports the grading, action, representation and operator, and all four
actual compact defects, including the graded source commutator.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedKasparovCycle

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

def transport (c : GradedKasparovCycle α β δA δB E) (u : HilbertModuleEquiv B E F) :
    GradedKasparovCycle α β δA δB F where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading := c.coefficientAction_preservesGrading
  countablyGenerated := c.countablyGenerated.map_linearIsometryEquiv
    u.linearIsometryEquiv id u.map_op_smul
  grading := u.transportGrading c.grading
  groupAction := u.transportAction c.groupAction
  grading_preserved := u.transportAction_preservesGrading c.groupAction c.grading c.grading_preserved
  representation := u.transportStarAlgEquiv.toNonUnitalStarAlgHom.comp c.representation
  representation_graded a y := by
    simp only [HilbertModuleEquiv.transportGrading_apply,
      HilbertModuleEquiv.transportRepresentation_apply,
      HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
    exact congrArg u (c.representation_graded a (u.symm y))
  representation_equivariant g a := by
    simp only [HilbertModuleEquiv.transportRepresentation_apply]
    rw [u.transportAction_conjugateOperator]
    exact congrArg u.transport (c.representation_equivariant g a)
  operator := u.transport c.operator
  operator_odd := u.transport_isOdd c.grading c.operator_odd
  selfadjoint_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (c.selfadjoint_mod_compact a)
    simpa only [HilbertModuleEquiv.transportRepresentation_apply,
      HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_star] using h
  square_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (c.square_mod_compact a)
    simpa only [HilbertModuleEquiv.transportRepresentation_apply,
      HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_one] using h
  commutator_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (c.commutator_compact a)
    simpa only [HilbertModuleEquiv.transportRepresentation_apply,
      HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub] using h
  equivariance_mod_compact g a := by
    rw [u.transportAction_conjugateOperator]
    have h := (u.transport_isModuleCompact_iff _).2 (c.equivariance_mod_compact g a)
    simpa only [HilbertModuleEquiv.transportRepresentation_apply,
      HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub] using h

@[simp] theorem transport_operator (c : GradedKasparovCycle α β δA δB E)
    (u : HilbertModuleEquiv B E F) : (c.transport u).operator = u.transport c.operator := rfl

@[simp] theorem transport_representation (c : GradedKasparovCycle α β δA δB E)
    (u : HilbertModuleEquiv B E F) (a : A) :
    (c.transport u).representation a = u.transport (c.representation a) := rfl

def transportIso (c : GradedKasparovCycle α β δA δB E) (u : HilbertModuleEquiv B E F) :
    GradedKasparovCycleIso c (c.transport u) where
  moduleEquiv := u
  grading_intertwine := u.transportGrading_intertwine c.grading
  action_intertwine := u.transportAction_intertwine c.groupAction
  representation_intertwine a x := by
    simp only [transport_representation, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  operator_intertwine x := by
    simp only [transport_operator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory.GradedKasparovCycle
