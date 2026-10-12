import BC4lean.KasparovCycleTransport
import BC4lean.OddKasparovCycleIso

/-! # Whole Hilbert-module transport of genuine odd cycles

Every raw cycle field is conjugated by the same coefficient-form unitary.
The four actual module compact defects are transported, and the resulting
whole-cycle isomorphism retains the actual group action and representation.
-/

noncomputable section
namespace BC4lean.KKTheory.OddKasparovCycle

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def transport (c : OddKasparovCycle α β E) (u : HilbertModuleEquiv B E F) :
    OddKasparovCycle α β F where
  countablyGenerated := c.countablyGenerated.map_linearIsometryEquiv
    u.linearIsometryEquiv id u.map_op_smul
  groupAction := u.transportAction c.groupAction
  representation := u.transportStarAlgEquiv.toNonUnitalStarAlgHom.comp c.representation
  representation_equivariant g a := by
    simp only [HilbertModuleEquiv.transportRepresentation_apply]
    rw [u.transportAction_conjugateOperator]
    exact congrArg u.transport (c.representation_equivariant g a)
  operator := u.transport c.operator
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

@[simp] theorem transport_operator (c : OddKasparovCycle α β E)
    (u : HilbertModuleEquiv B E F) : (c.transport u).operator = u.transport c.operator := rfl

@[simp] theorem transport_representation (c : OddKasparovCycle α β E)
    (u : HilbertModuleEquiv B E F) (a : A) :
    (c.transport u).representation a = u.transport (c.representation a) := rfl

def transportIso (c : OddKasparovCycle α β E) (u : HilbertModuleEquiv B E F) :
    OddKasparovCycleIso c (c.transport u) where
  moduleEquiv := u
  action_intertwine := u.transportAction_intertwine c.groupAction
  representation_intertwine a x := by
    simp only [transport_representation, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  operator_intertwine x := by
    simp only [transport_operator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory.OddKasparovCycle
