import BC4lean.GroupULiftHilbertModule
import BC4lean.KasparovCycleTransport
import BC4lean.OddKasparovCycleIso
import BC4lean.GradedKasparovCycleIso

/-! # Whole raw cycles transported to genuine lifted modules

These constructions transport the actual actions, gradings, representation,
operator and all four localized compact defects. Both odd and genuinely
graded even cycles may have module universes independent of their algebras.
-/

noncomputable section
universe uΓ uA uB uE uF v
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB}
  {E : Type uE} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

def unitaryTransport (c : OddKasparovCycle α β E) (u : HilbertModuleEquiv B E F) :
    OddKasparovCycle α β F where
  countablyGenerated := c.countablyGenerated.map_linearIsometryEquiv
    u.linearIsometryEquiv id u.map_op_smul
  groupAction := u.transportAction c.groupAction
  representation := u.transportStarAlgEquiv.toNonUnitalStarAlgHom.comp c.representation
  representation_equivariant g a := by
    change (u.transportAction c.groupAction).conjugateOperator g
      (u.transport (c.representation a)) = u.transport (c.representation (α.automorphism g a))
    rw [u.transportAction_conjugateOperator, c.representation_equivariant]
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
    change IsModuleCompact (((u.transportAction c.groupAction).conjugateOperator g
      (u.transport c.operator) - u.transport c.operator) * u.transport (c.representation a))
    rw [u.transportAction_conjugateOperator]
    have h := (u.transport_isModuleCompact_iff _).2 (c.equivariance_mod_compact g a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub] using h

def unitaryTransportIso (c : OddKasparovCycle α β E) (u : HilbertModuleEquiv B E F) :
    OddKasparovCycleIso c (c.unitaryTransport u) where
  moduleEquiv := u
  action_intertwine := u.transportAction_intertwine c.groupAction
  representation_intertwine a x := by
    change u (c.representation a x) = u (c.representation a (u.symm (u x)))
    rw [u.symm_apply_apply]
  operator_intertwine x := by
    change u (c.operator x) = u (c.operator (u.symm (u x)))
    rw [u.symm_apply_apply]

def ulift (c : OddKasparovCycle α β E) : OddKasparovCycle α β (ULift.{v} E) :=
  c.unitaryTransport (hilbertModuleULiftUp (B := B))

def uliftIso (c : OddKasparovCycle α β E) : OddKasparovCycleIso c c.ulift :=
  c.unitaryTransportIso (hilbertModuleULiftUp (B := B))

@[simp] theorem ulift_action (c : OddKasparovCycle α β E) (g : Γ) (x : ULift.{v} E) :
    c.ulift.groupAction.action g x = ULift.up (c.groupAction.action g x.down) := rfl

@[simp] theorem ulift_representation (c : OddKasparovCycle α β E) (a : A)
    (x : ULift.{v} E) :
    c.ulift.representation a x = ULift.up (c.representation a x.down) := rfl

@[simp] theorem ulift_operator (c : OddKasparovCycle α β E) (x : ULift.{v} E) :
    c.ulift.operator x = ULift.up (c.operator x.down) := rfl

theorem ulift_isDegenerate (c : OddKasparovCycle α β E) (h : c.IsDegenerate) :
    (c.ulift : OddKasparovCycle α β (ULift.{v} E)).IsDegenerate := by
  let u : HilbertModuleEquiv B E (ULift.{v} E) := hilbertModuleULiftUp (B := B) (E := E)
  constructor
  · intro a
    change (u.transport c.operator - star (u.transport c.operator)) *
      u.transport (c.representation a) = 0
    have hh := congrArg u.transport (h.1 a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_star, HilbertModuleEquiv.transport_zero] using hh
  constructor
  · intro a
    change (u.transport c.operator * u.transport c.operator - 1) *
      u.transport (c.representation a) = 0
    have hh := congrArg u.transport (h.2.1 a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_one, HilbertModuleEquiv.transport_zero] using hh
  constructor
  · intro a
    change u.transport c.operator * u.transport (c.representation a) -
      u.transport (c.representation a) * u.transport c.operator = 0
    have hh := congrArg u.transport (h.2.2.1 a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_zero] using hh
  · intro g a
    change ((u.transportAction c.groupAction).conjugateOperator g
      (u.transport c.operator) - u.transport c.operator) * u.transport (c.representation a) = 0
    rw [u.transportAction_conjugateOperator]
    have hh := congrArg u.transport (h.2.2.2 g a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_zero] using hh

end OddKasparovCycle

namespace OddKasparovCycleIso

def ulift {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
    (e : OddKasparovCycleIso c d) : OddKasparovCycleIso
      (c.ulift : OddKasparovCycle α β (ULift.{v} E)) d.ulift :=
  c.uliftIso.symm.trans (e.trans d.uliftIso)

end OddKasparovCycleIso

namespace KasparovCycle

def ulift (c : KasparovCycle α β E) : KasparovCycle α β (ULift.{v} E) :=
  c.transport (hilbertModuleULiftUp (B := B))

def uliftIso (c : KasparovCycle α β E) : KasparovCycleIso c c.ulift :=
  c.transportIso (hilbertModuleULiftUp (B := B))

end KasparovCycle

namespace GradedKasparovCycle
variable {δA : CStarGrading A} {δB : CStarGrading B}

def unitaryTransport (c : GradedKasparovCycle α β δA δB E)
    (u : HilbertModuleEquiv B E F) : GradedKasparovCycle α β δA δB F where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading := c.coefficientAction_preservesGrading
  countablyGenerated := c.countablyGenerated.map_linearIsometryEquiv
    u.linearIsometryEquiv id u.map_op_smul
  grading := u.transportGrading c.grading
  groupAction := u.transportAction c.groupAction
  grading_preserved := u.transportAction_preservesGrading c.groupAction c.grading c.grading_preserved
  representation := u.transportStarAlgEquiv.toNonUnitalStarAlgHom.comp c.representation
  representation_graded a x := by
    change u (c.grading.grading (u.symm (u (c.representation a (u.symm x))))) =
      u (c.representation (δA.automorphism a)
        (u.symm (u (c.grading.grading (u.symm x)))))
    simp only [u.symm_apply_apply]
    exact congrArg u (c.representation_graded a (u.symm x))
  representation_equivariant g a := by
    change (u.transportAction c.groupAction).conjugateOperator g
      (u.transport (c.representation a)) = u.transport (c.representation (α.automorphism g a))
    rw [u.transportAction_conjugateOperator, c.representation_equivariant]
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
    change IsModuleCompact (((u.transportAction c.groupAction).conjugateOperator g
      (u.transport c.operator) - u.transport c.operator) * u.transport (c.representation a))
    rw [u.transportAction_conjugateOperator]
    have h := (u.transport_isModuleCompact_iff _).2 (c.equivariance_mod_compact g a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub] using h

def unitaryTransportIso (c : GradedKasparovCycle α β δA δB E)
    (u : HilbertModuleEquiv B E F) : GradedKasparovCycleIso c (c.unitaryTransport u) where
  moduleEquiv := u
  grading_intertwine := u.transportGrading_intertwine c.grading
  action_intertwine := u.transportAction_intertwine c.groupAction
  representation_intertwine a x := by
    change u (c.representation a x) = u (c.representation a (u.symm (u x)))
    rw [u.symm_apply_apply]
  operator_intertwine x := by
    change u (c.operator x) = u (c.operator (u.symm (u x)))
    rw [u.symm_apply_apply]

def ulift (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle α β δA δB (ULift.{v} E) :=
  c.unitaryTransport (hilbertModuleULiftUp (B := B))

def uliftIso (c : GradedKasparovCycle α β δA δB E) : GradedKasparovCycleIso c c.ulift :=
  c.unitaryTransportIso (hilbertModuleULiftUp (B := B))

end GradedKasparovCycle
end BC4lean.KKTheory
