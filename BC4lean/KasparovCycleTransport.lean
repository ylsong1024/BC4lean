import BC4lean.KasparovCycleIso

/-! # Transport of raw Kasparov cycles between module types

Unitary coefficient-linear module equivalences transport the grading, compatible
group action, representation and Fredholm operator. Countable generation and
all four compact defects are proved for the transported data. The result is
an actual raw cycle and a genuine cycle isomorphism to it; no quotient is used.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

namespace HilbertModuleEquiv

/-- Conjugate a complex-linear isometric automorphism across the module types. -/
def conjugateLinearIsometryEquiv (u : HilbertModuleEquiv B E F) (v : E ≃ₗᵢ[ℂ] E) :
    F ≃ₗᵢ[ℂ] F :=
  u.linearIsometryEquiv.symm.trans (v.trans u.linearIsometryEquiv)
@[simp] theorem conjugateLinearIsometryEquiv_apply (u : HilbertModuleEquiv B E F)
    (v : E ≃ₗᵢ[ℂ] E) (y : F) :
    u.conjugateLinearIsometryEquiv v y = u (v (u.symm y)) := rfl

/-- Transport a genuine module grading, including its coefficient-inner-product law. -/
def transportGrading {δ : CStarGrading B} (u : HilbertModuleEquiv B E F)
    (γ : GradedHilbertModule δ E) : GradedHilbertModule δ F where
  grading := u.conjugateLinearIsometryEquiv γ.grading
  involutive y := by
    simp only [conjugateLinearIsometryEquiv_apply, symm_apply_apply, γ.grading_sq,
      apply_symm_apply]
  inner_grading x y := by
    simp only [conjugateLinearIsometryEquiv_apply]
    rw [u.inner_map, γ.inner_grading, u.symm.inner_map]

@[simp] theorem transportGrading_apply {δ : CStarGrading B}
    (u : HilbertModuleEquiv B E F) (γ : GradedHilbertModule δ E) (y : F) :
    (u.transportGrading γ).grading y = u (γ.grading (u.symm y)) := rfl

/-- The transported grading is intertwined by the original module equivalence. -/
theorem transportGrading_intertwine {δ : CStarGrading B}
    (u : HilbertModuleEquiv B E F) (γ : GradedHilbertModule δ E) (x : E) :
    u (γ.grading x) = (u.transportGrading γ).grading (u x) := by
  simp only [transportGrading_apply, symm_apply_apply]

/-- Transport the actual group action, with its identity and multiplication laws. -/
def transportAction {β : CStarAlgebraAction Γ B} (u : HilbertModuleEquiv B E F)
    (U : EquivariantHilbertModule β E) : EquivariantHilbertModule β F where
  action :=
    { toFun g := u.conjugateLinearIsometryEquiv (U.action g)
      map_one' := by
        ext y
        simp only [conjugateLinearIsometryEquiv_apply, U.one_apply, apply_symm_apply,
          LinearIsometryEquiv.coe_one, id_eq]
      map_mul' g h := by
        ext y
        simp only [conjugateLinearIsometryEquiv_apply, U.mul_apply,
          LinearIsometryEquiv.coe_mul, Function.comp_apply, symm_apply_apply] }
  inner_action g x y := by
    change ⟪u (U.action g (u.symm x)), u (U.action g (u.symm y))⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv (β.automorphism g) ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [u.inner_map, U.inner_action, u.symm.inner_map]

@[simp] theorem transportAction_apply {β : CStarAlgebraAction Γ B}
    (u : HilbertModuleEquiv B E F) (U : EquivariantHilbertModule β E) (g : Γ) (y : F) :
    (u.transportAction U).action g y = u (U.action g (u.symm y)) := rfl

/-- The transported group action is exactly intertwined. -/
theorem transportAction_intertwine {β : CStarAlgebraAction Γ B}
    (u : HilbertModuleEquiv B E F) (U : EquivariantHilbertModule β E) (g : Γ) (x : E) :
    u (U.action g x) = (u.transportAction U).action g (u x) := by
  simp only [transportAction_apply, symm_apply_apply]

/-- Grading preservation persists for the transported genuine action. -/
theorem transportAction_preservesGrading {δ : CStarGrading B}
    {β : CStarAlgebraAction Γ B} (u : HilbertModuleEquiv B E F)
    (U : EquivariantHilbertModule β E) (γ : GradedHilbertModule δ E)
    (h : U.PreservesGrading γ) :
    (u.transportAction U).PreservesGrading (u.transportGrading γ) := by
  intro g y
  simp only [transportAction_apply, transportGrading_apply, symm_apply_apply]
  exact congrArg u (h g (u.symm y))

/-- Transport preserves the degree of an even endomorphism. -/
theorem transport_isEven {δ : CStarGrading B} (u : HilbertModuleEquiv B E F)
    (γ : GradedHilbertModule δ E) {T : AdjointableMap B E E}
    (hT : γ.IsEven γ T) : (u.transportGrading γ).IsEven (u.transportGrading γ) (u.transport T) := by
  intro y
  simp only [transportGrading_apply, transport_apply, symm_apply_apply]
  exact congrArg u (hT (u.symm y))

/-- Transport preserves oddness of the Fredholm operator. -/
theorem transport_isOdd {δ : CStarGrading B} (u : HilbertModuleEquiv B E F)
    (γ : GradedHilbertModule δ E) {T : AdjointableMap B E E}
    (hT : γ.IsOdd γ T) : (u.transportGrading γ).IsOdd (u.transportGrading γ) (u.transport T) := by
  intro y
  simp only [transportGrading_apply, transport_apply, symm_apply_apply]
  rw [hT (u.symm y), map_neg]

/-- Operator transport commutes with conjugation by the transported module action. -/
theorem transportAction_conjugateOperator {β : CStarAlgebraAction Γ B}
    (u : HilbertModuleEquiv B E F) (U : EquivariantHilbertModule β E) (g : Γ)
    (T : AdjointableMap B E E) :
    (u.transportAction U).conjugateOperator g (u.transport T) =
      u.transport (U.conjugateOperator g T) := by
  ext y
  simp only [EquivariantHilbertModule.conjugateMap_apply,
    transportAction_apply, transport_apply, symm_apply_apply]

/-- Explicit application rule for the transported nonunital representation. -/
@[simp] theorem transportRepresentation_apply (u : HilbertModuleEquiv B E F)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) :
    (u.transportStarAlgEquiv.toNonUnitalStarAlgHom.comp π) a = u.transport (π a) := rfl

end HilbertModuleEquiv

variable [StarOrderedRing B] [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- Transport every part of a raw cycle by an actual unitary module equivalence. -/
def transport (c : KasparovCycle α β E) (u : HilbertModuleEquiv B E F) :
    KasparovCycle α β F where
  countablyGenerated := c.countablyGenerated.map_linearIsometryEquiv
    u.linearIsometryEquiv id u.map_op_smul
  grading := u.transportGrading c.grading
  groupAction := u.transportAction c.groupAction
  grading_preserved := u.transportAction_preservesGrading c.groupAction c.grading c.grading_preserved
  representation := u.transportStarAlgEquiv.toNonUnitalStarAlgHom.comp c.representation
  representation_even a := u.transport_isEven c.grading (c.representation_even a)
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

@[simp] theorem transport_operator (c : KasparovCycle α β E)
    (u : HilbertModuleEquiv B E F) : (c.transport u).operator = u.transport c.operator := rfl

@[simp] theorem transport_representation (c : KasparovCycle α β E)
    (u : HilbertModuleEquiv B E F) (a : A) :
    (c.transport u).representation a = u.transport (c.representation a) := rfl

/-- Exact vanishing of all four defects persists under unitary cycle transport. -/
theorem transport_isDegenerate (c : KasparovCycle α β E)
    (u : HilbertModuleEquiv B E F) (h : c.IsDegenerate) : (c.transport u).IsDegenerate := by
  constructor
  · intro a
    have h' := congrArg u.transport (h.1 a)
    simpa only [transport_operator, transport_representation, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_star,
      HilbertModuleEquiv.transport_zero] using h'
  constructor
  · intro a
    have h' := congrArg u.transport (h.2.1 a)
    simpa only [transport_operator, transport_representation, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
      HilbertModuleEquiv.transport_zero] using h'
  constructor
  · intro a
    have h' := congrArg u.transport (h.2.2.1 a)
    simpa only [transport_operator, transport_representation, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_zero] using h'
  · intro g a
    change ((u.transportAction c.groupAction).conjugateOperator g
      (u.transport c.operator) - u.transport c.operator) *
      u.transport (c.representation a) = 0
    rw [u.transportAction_conjugateOperator]
    have h' := congrArg u.transport (h.2.2.2 g a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_zero] using h'

/-- The original and transported cycles are genuinely isomorphic across module types. -/
def transportIso (c : KasparovCycle α β E) (u : HilbertModuleEquiv B E F) :
    KasparovCycleIso c (c.transport u) where
  moduleEquiv := u
  grading_intertwine := u.transportGrading_intertwine c.grading
  action_intertwine := u.transportAction_intertwine c.groupAction
  representation_intertwine a x := by
    simp only [transport_representation, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  operator_intertwine x := by
    simp only [transport_operator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]

end KasparovCycle
end BC4lean.KKTheory
