import BC4lean.IntervalKasparovFibre

/-! # Odd cycles on genuine fibres of arbitrary interval modules -/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B X M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

namespace OddKasparovCycle
variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Every arbitrary odd interval cycle descends through the evaluated
radical quotient and its actual Hilbert-module completion. -/
def fibre (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    OddKasparovCycle α β (HilbertModuleFibre B M t) where
  countablyGenerated := c.countablyGenerated.fibre t
  groupAction := c.groupAction.fibre t
  representation := (hilbertModuleFibreOperatorHom t).toNonUnitalStarAlgHom.comp c.representation
  representation_equivariant g a := by
    change (c.groupAction.fibre t).conjugateOperator g
      (hilbertModuleFibreOperator t (c.representation a)) =
        hilbertModuleFibreOperator t (c.representation (α.automorphism g a))
    rw [c.groupAction.fibre_conjugateOperator]
    exact congrArg (hilbertModuleFibreOperator (B := B) t) (c.representation_equivariant g a)
  operator := hilbertModuleFibreOperator t c.operator
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((hilbertModuleFibreOperator t c.operator -
      star (hilbertModuleFibreOperator t c.operator)) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.selfadjoint_mod_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_star] using h
  square_mod_compact a := by
    change IsModuleCompact ((hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t c.operator - 1) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.square_mod_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_one] using h
  commutator_compact a := by
    change IsModuleCompact (hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t (c.representation a) -
        hilbertModuleFibreOperator t (c.representation a) *
          hilbertModuleFibreOperator t c.operator)
    have h := (c.commutator_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub] using h
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.fibre t).conjugateOperator g
      (hilbertModuleFibreOperator t c.operator) - hilbertModuleFibreOperator t c.operator) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.equivariance_mod_compact g a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      c.groupAction.fibre_conjugateOperator] using h

@[simp] theorem fibre_operator_mk
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) (x : M) :
    (c.fibre t).operator (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.operator x) :=
  hilbertModuleFibreOperator_mk t c.operator x

@[simp] theorem fibre_representation_mk
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) (a : A) (x : M) :
    (c.fibre t).representation a (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.representation a x) :=
  hilbertModuleFibreOperator_mk t (c.representation a) x

@[simp] theorem fibre_action_mk
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) (g : Γ) (x : M) :
    (c.fibre t).groupAction.action g (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.groupAction.action g x) :=
  c.groupAction.fibre_action_mk t g x

end OddKasparovCycle
end BC4lean.KKTheory
