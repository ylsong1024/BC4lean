import BC4lean.ConeKasparovHomotopy
import BC4lean.BundledOddKasparovOperations
import BC4lean.OddIntervalKasparovFibre

/-! # Actual cone witnesses for exactly degenerate odd cycles

The genuine closed cone module and its evaluated fibre unitaries are reused.
Every defect is proved exactly zero, so no pointwise-compactness assumption
is substituted for actual module compactness.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

namespace OddKasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- An exactly degenerate cycle gives an actual interval cycle on the cone,
whose defects are proved zero rather than assumed compact pointwise. -/
def degenerateCone (c : OddKasparovCycle α β E) (hc : c.IsDegenerate) :
    OddKasparovCycle α (β.continuousSections (X := unitInterval)) (ConeHilbertModule B E) where
  countablyGenerated := cone_isCountablyGenerated c.countablyGenerated
  groupAction := c.groupAction.cone
  representation := coneOperatorHom.toNonUnitalStarAlgHom.comp c.representation
  representation_equivariant g a := by
    change c.groupAction.cone.conjugateOperator g (coneOperator (c.representation a)) = _
    rw [c.groupAction.cone_conjugateOperator, c.representation_equivariant]
    rfl
  operator := coneOperator c.operator
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((coneOperator c.operator - star (coneOperator c.operator)) *
      coneOperator (c.representation a))
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.1 a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_star, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero
  square_mod_compact a := by
    change IsModuleCompact ((coneOperator c.operator * coneOperator c.operator - 1) *
      coneOperator (c.representation a))
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.2.1 a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_one, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero
  commutator_compact a := by
    change IsModuleCompact (coneOperator c.operator * coneOperator (c.representation a) -
      coneOperator (c.representation a) * coneOperator c.operator)
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.2.2.1 a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero
  equivariance_mod_compact g a := by
    change IsModuleCompact ((c.groupAction.cone.conjugateOperator g (coneOperator c.operator) -
      coneOperator c.operator) * coneOperator (c.representation a))
    rw [c.groupAction.cone_conjugateOperator]
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.2.2.2 g a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero

/-- The actual zero-endpoint fibre cycle is isomorphic to the genuine zero
cycle, by the unitary identification of the whole cone fibre. -/
def degenerateConeZeroFibreIso (c : OddKasparovCycle α β E) (hc : c.IsDegenerate) :
    OddKasparovCycleIso ((c.degenerateCone hc).fibre 0) (zeroOddKasparovCycle α β) where
  moduleEquiv := coneZeroFibreEquiv
  action_intertwine _ _ := Subsingleton.elim _ _
  representation_intertwine _ _ := Subsingleton.elim _ _
  operator_intertwine _ := Subsingleton.elim _ _

/-- Evaluation at one intertwines every part of the cycle data, giving the
actual original cycle as the target endpoint of the degenerate cone. -/
def degenerateConeOneFibreIso (c : OddKasparovCycle α β E) (hc : c.IsDegenerate) :
    OddKasparovCycleIso ((c.degenerateCone hc).fibre 1) c where
  moduleEquiv := coneOneFibreEquiv
  action_intertwine g z := by
    refine DenseRange.induction_on (hilbertModuleFibreMk_denseRange
      (X := unitInterval) (B := B) (M := ConeHilbertModule B E) (1 : unitInterval))
      z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_action_mk, coneOneFibreEquiv_mk, coneOneFibreEquiv_mk]
      rfl
  representation_intertwine a z := by
    refine DenseRange.induction_on (hilbertModuleFibreMk_denseRange
      (X := unitInterval) (B := B) (M := ConeHilbertModule B E) (1 : unitInterval))
      z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_representation_mk, coneOneFibreEquiv_mk, coneOneFibreEquiv_mk]
      rfl
  operator_intertwine z := by
    refine DenseRange.induction_on (hilbertModuleFibreMk_denseRange
      (X := unitInterval) (B := B) (M := ConeHilbertModule B E) (1 : unitInterval))
      z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_operator_mk, coneOneFibreEquiv_mk, coneOneFibreEquiv_mk]
      rfl

end OddKasparovCycle
end BC4lean.KKTheory
