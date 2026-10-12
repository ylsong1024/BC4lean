import BC4lean.GradedKasparovProductCriterion
import BC4lean.GradedKasparovCycleIso

/-! # Transport of an actual cycle to specified tensor data

An actual whole-module unitary intertwines the grading, action and source
representation with the canonical tensor data. Its transported operator has
all the genuine localized cycle defects. This is a transport lemma, not an
existence assumption for a product.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C E F M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
  (k : GradedKasparovCycle α γ δA δC M)
  (u : HilbertModuleEquiv C M (InteriorModuleTensor (E := E) d.representation))
  (hgrading : ∀ x, u (k.grading.grading x) = (gradedKasparovTensorGrading c d).grading (u x))
  (haction : ∀ g x, u (k.groupAction.action g x) =
    (gradedKasparovTensorAction c d).action g (u x))
  (hrepresentation : ∀ a x, u (k.representation a x) =
    gradedKasparovTensorRepresentation c d a (u x))

include hrepresentation in
theorem transportedCycle_tensorRepresentation (a : A) :
    u.transport (k.representation a) = gradedKasparovTensorRepresentation c d a := by
  ext y
  rw [HilbertModuleEquiv.transport_apply, hrepresentation, HilbertModuleEquiv.apply_symm_apply]

include haction in
theorem transportedCycle_tensorConjugateOperator (g : Γ) :
    u.transport (k.groupAction.conjugateOperator g k.operator) =
      (gradedKasparovTensorAction c d).conjugateOperator g (u.transport k.operator) := by
  have hsym (g : Γ) (y : InteriorModuleTensor (E := E) d.representation) :
      u.symm ((gradedKasparovTensorAction c d).action g y) =
        k.groupAction.action g (u.symm y) := by
    apply u.injective
    rw [HilbertModuleEquiv.apply_symm_apply, haction, HilbertModuleEquiv.apply_symm_apply]
  ext y
  simp only [HilbertModuleEquiv.transport_apply, EquivariantHilbertModule.conjugateMap_apply,
    hsym, haction]

include hgrading haction hrepresentation in
theorem transportedCycle_tensorConditions :
    GradedKasparovTensorOperatorConditions c d (u.transport k.operator) where
  operator_odd := by
    intro y
    have hsym : u.symm ((gradedKasparovTensorGrading c d).grading y) =
        k.grading.grading (u.symm y) := by
      apply u.injective
      rw [HilbertModuleEquiv.apply_symm_apply, hgrading, HilbertModuleEquiv.apply_symm_apply]
    simp only [HilbertModuleEquiv.transport_apply]
    rw [← hgrading, k.operator_odd, map_neg, hsym]
  selfadjoint_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.selfadjoint_mod_compact a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_star, transportedCycle_tensorRepresentation c d k u
        hrepresentation] using h
  square_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.square_mod_compact a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_one, transportedCycle_tensorRepresentation c d k u
        hrepresentation] using h
  commutator_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.commutator_compact a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      transportedCycle_tensorRepresentation c d k u hrepresentation] using h
  equivariance_mod_compact g a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.equivariance_mod_compact g a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      transportedCycle_tensorRepresentation c d k u hrepresentation,
      transportedCycle_tensorConjugateOperator c d k u haction] using h

def transportedCycle_tensorIso : GradedKasparovCycleIso k
    (gradedKasparovTensorCycleOfConditions c d (u.transport k.operator)
      (transportedCycle_tensorConditions c d k u hgrading haction hrepresentation)) where
  moduleEquiv := u
  grading_intertwine := hgrading
  action_intertwine := haction
  representation_intertwine := hrepresentation
  operator_intertwine x := by
    change u (k.operator x) = u.transport k.operator (u x)
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
