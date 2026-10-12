import BC4lean.GradedKasparovLocalCompactPerturbation
import BC4lean.GradedKasparovCycleIso

/-! # Genuine operator transport onto fixed graded cycle data -/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}
  (k : GradedKasparovCycle α β δA δB E) (c : GradedKasparovCycle α β δA δB F)
  (u : HilbertModuleEquiv B E F)
  (hgrading : ∀ x, u (k.grading.grading x) = c.grading.grading (u x))
  (haction : ∀ g x, u (k.groupAction.action g x) = c.groupAction.action g (u x))
  (hrepresentation : ∀ a x, u (k.representation a x) = c.representation a (u x))

include hrepresentation in
theorem transportedCycle_fixedRepresentation (a : A) :
    u.transport (k.representation a) = c.representation a := by
  ext y
  rw [HilbertModuleEquiv.transport_apply, hrepresentation, HilbertModuleEquiv.apply_symm_apply]

include haction in
theorem transportedCycle_fixedConjugateOperator (g : Γ) :
    u.transport (k.groupAction.conjugateOperator g k.operator) =
      c.groupAction.conjugateOperator g (u.transport k.operator) := by
  have hsym (g : Γ) (y : F) : u.symm (c.groupAction.action g y) =
      k.groupAction.action g (u.symm y) := by
    apply u.injective
    rw [HilbertModuleEquiv.apply_symm_apply, haction, HilbertModuleEquiv.apply_symm_apply]
  ext y
  simp only [HilbertModuleEquiv.transport_apply, EquivariantHilbertModule.conjugateMap_apply,
    hsym, haction]

include hgrading haction hrepresentation in
theorem transportedCycle_fixedOperatorConditions : c.OperatorConditions (u.transport k.operator) where
  operator_odd := by
    intro y
    have hsym : u.symm (c.grading.grading y) = k.grading.grading (u.symm y) := by
      apply u.injective
      rw [HilbertModuleEquiv.apply_symm_apply, hgrading, HilbertModuleEquiv.apply_symm_apply]
    simp only [HilbertModuleEquiv.transport_apply]
    rw [← hgrading, k.operator_odd, map_neg, hsym]
  selfadjoint_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.selfadjoint_mod_compact a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_star, transportedCycle_fixedRepresentation k c u hrepresentation] using h
  square_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.square_mod_compact a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      HilbertModuleEquiv.transport_one, transportedCycle_fixedRepresentation k c u hrepresentation] using h
  commutator_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.commutator_compact a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      transportedCycle_fixedRepresentation k c u hrepresentation] using h
  equivariance_mod_compact g a := by
    have h := (u.transport_isModuleCompact_iff _).2 (k.equivariance_mod_compact g a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub,
      transportedCycle_fixedRepresentation k c u hrepresentation,
      transportedCycle_fixedConjugateOperator k c u haction] using h

def transportedCycle_fixedIso : GradedKasparovCycleIso k
    (c.withOperator (u.transport k.operator)
      (transportedCycle_fixedOperatorConditions k c u hgrading haction hrepresentation)) where
  moduleEquiv := u
  grading_intertwine := hgrading
  action_intertwine := haction
  representation_intertwine := hrepresentation
  operator_intertwine x := by
    change u (k.operator x) = u.transport k.operator (u x)
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
