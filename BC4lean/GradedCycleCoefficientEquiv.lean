import BC4lean.GradedCycleCoefficientTransport
import BC4lean.HilbertModuleCoefficientEquiv
import BC4lean.BundledGradedKasparovCycle

/-! # Invertible transport of entire graded cycles

The coefficient equivalence includes its actual grading and action
compatibilities. Transported cycle isomorphisms and the inverse-change
isomorphism intertwine all four pieces of whole-cycle data.
-/

noncomputable section
universe uΓ uA uB uC uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A coefficient star equivalence respecting the actual action and grading. -/
structure GradedCoefficientEquiv (β : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (η : CStarAlgebraAction Γ C) (δC : CStarGrading C) where
  starAlgEquiv : B ≃⋆ₐ[ℂ] C
  action_intertwine : ∀ g b, starAlgEquiv (β.automorphism g b) = η.automorphism g (starAlgEquiv b)
  grading_intertwine : ∀ b, starAlgEquiv (δB.automorphism b) = δC.automorphism (starAlgEquiv b)

namespace GradedCoefficientEquiv
variable {β : CStarAlgebraAction Γ B} {η : CStarAlgebraAction Γ C}
  {δB : CStarGrading B} {δC : CStarGrading C}

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
@[ext] theorem ext {e f : GradedCoefficientEquiv β δB η δC}
    (h : e.starAlgEquiv = f.starAlgEquiv) : e = f := by
  cases e
  cases f
  cases h
  rfl

def symm (e : GradedCoefficientEquiv β δB η δC) : GradedCoefficientEquiv η δC β δB where
  starAlgEquiv := e.starAlgEquiv.symm
  action_intertwine g c := by
    apply e.starAlgEquiv.injective
    change e.starAlgEquiv (e.starAlgEquiv.symm (η.automorphism g c)) =
      e.starAlgEquiv (β.automorphism g (e.starAlgEquiv.symm c))
    rw [e.starAlgEquiv.apply_symm_apply, e.action_intertwine, e.starAlgEquiv.apply_symm_apply]
  grading_intertwine c := by
    apply e.starAlgEquiv.injective
    change e.starAlgEquiv (e.starAlgEquiv.symm (δC.automorphism c)) =
      e.starAlgEquiv (δB.automorphism (e.starAlgEquiv.symm c))
    rw [e.starAlgEquiv.apply_symm_apply, e.grading_intertwine, e.starAlgEquiv.apply_symm_apply]

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem symm_starAlgEquiv (e : GradedCoefficientEquiv β δB η δC) :
    e.symm.starAlgEquiv = e.starAlgEquiv.symm := rfl

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem symm_symm (e : GradedCoefficientEquiv β δB η δC) : e.symm.symm = e := by
  apply ext
  exact e.starAlgEquiv.symm_symm

end GradedCoefficientEquiv

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {η : CStarAlgebraAction Γ C} {δA : CStarGrading A}
  {δB : CStarGrading B} {δC : CStarGrading C}

section RawCycles
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

def GradedKasparovCycle.changeCoefficients (c : GradedKasparovCycle α β δA δB E)
    (e : GradedCoefficientEquiv β δB η δC) :
    GradedKasparovCycle α η δA δC (CoefficientChangedModule e.starAlgEquiv E) :=
  c.coefficientChanged e.starAlgEquiv η δC e.action_intertwine e.grading_intertwine

def GradedKasparovCycleIso.changeCoefficients
    {c : GradedKasparovCycle α β δA δB E} {d : GradedKasparovCycle α β δA δB F}
    (u : GradedKasparovCycleIso c d) (e : GradedCoefficientEquiv β δB η δC) :
    GradedKasparovCycleIso (c.changeCoefficients e) (d.changeCoefficients e) where
  moduleEquiv := u.moduleEquiv.coefficientChanged e.starAlgEquiv
  grading_intertwine := u.grading_intertwine
  action_intertwine := u.action_intertwine
  representation_intertwine := u.representation_intertwine
  operator_intertwine := u.operator_intertwine

/-- Changing coefficients in both directions restores the whole raw cycle
through the explicitly constructed inverse-change module unitary. -/
def GradedKasparovCycle.changeCoefficientsInverseIso
    (c : GradedKasparovCycle α β δA δB E) (e : GradedCoefficientEquiv β δB η δC) :
    GradedKasparovCycleIso ((c.changeCoefficients e).changeCoefficients e.symm) c where
  moduleEquiv := coefficientChangedInverseEquiv e.starAlgEquiv
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end RawCycles

def BundledGradedKasparovCycle.changeCoefficients
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (e : GradedCoefficientEquiv β δB η δC) :
    BundledGradedKasparovCycle.{uΓ, uA, uC, uE} α η δA δC :=
  BundledGradedKasparovCycle.of (c.cycle.changeCoefficients e)

end BC4lean.KKTheory
