import BC4lean.FullGradedKasparovHomotopy
import BC4lean.GradedKasparovDirectSum

/-! # Genuine graded-equivariant source pullback

An actual nonunital star homomorphism respecting source grading and group
action precomposes the representation. Every localized cycle defect is the
original defect at the image of that source element. The whole Hilbert
module, its genuine semilinear grading, group action and operator are kept.
Whole-cycle isomorphisms, evaluated fibres, single full witnesses and actual
direct sums are transported by their concrete unchanged-vector unitaries.
-/

noncomputable section
universe uΓ uA uA' uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}
  (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A')
  (hα' : α'.PreservesGrading δA') (f : A' →⋆ₙₐ[ℂ] A)
  (hact : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
  (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))

section Raw

variable {E F : Type uE}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

def GradedKasparovCycle.sourcePullback (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle α' β δA' δB E where
  sourceAction_preservesGrading := hα'
  coefficientAction_preservesGrading := c.coefficientAction_preservesGrading
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := c.groupAction
  grading_preserved := c.grading_preserved
  representation := c.representation.comp f
  representation_graded a x := by
    change c.grading.grading (c.representation (f a) x) =
      c.representation (f (δA'.automorphism a)) (c.grading.grading x)
    rw [hgrade]
    exact c.representation_graded (f a) x
  representation_equivariant g a := by
    change c.groupAction.conjugateOperator g (c.representation (f a)) =
      c.representation (f (α'.automorphism g a))
    rw [hact]
    exact c.representation_equivariant g (f a)
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact a := c.selfadjoint_mod_compact (f a)
  square_mod_compact a := c.square_mod_compact (f a)
  commutator_compact a := by
    change IsModuleCompact (c.operator * c.representation (f a) -
      c.representation (f (δA'.automorphism a)) * c.operator)
    rw [hgrade]
    exact c.commutator_compact (f a)
  equivariance_mod_compact g a := c.equivariance_mod_compact g (f a)

@[simp] theorem GradedKasparovCycle.sourcePullback_representation
    (c : GradedKasparovCycle α β δA δB E) (a : A') :
    (c.sourcePullback α' δA' hα' f hact hgrade).representation a = c.representation (f a) := rfl

def GradedKasparovCycleIso.sourcePullback
    {c : GradedKasparovCycle α β δA δB E} {d : GradedKasparovCycle α β δA δB F}
    (e : GradedKasparovCycleIso c d) :
    GradedKasparovCycleIso (c.sourcePullback α' δA' hα' f hact hgrade)
      (d.sourcePullback α' δA' hα' f hact hgrade) where
  moduleEquiv := e.moduleEquiv
  grading_intertwine := e.grading_intertwine
  action_intertwine := e.action_intertwine
  representation_intertwine a := e.representation_intertwine (f a)
  operator_intertwine := e.operator_intertwine

def GradedKasparovCycle.sourcePullbackDirectSumIso
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle α β δA δB F) :
    GradedKasparovCycleIso ((c.directSum d).sourcePullback α' δA' hα' f hact hgrade)
      ((c.sourcePullback α' δA' hα' f hact hgrade).directSum
        (d.sourcePullback α' δA' hα' f hact hgrade)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Raw

section Fibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

def GradedKasparovCycle.sourcePullbackFibreIso
    (c : GradedKasparovCycle α (β.continuousSections (X := X)) δA δB.continuousSections M)
    (t : X) : GradedKasparovCycleIso
      ((c.sourcePullback α' δA' hα' f hact hgrade).fibre t)
      ((c.fibre t).sourcePullback α' δA' hα' f hact hgrade) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Fibre

def BundledGradedKasparovCycle.sourcePullback
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    BundledGradedKasparovCycle.{uΓ,uA',uB,uE} α' β δA' δB :=
  .of (c.cycle.sourcePullback α' δA' hα' f hact hgrade)

def FullGradedKasparovHomotopy.sourcePullback
    {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) :
    FullGradedKasparovHomotopy (c.sourcePullback α' δA' hα' f hact hgrade)
      (d.sourcePullback α' δA' hα' f hact hgrade) where
  intervalCycle := h.intervalCycle.sourcePullback α' δA' hα' f hact hgrade
  sourceIso := (h.intervalCycle.cycle.sourcePullbackFibreIso α' δA' hα' f hact hgrade 0).trans
    (h.sourceIso.sourcePullback α' δA' hα' f hact hgrade)
  targetIso := (h.intervalCycle.cycle.sourcePullbackFibreIso α' δA' hα' f hact hgrade 1).trans
    (h.targetIso.sourcePullback α' δA' hα' f hact hgrade)

section Evaluation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

local instance gradedSourcePullbackEvaluationSpectralOrder : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance gradedSourcePullbackEvaluationSpectralStarOrderedRing : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The actual nonunital evaluation homomorphism, with no unit assumption. -/
def gradedSourceEvaluation (t : X) : C(X, A) →⋆ₙₐ[ℂ] A where
  toFun a := a t
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [CompactSpace X] in
@[simp] theorem gradedSourceEvaluation_apply (t : X) (a : C(X, A)) :
    gradedSourceEvaluation t a = a t := rfl

theorem gradedSourceEvaluation_action (t : X) (g : Γ) (a : C(X, A)) :
    gradedSourceEvaluation t ((α.continuousSections (X := X)).automorphism g a) =
      α.automorphism g (gradedSourceEvaluation t a) := rfl

theorem gradedSourceEvaluation_grading (t : X) (a : C(X, A)) :
    gradedSourceEvaluation t (δA.continuousSections.automorphism a) =
      δA.automorphism (gradedSourceEvaluation t a) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def GradedKasparovCycle.sourceEvaluationPullback (c : GradedKasparovCycle α β δA δB E) (t : X) :
    GradedKasparovCycle (α.continuousSections (X := X)) β δA.continuousSections δB E :=
  c.sourcePullback α.continuousSections δA.continuousSections
    (CStarAlgebraAction.preservesGrading_continuousSections c.sourceAction_preservesGrading)
    (gradedSourceEvaluation t) (gradedSourceEvaluation_action t) (gradedSourceEvaluation_grading t)

end Evaluation
end BC4lean.KKTheory
