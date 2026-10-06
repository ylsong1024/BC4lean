import BC4lean.GradedKasparovCycle
import BC4lean.HilbertModuleEquiv

/-! # Isomorphisms of genuinely graded Kasparov cycles

An isomorphism may connect cycles on different Hilbert-module types. Its
inner-product-preserving complex-linear isometry equivalence intertwines the
module grading, group action, representation and Fredholm operator exactly.
The inverse and composition retain all four intertwining laws. Both algebra gradings may be nontrivial. This file
concerns cycle data; no quotient or KK group is constructed here.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E F G : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- A genuine isomorphism of raw Kasparov cycles, including cycles carried by
different right Hilbert modules. Every part of the cycle data is intertwined
by the same inner-product-preserving linear isometry equivalence. -/
structure GradedKasparovCycleIso (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle α β δA δB F) where
  moduleEquiv : HilbertModuleEquiv B E F
  grading_intertwine : ∀ x,
    moduleEquiv (c.grading.grading x) = d.grading.grading (moduleEquiv x)
  action_intertwine : ∀ g x,
    moduleEquiv (c.groupAction.action g x) = d.groupAction.action g (moduleEquiv x)
  representation_intertwine : ∀ a x,
    moduleEquiv (c.representation a x) = d.representation a (moduleEquiv x)
  operator_intertwine : ∀ x,
    moduleEquiv (c.operator x) = d.operator (moduleEquiv x)

namespace GradedKasparovCycleIso

variable {c : GradedKasparovCycle α β δA δB E} {d : GradedKasparovCycle α β δA δB F}
  {k : GradedKasparovCycle α β δA δB G}

instance instCoeFun : CoeFun (GradedKasparovCycleIso c d) (fun _ => E → F) :=
  ⟨fun e => e.moduleEquiv⟩

/-- The underlying Hilbert-module equivalence determines a cycle isomorphism. -/
@[ext] theorem ext {e f : GradedKasparovCycleIso c d}
    (h : e.moduleEquiv = f.moduleEquiv) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- The identity equivalence intertwines every part of a raw cycle. -/
def refl (c : GradedKasparovCycle α β δA δB E) : GradedKasparovCycleIso c c where
  moduleEquiv := HilbertModuleEquiv.refl (B := B) (E := E)
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

@[simp] theorem refl_apply (c : GradedKasparovCycle α β δA δB E) (x : E) : refl c x = x := rfl

/-- Inverting a cycle isomorphism reverses every exact intertwining law. -/
def symm (e : GradedKasparovCycleIso c d) : GradedKasparovCycleIso d c where
  moduleEquiv := e.moduleEquiv.symm
  grading_intertwine y := by
    apply e.moduleEquiv.injective
    simpa only [HilbertModuleEquiv.apply_symm_apply] using
      (e.grading_intertwine (e.moduleEquiv.symm y)).symm
  action_intertwine g y := by
    apply e.moduleEquiv.injective
    simpa only [HilbertModuleEquiv.apply_symm_apply] using
      (e.action_intertwine g (e.moduleEquiv.symm y)).symm
  representation_intertwine a y := by
    apply e.moduleEquiv.injective
    simpa only [HilbertModuleEquiv.apply_symm_apply] using
      (e.representation_intertwine a (e.moduleEquiv.symm y)).symm
  operator_intertwine y := by
    apply e.moduleEquiv.injective
    simpa only [HilbertModuleEquiv.apply_symm_apply] using
      (e.operator_intertwine (e.moduleEquiv.symm y)).symm

@[simp] theorem symm_moduleEquiv (e : GradedKasparovCycleIso c d) :
    e.symm.moduleEquiv = e.moduleEquiv.symm := rfl

@[simp] theorem apply_symm_apply (e : GradedKasparovCycleIso c d) (y : F) :
    e (e.symm y) = y := e.moduleEquiv.apply_symm_apply y

@[simp] theorem symm_apply_apply (e : GradedKasparovCycleIso c d) (x : E) :
    e.symm (e x) = x := e.moduleEquiv.symm_apply_apply x

@[simp] theorem symm_symm (e : GradedKasparovCycleIso c d) : e.symm.symm = e :=
  ext (HilbertModuleEquiv.symm_symm e.moduleEquiv)

/-- Composition through an intermediate module intertwines the entire cycle. -/
def trans (e : GradedKasparovCycleIso c d) (f : GradedKasparovCycleIso d k) :
    GradedKasparovCycleIso c k where
  moduleEquiv := e.moduleEquiv.trans f.moduleEquiv
  grading_intertwine x := by
    simp only [HilbertModuleEquiv.trans_apply]
    rw [e.grading_intertwine, f.grading_intertwine]
  action_intertwine g x := by
    simp only [HilbertModuleEquiv.trans_apply]
    rw [e.action_intertwine, f.action_intertwine]
  representation_intertwine a x := by
    simp only [HilbertModuleEquiv.trans_apply]
    rw [e.representation_intertwine, f.representation_intertwine]
  operator_intertwine x := by
    simp only [HilbertModuleEquiv.trans_apply]
    rw [e.operator_intertwine, f.operator_intertwine]

@[simp] theorem trans_moduleEquiv (e : GradedKasparovCycleIso c d) (f : GradedKasparovCycleIso d k) :
    (e.trans f).moduleEquiv = e.moduleEquiv.trans f.moduleEquiv := rfl

@[simp] theorem trans_apply (e : GradedKasparovCycleIso c d) (f : GradedKasparovCycleIso d k) (x : E) :
    e.trans f x = f (e x) := HilbertModuleEquiv.trans_apply _ _ _

@[simp] theorem refl_trans (e : GradedKasparovCycleIso c d) : (refl c).trans e = e := by
  apply ext
  apply HilbertModuleEquiv.ext
  intro x
  rfl

@[simp] theorem trans_refl (e : GradedKasparovCycleIso c d) : e.trans (refl d) = e := by
  apply ext
  apply HilbertModuleEquiv.ext
  intro x
  rfl

@[simp] theorem trans_symm (e : GradedKasparovCycleIso c d) : e.trans e.symm = refl c := by
  apply ext
  apply HilbertModuleEquiv.ext
  intro x
  exact e.moduleEquiv.symm_apply_apply x

@[simp] theorem symm_trans (e : GradedKasparovCycleIso c d) : e.symm.trans e = refl d := by
  apply ext
  apply HilbertModuleEquiv.ext
  intro y
  exact e.moduleEquiv.apply_symm_apply y

/-- Conjugating the source operator by the isomorphism gives the target operator. -/
theorem transport_operator (e : GradedKasparovCycleIso c d) :
    e.moduleEquiv.transport c.operator = d.operator := by
  apply AdjointableMap.ext
  intro y
  rw [HilbertModuleEquiv.transport_apply]
  calc
    e.moduleEquiv (c.operator (e.moduleEquiv.symm y)) =
        d.operator (e.moduleEquiv (e.moduleEquiv.symm y)) :=
      e.operator_intertwine (e.moduleEquiv.symm y)
    _ = d.operator y := by rw [HilbertModuleEquiv.apply_symm_apply]

/-- Conjugation by the isomorphism transports each represented source-algebra element. -/
theorem transport_representation (e : GradedKasparovCycleIso c d) (a : A) :
    e.moduleEquiv.transport (c.representation a) = d.representation a := by
  apply AdjointableMap.ext
  intro y
  rw [HilbertModuleEquiv.transport_apply]
  calc
    e.moduleEquiv (c.representation a (e.moduleEquiv.symm y)) =
        d.representation a (e.moduleEquiv (e.moduleEquiv.symm y)) :=
      e.representation_intertwine a (e.moduleEquiv.symm y)
    _ = d.representation a y := by rw [HilbertModuleEquiv.apply_symm_apply]

end GradedKasparovCycleIso
end BC4lean.KKTheory
