import BC4lean.GroupULiftFibre
import BC4lean.GradedKasparovSourcePullbackClass

/-! # Genuine graded universe lifts preserve full interval witnesses

The whole Hilbert-module ULift unitary preserves the entire coefficient form.
Its completed fibre comparison intertwines the actual nontrivial semilinear
grading, group action, representation and Fredholm operator. Lifting the
arbitrary interval module therefore supplies a genuine full witness between
the lifted endpoint cycles. The resulting map on full graded classes raises
only the module universe, and commutes with actual source pullback.
-/

noncomputable section
universe uΓ uA uB uE v uF uM uX uA'
namespace BC4lean.KKTheory

section Raw
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovCycle

@[simp] theorem ulift_grading (c : GradedKasparovCycle α β δA δB E)
    (x : ULift.{v} E) :
    c.ulift.grading.grading x = ULift.up (c.grading.grading x.down) := rfl

@[simp] theorem ulift_action (c : GradedKasparovCycle α β δA δB E)
    (g : Γ) (x : ULift.{v} E) :
    c.ulift.groupAction.action g x = ULift.up (c.groupAction.action g x.down) := rfl

@[simp] theorem ulift_representation (c : GradedKasparovCycle α β δA δB E)
    (a : A) (x : ULift.{v} E) :
    c.ulift.representation a x = ULift.up (c.representation a x.down) := rfl

@[simp] theorem ulift_operator (c : GradedKasparovCycle α β δA δB E)
    (x : ULift.{v} E) :
    c.ulift.operator x = ULift.up (c.operator x.down) := rfl

end GradedKasparovCycle

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

def GradedKasparovCycleIso.ulift
    {c : GradedKasparovCycle α β δA δB E}
    {d : GradedKasparovCycle α β δA δB F} (e : GradedKasparovCycleIso c d) :
    GradedKasparovCycleIso
      (c.ulift : GradedKasparovCycle α β δA δB (ULift.{v} E)) d.ulift :=
  c.uliftIso.symm.trans (e.trans d.uliftIso)

end Raw

section Fibre
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {X : Type uX} {M : Type uM}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- The true completed fibre of the lifted arbitrary interval module is
unitarily the lift of its completed fibre, with every cycle datum retained. -/
def GradedKasparovCycle.uliftFibreIso
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA δB.continuousSections M) (t : X) :
    GradedKasparovCycleIso
      ((c.ulift : GradedKasparovCycle α (β.continuousSections (X := X))
        δA δB.continuousSections (ULift.{v} M)).fibre t)
      ((c.fibre t).ulift : GradedKasparovCycle α β δA δB
        (ULift.{v} (HilbertModuleFibre B M t))) where
  moduleEquiv := hilbertModuleULiftFibreEquiv t
  grading_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := ULift.{v} M) t z
    rw [GradedKasparovCycle.fibre_grading_mk, hilbertModuleULiftFibreEquiv_mk,
      hilbertModuleULiftFibreEquiv_mk]
    simp only [GradedKasparovCycle.ulift_grading, ULift.down_up,
      GradedKasparovCycle.fibre_grading_mk]
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := ULift.{v} M) t z
    rw [GradedKasparovCycle.fibre_action_mk, hilbertModuleULiftFibreEquiv_mk,
      hilbertModuleULiftFibreEquiv_mk]
    simp only [GradedKasparovCycle.ulift_action, ULift.down_up,
      GradedKasparovCycle.fibre_action_mk]
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := ULift.{v} M) t z
    rw [GradedKasparovCycle.fibre_representation_mk, hilbertModuleULiftFibreEquiv_mk,
      hilbertModuleULiftFibreEquiv_mk]
    simp only [GradedKasparovCycle.ulift_representation, ULift.down_up,
      GradedKasparovCycle.fibre_representation_mk]
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := ULift.{v} M) t z
    rw [GradedKasparovCycle.fibre_operator_mk, hilbertModuleULiftFibreEquiv_mk,
      hilbertModuleULiftFibreEquiv_mk]
    simp only [GradedKasparovCycle.ulift_operator, ULift.down_up,
      GradedKasparovCycle.fibre_operator_mk]

end Fibre

section Bundled
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace BundledGradedKasparovCycle

/-- Lift the actual carrier and all genuine graded cycle data. -/
def ulift (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    BundledGradedKasparovCycle.{uΓ, uA, uB, max uE v} α β δA δB :=
  of (c.cycle.ulift : GradedKasparovCycle α β δA δB (ULift.{v} c.carrier))

@[simp] theorem ulift_carrier
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    (c.ulift : BundledGradedKasparovCycle.{uΓ, uA, uB, max uE v} α β δA δB).carrier =
      ULift.{v} c.carrier := rfl

end BundledGradedKasparovCycle

/-- Lift the arbitrary full interval witness and its actual completed
endpoint fibres, using whole graded cycle unitaries at both endpoints. -/
def FullGradedKasparovHomotopy.ulift
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) : FullGradedKasparovHomotopy
      (c.ulift : BundledGradedKasparovCycle.{uΓ, uA, uB, max uE v} α β δA δB)
      d.ulift where
  intervalCycle := h.intervalCycle.ulift
  sourceIso := (h.intervalCycle.cycle.uliftFibreIso 0).trans h.sourceIso.ulift
  targetIso := (h.intervalCycle.cycle.uliftFibreIso 1).trans h.targetIso.ulift

namespace GradedKasparovHomotopyClass
variable [TopologicalSpace.SeparableSpace B]

/-- Universe lift on the quotient by one genuine full graded interval witness. -/
def ulift : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB →
    GradedKasparovHomotopyClass.{uΓ, uA, uB, max uE v} α β δA δB :=
  Quotient.lift (fun c => mk
    (c.ulift : BundledGradedKasparovCycle.{uΓ, uA, uB, max uE v} α β δA δB)) (by
      intro c d h
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.ulift⟩)

@[simp] theorem ulift_mk
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    ulift (mk c) = mk
      (c.ulift : BundledGradedKasparovCycle.{uΓ, uA, uB, max uE v} α β δA δB) := rfl

/-- An additional lift within the existing common module universe is
identified by the actual whole-cycle ULift unitary. -/
theorem ulift_eq_self
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, max uE v} α β δA δB) :
    ulift.{uΓ, uA, uB, max uE v, v} x = x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact mk_eq_of_iso (c.cycle.uliftIso : GradedKasparovCycleIso c.cycle
    (c.ulift : BundledGradedKasparovCycle.{uΓ, uA, uB, max uE v} α β δA δB).cycle).symm

end GradedKasparovHomotopyClass
end Bundled

section SourcePullbackRaw
variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {B : Type uB} {E : Type uE}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}
  (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A')
  (hα' : α'.PreservesGrading δA') (f : A' →⋆ₙₐ[ℂ] A)
  (hact : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
  (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))

/-- Source pullback and carrier lift commute through their actual unchanged
lifted-vector unitary, preserving every whole cycle datum. -/
def GradedKasparovCycle.uliftSourcePullbackIso
    (c : GradedKasparovCycle α β δA δB E) : GradedKasparovCycleIso
      ((c.sourcePullback α' δA' hα' f hact hgrade).ulift :
        GradedKasparovCycle α' β δA' δB (ULift.{v} E))
      ((c.ulift : GradedKasparovCycle α β δA δB (ULift.{v} E)).sourcePullback
        α' δA' hα' f hact hgrade) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end SourcePullbackRaw

section SourcePullbackClass
variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}
  (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A')
  (hα' : α'.PreservesGrading δA') (f : A' →⋆ₙₐ[ℂ] A)
  (hact : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
  (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))

/-- The actual graded quotient lift commutes with genuine source pullback. -/
theorem GradedKasparovHomotopyClass.ulift_sourcePullback
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    GradedKasparovHomotopyClass.ulift.{uΓ, uA', uB, uE, v}
      (GradedKasparovHomotopyClass.sourcePullback α' δA' hα' f hact hgrade x) =
    GradedKasparovHomotopyClass.sourcePullback α' δA' hα' f hact hgrade
      (GradedKasparovHomotopyClass.ulift.{uΓ, uA, uB, uE, v} x) := by
  refine Quotient.inductionOn x ?_
  intro c
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    (c.cycle.uliftSourcePullbackIso α' δA' hα' f hact hgrade)

end SourcePullbackClass
end BC4lean.KKTheory
