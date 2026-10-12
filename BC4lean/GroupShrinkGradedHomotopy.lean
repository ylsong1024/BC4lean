import BC4lean.GroupShrinkOddHomotopy
import BC4lean.GradedKasparovSourcePullbackClass

/-! # Genuine graded shrinking preserves full arbitrary interval witnesses

Both algebra gradings may be nontrivial. The completed fibre unitary
preserves the entire coefficient form and intertwines the transported
semilinear grading, action, representation and operator. Countable
generation over separable coefficients supplies small models for the
actual endpoint and interval modules. Thus the shrink map descends through
the relation given by a single genuine full graded interval witness.
-/

noncomputable section
universe uΓ uA uB uE v uM uX
namespace BC4lean.KKTheory

section Fibre
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {X : Type uX} {M : Type uM}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M] [Small.{v} M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

def GradedKasparovCycle.shrinkFibreIso
    (c : GradedKasparovCycle α (β.continuousSections (X := X)) δA δB.continuousSections M)
    (t : X) : GradedKasparovCycleIso
      ((c.shrink : GradedKasparovCycle α (β.continuousSections (X := X))
        δA δB.continuousSections (Shrink.{v} M)).fibre t) (c.fibre t) where
  moduleEquiv := hilbertModuleShrinkFibreDown t
  grading_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := Shrink.{v} M) t z
    rw [GradedKasparovCycle.fibre_grading_mk, hilbertModuleShrinkFibreDown_mk,
      hilbertModuleShrinkFibreDown_mk]
    simp only [GradedKasparovCycle.shrink_grading, Equiv.symm_apply_apply,
      GradedKasparovCycle.fibre_grading_mk]
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := Shrink.{v} M) t z
    rw [GradedKasparovCycle.fibre_action_mk, hilbertModuleShrinkFibreDown_mk,
      hilbertModuleShrinkFibreDown_mk]
    simp only [GradedKasparovCycle.shrink_action, Equiv.symm_apply_apply,
      GradedKasparovCycle.fibre_action_mk]
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := Shrink.{v} M) t z
    rw [GradedKasparovCycle.fibre_representation_mk, hilbertModuleShrinkFibreDown_mk,
      hilbertModuleShrinkFibreDown_mk]
    simp only [GradedKasparovCycle.shrink_representation, Equiv.symm_apply_apply,
      GradedKasparovCycle.fibre_representation_mk]
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := Shrink.{v} M) t z
    rw [GradedKasparovCycle.fibre_operator_mk, hilbertModuleShrinkFibreDown_mk,
      hilbertModuleShrinkFibreDown_mk]
    simp only [GradedKasparovCycle.shrink_operator, Equiv.symm_apply_apply,
      GradedKasparovCycle.fibre_operator_mk]

end Fibre

section Bundled
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

def BundledGradedKasparovCycle.shrink
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    BundledGradedKasparovCycle.{uΓ, uA, uB, v} α β δA δB := by
  letI : Small.{v} c.carrier := c.cycle.countablyGenerated.small
  exact BundledGradedKasparovCycle.of
    (c.cycle.shrink : GradedKasparovCycle α β δA δB (Shrink.{v} c.carrier))

def BundledGradedKasparovCycle.shrinkIso
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    GradedKasparovCycleIso c.cycle
      (c.shrink : BundledGradedKasparovCycle.{uΓ, uA, uB, v} α β δA δB).cycle := by
  letI : Small.{v} c.carrier := c.cycle.countablyGenerated.small
  exact c.cycle.shrinkIso

def FullGradedKasparovHomotopy.shrink
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) : FullGradedKasparovHomotopy
      (c.shrink : BundledGradedKasparovCycle.{uΓ, uA, uB, v} α β δA δB) d.shrink := by
  letI : Small.{v} h.intervalCycle.carrier := h.intervalCycle.cycle.countablyGenerated.small
  exact
    { intervalCycle := h.intervalCycle.shrink
      sourceIso := (h.intervalCycle.cycle.shrinkFibreIso 0).trans
        (h.sourceIso.trans c.shrinkIso)
      targetIso := (h.intervalCycle.cycle.shrinkFibreIso 1).trans
        (h.targetIso.trans d.shrinkIso) }

namespace GradedKasparovHomotopyClass

def shrink : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB →
    GradedKasparovHomotopyClass.{uΓ, uA, uB, v} α β δA δB :=
  Quotient.lift (fun c => mk
    (c.shrink : BundledGradedKasparovCycle.{uΓ, uA, uB, v} α β δA δB)) (by
      intro c d h
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.shrink⟩)

@[simp] theorem shrink_mk
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    shrink (mk c) = mk
      (c.shrink : BundledGradedKasparovCycle.{uΓ, uA, uB, v} α β δA δB) := rfl

end GradedKasparovHomotopyClass
end Bundled
end BC4lean.KKTheory
