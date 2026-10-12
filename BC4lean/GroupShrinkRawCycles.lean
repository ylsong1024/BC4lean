import BC4lean.GroupShrinkHilbertModule
import BC4lean.GroupULiftRawCycles

/-! # Whole raw cycles on genuine small Hilbert modules

Each action, grading, representation and Fredholm operator is transported
by a whole Hilbert-module unitary. The existing unitary transport proofs
preserve all localized compact defects and the actual countable generation.
The smallness premise here is discharged from countable generation in the
bundled and full-interval constructions.
-/

noncomputable section
universe uΓ uA uB uE v
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] [Small.{v} E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

def shrink (c : OddKasparovCycle α β E) : OddKasparovCycle α β (Shrink.{v} E) :=
  c.unitaryTransport (hilbertModuleShrinkUp (B := B))

def shrinkIso (c : OddKasparovCycle α β E) : OddKasparovCycleIso c c.shrink :=
  c.unitaryTransportIso (hilbertModuleShrinkUp (B := B))

@[simp] theorem shrink_action (c : OddKasparovCycle α β E) (g : Γ)
    (x : Shrink.{v} E) :
    c.shrink.groupAction.action g x =
      equivShrink E (c.groupAction.action g ((equivShrink E).symm x)) := rfl

@[simp] theorem shrink_representation (c : OddKasparovCycle α β E) (a : A)
    (x : Shrink.{v} E) :
    c.shrink.representation a x =
      equivShrink E (c.representation a ((equivShrink E).symm x)) := rfl

@[simp] theorem shrink_operator (c : OddKasparovCycle α β E) (x : Shrink.{v} E) :
    c.shrink.operator x = equivShrink E (c.operator ((equivShrink E).symm x)) := rfl

end OddKasparovCycle

namespace KasparovCycle

def shrink (c : KasparovCycle α β E) : KasparovCycle α β (Shrink.{v} E) :=
  c.transport (hilbertModuleShrinkUp (B := B))

def shrinkIso (c : KasparovCycle α β E) : KasparovCycleIso c c.shrink :=
  c.transportIso (hilbertModuleShrinkUp (B := B))

end KasparovCycle

namespace GradedKasparovCycle
variable {δA : CStarGrading A} {δB : CStarGrading B}

def shrink (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle α β δA δB (Shrink.{v} E) :=
  c.unitaryTransport (hilbertModuleShrinkUp (B := B))

def shrinkIso (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycleIso c c.shrink :=
  c.unitaryTransportIso (hilbertModuleShrinkUp (B := B))

@[simp] theorem shrink_grading (c : GradedKasparovCycle α β δA δB E)
    (x : Shrink.{v} E) :
    c.shrink.grading.grading x =
      equivShrink E (c.grading.grading ((equivShrink E).symm x)) := rfl

@[simp] theorem shrink_action (c : GradedKasparovCycle α β δA δB E) (g : Γ)
    (x : Shrink.{v} E) :
    c.shrink.groupAction.action g x =
      equivShrink E (c.groupAction.action g ((equivShrink E).symm x)) := rfl

@[simp] theorem shrink_representation (c : GradedKasparovCycle α β δA δB E) (a : A)
    (x : Shrink.{v} E) :
    c.shrink.representation a x =
      equivShrink E (c.representation a ((equivShrink E).symm x)) := rfl

@[simp] theorem shrink_operator (c : GradedKasparovCycle α β δA δB E)
    (x : Shrink.{v} E) :
    c.shrink.operator x = equivShrink E (c.operator ((equivShrink E).symm x)) := rfl

end GradedKasparovCycle
end BC4lean.KKTheory
