import BC4lean.OddIntervalKasparovConstant
import BC4lean.OddIntervalKasparovReversal
import BC4lean.OddIntervalKasparovCycleGluing
import Mathlib.Logic.Relation

/-! # The genuine full odd homotopy relation

For separable coefficient algebras, actual constant witnesses, reversal and
matched-pair concatenation prove that the existence of one arbitrary-module
full interval witness is an equivalence relation. Its generated relation is
proved equal to this single-witness relation. The odd quotient is taken by
the actual full witness relation, rather than merely declaring its closure.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace BundledOddKasparovCycle

def FullHomotopic (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) : Prop :=
  Nonempty (FullOddKasparovHomotopy c d)

def HomotopyStep (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) : Prop :=
  c.Isomorphic d ∨ c.FullHomotopic d

def Homotopic : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β →
    BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β → Prop := Relation.EqvGen HomotopyStep

theorem homotopyStep_iff_full {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β} :
    c.HomotopyStep d ↔ c.FullHomotopic d := by
  let _retainedOriginalSeparableB : TopologicalSpace.SeparableSpace B := inferInstance
  constructor
  · intro h
    change c.Isomorphic d ∨ c.FullHomotopic d at h
    rcases h with hIso | h
    · rcases (show Nonempty (c.Iso d) from hIso) with ⟨u⟩
      exact ⟨FullOddKasparovHomotopy.ofIso u⟩
    · exact h
  · exact Or.inr

/-- The actual arbitrary-module full witness relation is already an equivalence. -/
def fullHomotopySetoid : Setoid (BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) where
  r := FullHomotopic
  iseqv :=
    { refl c := ⟨FullOddKasparovHomotopy.refl c⟩
      symm h := by obtain ⟨h⟩ := h; exact ⟨h.symm⟩
      trans h k := by obtain ⟨h⟩ := h; obtain ⟨k⟩ := k; exact ⟨h.trans k⟩ }

/-- Every finite generated chain is represented by one actual full odd
interval witness. The proof constructs its reversal and joined module. -/
theorem homotopic_iff_full {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β} :
    c.Homotopic d ↔ c.FullHomotopic d := by
  constructor
  · intro h
    induction h with
    | rel c d h => exact homotopyStep_iff_full.mp h
    | refl c => exact ⟨FullOddKasparovHomotopy.refl c⟩
    | symm c d _ ih => obtain ⟨h⟩ := ih; exact ⟨h.symm⟩
    | trans c d k _ _ ih ih' => obtain ⟨h⟩ := ih; obtain ⟨h'⟩ := ih'; exact ⟨h.trans h'⟩
  · intro h
    exact Relation.EqvGen.rel _ _ (Or.inr h)

end BundledOddKasparovCycle

/-- Odd KK classes use the existence of an actual full arbitrary interval
witness. The relation is proved equivalent above, with explicit module universe. -/
abbrev OddKK (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :=
  Quotient (BundledOddKasparovCycle.fullHomotopySetoid
    (α := α) (β := β) : Setoid (BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β))

end BC4lean.KKTheory
