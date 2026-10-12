import BC4lean.CliffordCycleIso
import BC4lean.BundledGradedKasparovCycle

/-! # Odd cycles with their actual complete Hilbert modules bundled -/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- An odd cycle stores its actual module structures in a fixed module universe. -/
structure BundledOddKasparovCycle (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) where
  carrier : Type uE
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℂ carrier]
  [opSMul : SMul Bᵐᵒᵖ carrier]
  [cstarModule : CStarModule Bᵐᵒᵖ carrier]
  [completeSpace : CompleteSpace carrier]
  cycle : OddKasparovCycle α β carrier

attribute [instance] BundledOddKasparovCycle.normedAddCommGroup
  BundledOddKasparovCycle.normedSpace BundledOddKasparovCycle.opSMul
  BundledOddKasparovCycle.cstarModule BundledOddKasparovCycle.completeSpace

namespace BundledOddKasparovCycle
variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

instance instCoeSort : CoeSort (BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) (Type uE) :=
  ⟨carrier⟩

def of {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : OddKasparovCycle α β E) : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β where
  carrier := E
  cycle := c

abbrev Iso (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :=
  OddKasparovCycleIso c.cycle d.cycle

def isoRefl (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) : c.Iso c :=
  OddKasparovCycleIso.refl c.cycle

def Isomorphic (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) : Prop := Nonempty (c.Iso d)

def isoSetoid : Setoid (BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) where
  r := Isomorphic
  iseqv :=
    { refl c := ⟨isoRefl c⟩
      symm h := by obtain ⟨u⟩ := h; exact ⟨u.symm⟩
      trans h k := by obtain ⟨u⟩ := h; obtain ⟨v⟩ := k; exact ⟨u.trans v⟩ }

/-- Bundle the genuine product-coefficient expansion of an odd cycle. -/
def cliffordExpansion (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading :=
  BundledGradedKasparovCycle.of c.cycle.cliffordExpansion

end BundledOddKasparovCycle

/-- Bundle the actual first-range extraction of a genuinely graded cycle. -/
def BundledGradedKasparovCycle.cliffordExtraction
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :
    BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β :=
  BundledOddKasparovCycle.of (cliffordExtractOddCycle true c.cycle)

end BC4lean.KKTheory
