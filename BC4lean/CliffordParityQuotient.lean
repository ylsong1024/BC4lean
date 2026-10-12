import BC4lean.OddKasparovHomotopyRelation

/-! # Clifford parity on the genuine full homotopy quotients

The Clifford relation is the existence of one actual full graded interval
witness. Extraction and expansion, with their proved inverse cycle unitaries,
transfer the actual reflexivity, reversal and gluing of odd full witnesses.
The quotient equivalence therefore respects arbitrary varying-module full
homotopies in both directions. Additive group laws are a separate construction.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace FullGradedKasparovHomotopy

/-- A Clifford cycle isomorphism gives one actual full witness by odd
extraction, a constant interval cycle, and genuine reconstruction unitaries. -/
def cliffordOfIso
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading} (u : c.Iso d) :
    FullGradedKasparovHomotopy c d := by
  let h : FullOddKasparovHomotopy c.cliffordExtraction d.cliffordExtraction :=
    FullOddKasparovHomotopy.ofIso (c := c.cliffordExtraction) (d := d.cliffordExtraction)
      (u.cliffordExtraction true)
  exact h.cliffordExpansion.changeEndpoints (e := c) (f := d)
    c.cycle.cliffordReconstructionIso.symm d.cycle.cliffordReconstructionIso.symm

end FullGradedKasparovHomotopy

namespace BundledGradedKasparovCycle

def CliffordFullHomotopic
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) : Prop :=
  Nonempty (FullGradedKasparovHomotopy c d)

/-- The actual single full Clifford witness relation is an equivalence,
by extracting and expanding the actual odd reflexive/reversed/joined witness. -/
def cliffordFullHomotopySetoid :
    Setoid (BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) where
  r := CliffordFullHomotopic
  iseqv :=
    { refl c := ⟨FullGradedKasparovHomotopy.cliffordOfIso (isoRefl c)⟩
      symm h := by
        obtain ⟨h⟩ := h
        exact (fullCliffordHomotopy_iff_extraction _ _).mpr ⟨h.cliffordExtraction.symm⟩
      trans h k := by
        obtain ⟨h⟩ := h
        obtain ⟨k⟩ := k
        exact (fullCliffordHomotopy_iff_extraction _ _).mpr
          ⟨h.cliffordExtraction.trans k.cliffordExtraction⟩ }

end BundledGradedKasparovCycle

/-- The degree-one Clifford model uses genuine graded cycles and actual full
interval homotopies, with a trivial source grading and swap coefficient grading. -/
abbrev CliffordKK (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :=
  Quotient (BundledGradedKasparovCycle.cliffordFullHomotopySetoid
    (α := α) (β := β) :
      Setoid (BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
        CStarGrading.trivial cliffordCoefficientGrading))

/-- Actual odd/Clifford parity on the full arbitrary-module homotopy quotients.
The plus range is fixed by ε=(1,-1), including the required sign convention. -/
def cliffordParityEquiv : OddKK.{uΓ, uA, uB, uE} α β ≃ CliffordKK.{uΓ, uA, uB, uE} α β where
  toFun := Quotient.map BundledOddKasparovCycle.cliffordExpansion (by
    intro c d h
    obtain ⟨h⟩ := h
    exact ⟨h.cliffordExpansion⟩)
  invFun := Quotient.map BundledGradedKasparovCycle.cliffordExtraction (by
    intro c d h
    obtain ⟨h⟩ := h
    exact ⟨h.cliffordExtraction⟩)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro c
    exact Quotient.sound ⟨FullOddKasparovHomotopy.ofIso
      (c := c.cliffordExpansion.cliffordExtraction) (d := c)
      c.cycle.cliffordExtractionExpansionIso⟩
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro c
    exact Quotient.sound
      ⟨FullGradedKasparovHomotopy.cliffordOfIso
        (c := c.cliffordExtraction.cliffordExpansion) (d := c)
        c.cycle.cliffordReconstructionIso.symm⟩

end BC4lean.KKTheory
