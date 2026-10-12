import BC4lean.CliffordParityGroup
import BC4lean.CliffordDirectSumIso

/-! # The proved Clifford quotient addition is the actual graded direct sum

The transported additive law agrees with the raw genuine graded Hilbert
sum by the actual reconstruction unitaries and pair-sum permutation. Full
sum witnesses are built from the extracted odd full witnesses and then
expanded with those same whole-cycle endpoint unitaries.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace CliffordKK
def mk (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
    CStarGrading.trivial cliffordCoefficientGrading) : CliffordKK.{uΓ, uA, uB, uE} α β :=
  Quotient.mk _ c

theorem mk_eq_of_iso
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading} (u : c.Iso d) : mk c = mk d :=
  Quotient.sound ⟨FullGradedKasparovHomotopy.cliffordOfIso u⟩

theorem mk_eq_parity_extraction
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :
    mk c = cliffordParityAddEquiv (OddKK.mk c.cliffordExtraction) :=
  mk_eq_of_iso c.cycle.cliffordReconstructionIso

/-- Quotient addition is exactly the class of the actual raw graded sum. -/
@[simp] theorem mk_directSum
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :
    mk (c.directSum d) = mk c + mk d := by
  have u : (c.directSum d).Iso
      (c.cliffordExtraction.directSum d.cliffordExtraction).cliffordExpansion := by
    dsimp only [BundledGradedKasparovCycle.Iso, BundledGradedKasparovCycle.directSum,
      BundledGradedKasparovCycle.cliffordExtraction, BundledGradedKasparovCycle.of,
      BundledOddKasparovCycle.directSum, BundledOddKasparovCycle.cliffordExpansion,
      BundledOddKasparovCycle.of]
    exact c.cycle.cliffordReconstructionDirectSumIso d.cycle
  have h : mk (c.directSum d) = cliffordParityAddEquiv
      (OddKK.mk (c.cliffordExtraction.directSum d.cliffordExtraction)) := by
    rw [cliffordParityAddEquiv_apply]
    change mk (c.directSum d) =
      mk (c.cliffordExtraction.directSum d.cliffordExtraction).cliffordExpansion
    exact mk_eq_of_iso (c := c.directSum d)
      (d := (c.cliffordExtraction.directSum d.cliffordExtraction).cliffordExpansion)
      u
  rw [h, OddKK.mk_directSum, map_add, ← mk_eq_parity_extraction, ← mk_eq_parity_extraction]

end CliffordKK

set_option maxHeartbeats 600000 in
/-- The raw graded sum of two actual full Clifford witnesses has an actual
full witness, obtained by extracting, summing, expanding and using the proved
whole-cycle direct-sum reconstruction at its endpoints. -/
def FullGradedKasparovHomotopy.cliffordDirectSum
    {c d k l : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading}
    (h : FullGradedKasparovHomotopy c d) (h' : FullGradedKasparovHomotopy k l) :
    FullGradedKasparovHomotopy (c.directSum k) (d.directSum l) := by
  let hs : FullOddKasparovHomotopy
      (c.cliffordExtraction.directSum k.cliffordExtraction)
      (d.cliffordExtraction.directSum l.cliffordExtraction) :=
    FullOddKasparovHomotopy.directSum
      (c := c.cliffordExtraction) (d := d.cliffordExtraction)
      (k := k.cliffordExtraction) (l := l.cliffordExtraction)
      h.cliffordExtraction h'.cliffordExtraction
  have hsum : FullGradedKasparovHomotopy
      (c.cliffordExtraction.directSum k.cliffordExtraction).cliffordExpansion
      (d.cliffordExtraction.directSum l.cliffordExtraction).cliffordExpansion :=
    FullOddKasparovHomotopy.cliffordExpansion
      (c := c.cliffordExtraction.directSum k.cliffordExtraction)
      (d := d.cliffordExtraction.directSum l.cliffordExtraction) hs
  have u : (c.cliffordExtraction.directSum k.cliffordExtraction).cliffordExpansion.Iso
      (c.directSum k) := by
    dsimp only [BundledGradedKasparovCycle.Iso, BundledGradedKasparovCycle.directSum,
      BundledGradedKasparovCycle.cliffordExtraction, BundledGradedKasparovCycle.of,
      BundledOddKasparovCycle.directSum, BundledOddKasparovCycle.cliffordExpansion,
      BundledOddKasparovCycle.of]
    exact (c.cycle.cliffordReconstructionDirectSumIso k.cycle).symm
  have v : (d.cliffordExtraction.directSum l.cliffordExtraction).cliffordExpansion.Iso
      (d.directSum l) := by
    dsimp only [BundledGradedKasparovCycle.Iso, BundledGradedKasparovCycle.directSum,
      BundledGradedKasparovCycle.cliffordExtraction, BundledGradedKasparovCycle.of,
      BundledOddKasparovCycle.directSum, BundledOddKasparovCycle.cliffordExpansion,
      BundledOddKasparovCycle.of]
    exact (d.cycle.cliffordReconstructionDirectSumIso l.cycle).symm
  exact hsum.changeEndpoints (e := c.directSum k) (f := d.directSum l)
    u v

end BC4lean.KKTheory
