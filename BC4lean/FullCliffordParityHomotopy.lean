import BC4lean.BundledOddKasparovCycle
import BC4lean.FullGradedKasparovHomotopy
import BC4lean.CliffordIntervalExpansionFibre

/-! # Clifford parity preserves genuine full arbitrary interval homotopies

An odd full homotopy stores an actual odd cycle on an arbitrary complete,
countably generated interval-coefficient module, with whole-cycle endpoint
unitaries. Extraction and expansion transport such witnesses in both
directions by the actual coefficient equivalence and fibre unitaries proved
earlier. The equivalences below concern single full witnesses. No generated
equivalence closure, fixed-module normal form, or endpoint transport is assumed.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- A full odd interval homotopy allows every actual complete interval module. -/
structure FullOddKasparovHomotopy
    (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) where
  intervalCycle : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α
    (β.continuousSections (X := unitInterval))
  sourceIso : OddKasparovCycleIso (intervalCycle.cycle.fibre 0) c.cycle
  targetIso : OddKasparovCycleIso (intervalCycle.cycle.fibre 1) d.cycle

namespace FullOddKasparovHomotopy
variable {c d e f : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}

def changeEndpoints (h : FullOddKasparovHomotopy c d) (u : c.Iso e) (v : d.Iso f) :
    FullOddKasparovHomotopy e f where
  intervalCycle := h.intervalCycle
  sourceIso := h.sourceIso.trans u
  targetIso := h.targetIso.trans v

/-- Expand the same arbitrary odd interval witness into a genuine Clifford
graded interval witness, with actual identifications of both fibres. -/
def cliffordExpansion (h : FullOddKasparovHomotopy c d) :
    FullGradedKasparovHomotopy c.cliffordExpansion d.cliffordExpansion where
  intervalCycle := BundledGradedKasparovCycle.of h.intervalCycle.cycle.cliffordIntervalExpansion
  sourceIso := (h.intervalCycle.cycle.cliffordIntervalExpansionFibreIso 0).trans
    h.sourceIso.cliffordExpansion
  targetIso := (h.intervalCycle.cycle.cliffordIntervalExpansionFibreIso 1).trans
    h.targetIso.cliffordExpansion

end FullOddKasparovHomotopy

namespace FullGradedKasparovHomotopy
variable {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
  CStarGrading.trivial cliffordCoefficientGrading}

/-- Extract the actual first range of any arbitrary full Clifford interval
witness, and use the proved whole-cycle extraction-fibre unitaries. -/
def cliffordExtraction (h : FullGradedKasparovHomotopy c d) :
    FullOddKasparovHomotopy c.cliffordExtraction d.cliffordExtraction where
  intervalCycle := BundledOddKasparovCycle.of h.intervalCycle.cycle.cliffordIntervalExtraction
  sourceIso := (h.intervalCycle.cycle.cliffordIntervalExtractionFibreIso 0).trans
    (h.sourceIso.cliffordExtraction true)
  targetIso := (h.intervalCycle.cycle.cliffordIntervalExtractionFibreIso 1).trans
    (h.targetIso.cliffordExtraction true)

end FullGradedKasparovHomotopy

/-- Two odd cycles admit a single full interval witness exactly when their
Clifford expansions do. Both implications construct actual interval witnesses. -/
theorem fullOddHomotopy_iff_cliffordExpansion
    (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    Nonempty (FullOddKasparovHomotopy c d) ↔
      Nonempty (FullGradedKasparovHomotopy c.cliffordExpansion d.cliffordExpansion) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.cliffordExpansion⟩
  · rintro ⟨h⟩
    exact ⟨h.cliffordExtraction.changeEndpoints
      c.cycle.cliffordExtractionExpansionIso d.cycle.cliffordExtractionExpansionIso⟩

/-- Two genuine Clifford cycles admit a single full witness exactly when
their extracted odd cycles do; reconstruction changes the endpoints by the
proved whole-cycle unitaries. -/
theorem fullCliffordHomotopy_iff_extraction
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :
    Nonempty (FullGradedKasparovHomotopy c d) ↔
      Nonempty (FullOddKasparovHomotopy c.cliffordExtraction d.cliffordExtraction) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.cliffordExtraction⟩
  · rintro ⟨h⟩
    exact ⟨h.cliffordExpansion.changeEndpoints
      c.cycle.cliffordReconstructionIso.symm d.cycle.cliffordReconstructionIso.symm⟩

end BC4lean.KKTheory
