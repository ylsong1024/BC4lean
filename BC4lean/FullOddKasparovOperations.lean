import BC4lean.OddKasparovHomotopyRelation
import BC4lean.BundledOddKasparovOperations
import BC4lean.OddKasparovFibreDirectSumIso
import BC4lean.OddKasparovFibreOpposite
import BC4lean.OddIntervalOperatorHomotopy
import BC4lean.OddConeKasparovHomotopy

/-! # Actual full odd witnesses for the additive operations

Direct sums use the genuine sum-fibre unitary. Opposites use the actual
identity fibre unitary for the negated operator. The inverse rotation and
degenerate cone are actual interval cycles, and their matched concatenation
is one full witness for the inverse law.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace FullOddKasparovHomotopy

def directSum {c d k l : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) (h' : FullOddKasparovHomotopy k l) :
    FullOddKasparovHomotopy (c.directSum k) (d.directSum l) where
  intervalCycle := h.intervalCycle.directSum h'.intervalCycle
  sourceIso := by
    change OddKasparovCycleIso
      ((h.intervalCycle.cycle.directSum h'.intervalCycle.cycle).fibre (0 : unitInterval))
      (c.cycle.directSum k.cycle)
    exact OddKasparovCycleIso.trans
      (OddKasparovCycleIso.fibreDirectSum h.intervalCycle.cycle h'.intervalCycle.cycle
        (0 : unitInterval)) (h.sourceIso.directSum h'.sourceIso)
  targetIso := by
    change OddKasparovCycleIso
      ((h.intervalCycle.cycle.directSum h'.intervalCycle.cycle).fibre (1 : unitInterval))
      (d.cycle.directSum l.cycle)
    exact OddKasparovCycleIso.trans
      (OddKasparovCycleIso.fibreDirectSum h.intervalCycle.cycle h'.intervalCycle.cycle
        (1 : unitInterval)) (h.targetIso.directSum h'.targetIso)

def opposite {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) : FullOddKasparovHomotopy c.opposite d.opposite where
  intervalCycle := h.intervalCycle.opposite
  sourceIso := (OddKasparovCycleIso.fibreOpposite h.intervalCycle.cycle 0).trans h.sourceIso.opposite
  targetIso := (OddKasparovCycleIso.fibreOpposite h.intervalCycle.cycle 1).trans h.targetIso.opposite

def degenerateCone (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β)
    (hc : c.cycle.IsDegenerate) : FullOddKasparovHomotopy (BundledOddKasparovCycle.zero α β) c where
  intervalCycle := BundledOddKasparovCycle.of (c.cycle.degenerateCone hc)
  sourceIso := c.cycle.degenerateConeZeroFibreIso hc
  targetIso := c.cycle.degenerateConeOneFibreIso hc

def inverseRotation (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    FullOddKasparovHomotopy (c.directSum c.opposite)
      (BundledOddKasparovCycle.of ((OddKasparovOperatorHomotopy.inverseRotation c.cycle).cycleAt 1)) where
  intervalCycle := BundledOddKasparovCycle.of
    (OddKasparovOperatorHomotopy.inverseRotation c.cycle).intervalCycle
  sourceIso := by
    change OddKasparovCycleIso
      ((OddKasparovOperatorHomotopy.inverseRotation c.cycle).intervalCycle.fibre
        (0 : unitInterval)) (c.cycle.directSum c.cycle.opposite)
    simpa only [OddKasparovOperatorHomotopy.source_cycleAt, OddKasparovCycle.withOperator_self] using
      (OddKasparovOperatorHomotopy.inverseRotation c.cycle).intervalFibreIso 0
  targetIso := (OddKasparovOperatorHomotopy.inverseRotation c.cycle).intervalFibreIso 1

/-- The inverse law is witnessed by one actual joined arbitrary interval module. -/
def inverseLaw [TopologicalSpace.SeparableSpace B]
    (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    FullOddKasparovHomotopy (c.opposite.directSum c) (BundledOddKasparovCycle.zero α β) :=
  (ofIso (BundledOddKasparovCycle.directSumCommIso c.opposite c)).trans
    ((inverseRotation c).trans
      (degenerateCone _ (OddKasparovOperatorHomotopy.inverseRotation_target_isDegenerate c.cycle)).symm)

end FullOddKasparovHomotopy
end BC4lean.KKTheory
