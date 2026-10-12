import BC4lean.OddScalarKasparovIndexFibre
import BC4lean.OddKasparovHomotopyRelation

/-! # The genuine scalar odd index on the full odd KK quotient

The quotient relation is the existence of an arbitrary-module full interval
witness. Actual supported interval normalization, global stabilization,
completed fibre evaluation and proved absorption independence identify its
endpoint index values. Thus this lift uses the actual full relation.
-/

noncomputable section
universe uB uE
namespace BC4lean.KKTheory

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

theorem oddScalarKasparovOperatorK1Index_full
    {c d : BundledOddKasparovCycle.{0, 0, uB, uE} α₁ β₁}
    (h : FullOddKasparovHomotopy c d) : c.cycle.operatorK1Index = d.cycle.operatorK1Index := by
  calc
    _ = (h.intervalCycle.cycle.fibre 0).operatorK1Index :=
      (oddScalarKasparovOperatorK1Index_iso h.sourceIso).symm
    _ = (h.intervalCycle.cycle.fibre 1).operatorK1Index :=
      oddScalarKasparovOperatorK1Index_fibre_endpoints h.intervalCycle.cycle
    _ = _ := oddScalarKasparovOperatorK1Index_iso h.targetIso

/-- The actual exponential index descends to the project's full odd KK group
and takes values in its actual finite-unitary scalar-kernel OperatorK1(B). -/
def oddKKOperatorK1Index : OddKK.{0, 0, uB, uE} α₁ β₁ → OperatorKTheory.OperatorK1 B :=
  Quotient.lift (fun c => c.cycle.operatorK1Index) (by
    intro c d h
    obtain ⟨h⟩ := h
    exact oddScalarKasparovOperatorK1Index_full h)

@[simp] theorem oddKKOperatorK1Index_mk
    (c : BundledOddKasparovCycle.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1Index (OddKK.mk c) = c.cycle.operatorK1Index := rfl

end BC4lean.KKTheory
