import BC4lean.OddKTheoryStandardUnitaryInverse
import BC4lean.OddFredholmSumOperatorHom
import BC4lean.OddKTheoryIndexQuotient
import BC4lean.OddFredholmRowEndpoint

/-! # One actual inverse identity for every scalar odd Kasparov cycle

The actual supported normalized cycle gives a selfadjoint contraction. Its
genuine augmented absorption is still a contraction. The finite inverse of
its actual exponential index equals the completed row inverse, and the
explicit row reflection homotopy recovers the whole original odd class.
Degenerate scalar representations and arbitrary complete countably generated
coefficient modules are included through the actual support projection.
-/

noncomputable section
universe uB
namespace BC4lean.KKTheory

variable {B E : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace B]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

def oddFredholmCompactExponentialPullbackCycleIso
    (hE : IsCountablyGeneratedModule B E) (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * F - 1))
    (hnorm : ‖(F : AdjointableMap B E E)‖ ≤ 1) :
    OddKasparovCycleIso
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hE (oddFredholmExponential F)
        (oddFredholmExponential_sub_one_isModuleCompact F hF))
      (oddFredholmRowExponentialPullbackCycle (Γ := PUnit) hE F hF hnorm) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

theorem oddOperatorK1KKInverse_standardFredholmIndex
    (F : selfAdjoint (OddFredholmStandardOperator B))
    (hF : IsModuleCompact ((F : OddFredholmStandardOperator B) ^ 2 - 1))
    (hnorm : ‖(F : OddFredholmStandardOperator B)‖ ≤ 1) :
    oddOperatorK1KKInverse (oddFredholmStandardIndex F hF) =
      OddKK.mk (BundledOddKasparovCycle.of (oddKTheoryScalarFredholmCycle (Γ := PUnit)
        standardCountableHilbertModule_isCountablyGenerated F F.property
        (by simpa only [pow_two] using hF))) := by
  have hs : IsModuleCompact ((F : OddFredholmStandardOperator B) * F - 1) := by
    simpa only [pow_two] using hF
  calc
    _ = OddKK.mk (BundledOddKasparovCycle.of
        (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
          standardCountableHilbertModule_isCountablyGenerated (oddFredholmExponential F)
          (oddFredholmExponential_sub_one_isModuleCompact F hs))) :=
      oddOperatorK1KKInverse_standardUnitaryIndex _ _
    _ = OddKK.mk (BundledOddKasparovCycle.of
        (oddFredholmRowExponentialPullbackCycle (Γ := PUnit)
          standardCountableHilbertModule_isCountablyGenerated F hs hnorm)) :=
      OddKK.mk_eq_of_iso (oddFredholmCompactExponentialPullbackCycleIso _ F hs hnorm)
    _ = _ := oddFredholmRowExponentialPullbackCycle_class _ F hs hnorm

theorem OddKasparovCycle.operatorK1Index_inverse_class (c : OddKasparovCycle α₁ β₁ E) :
    oddOperatorK1KKInverse c.operatorK1Index = OddKK.mk (BundledOddKasparovCycle.of c) := by
  let F := oddFredholmStandardStabilizedOperator c.scalarSupportNormalizedCycle.countablyGenerated
    c.scalarSupportFredholmSelfAdjoint
  have hF : IsModuleCompact ((F : OddFredholmStandardOperator B) ^ 2 - 1) := by
    simpa only [F, pow_two] using oddFredholmStandardStabilizedOperator_square_compact
      c.scalarSupportNormalizedCycle.countablyGenerated c.scalarSupportFredholmSelfAdjoint
      c.scalarSupportNormalizedCycle_square_isModuleCompact
  have hnorm : ‖(F : OddFredholmStandardOperator B)‖ ≤ 1 :=
    oddFredholmStandardStabilizedOperator_norm_le_one _ _
      c.scalarSupportNormalizedCycle_norm_le_one
  change oddOperatorK1KKInverse (oddFredholmStandardIndex F hF) = _
  exact (oddOperatorK1KKInverse_standardFredholmIndex F hF hnorm).trans
    c.scalarStandardFredholmCycle_class

theorem oddOperatorK1KKInverse_leftInverse_index :
    Function.LeftInverse (oddOperatorK1KKInverse (B := B))
      (oddKKOperatorK1Index : OddKK.{0, 0, uB, uB} α₁ β₁ → OperatorKTheory.OperatorK1 B) := by
  intro x
  induction x using Quotient.inductionOn with
  | h c => exact c.cycle.operatorK1Index_inverse_class

theorem oddKKOperatorK1Index_injective :
    Function.Injective (oddKKOperatorK1Index :
      OddKK.{0, 0, uB, uB} α₁ β₁ → OperatorKTheory.OperatorK1 B) :=
  oddOperatorK1KKInverse_leftInverse_index.injective

theorem oddOperatorK1KKInverse_surjective :
    Function.Surjective (oddOperatorK1KKInverse (B := B)) :=
  oddOperatorK1KKInverse_leftInverse_index.surjective

end BC4lean.KKTheory
