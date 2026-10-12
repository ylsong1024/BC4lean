import BC4lean.GroupUniverseOddFullComparison

/-! # The genuine odd index and finite inverse in arbitrary module universes

Whole shrinking unitaries preserve the actual index. Transporting the
proved finite inverse through the actual full-homotopy shrink map places
it in any chosen module universe. Its two inverse identities follow from
the already proved canonical finite recovery and the genuine full odd
comparison for every original module universe.
-/

noncomputable section
universe uB uE uF
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

theorem oddKKOperatorK1Index_shrink_anyModuleUniverse
    (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1Index (OddKK.shrink.{0, 0, uB, uE, uF} x) =
      oddKKOperatorK1Index x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact (oddScalarKasparovOperatorK1Index_iso
    (c.shrinkIso : OddKasparovCycleIso c.cycle
      (c.shrink : BundledOddKasparovCycle.{0, 0, uB, uF} α₁ β₁).cycle)).symm

def oddOperatorK1KKInverseAllModuleUniverses :
    OperatorK1 B →+ OddKK.{0, 0, uB, uE} α₁ β₁ :=
  (OddKK.shrinkHom.{0, 0, uB, uB, uE}).comp oddOperatorK1KKInverse

theorem oddOperatorK1KKInverseAllModuleUniverses_rightInverse_index
    (x : OperatorK1 B) :
    oddKKOperatorK1Index (oddOperatorK1KKInverseAllModuleUniverses.{uB, uE} x) = x := by
  change oddKKOperatorK1Index
    (OddKK.shrink.{0, 0, uB, uB, uE} (oddOperatorK1KKInverse x)) = x
  rw [oddKKOperatorK1Index_shrink_anyModuleUniverse]
  exact oddOperatorK1KKInverse_rightInverse_index x

theorem oddOperatorK1KKInverseAllModuleUniverses_leftInverse_index
    (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddOperatorK1KKInverseAllModuleUniverses.{uB, uE} (oddKKOperatorK1Index x) = x := by
  change OddKK.shrink.{0, 0, uB, uB, uE}
    (oddOperatorK1KKInverse (oddKKOperatorK1Index x)) = x
  rw [← oddKKOperatorK1Index_shrink_anyModuleUniverse.{uB, uE, uB} x,
    oddOperatorK1KKInverse_leftInverse_index, OddKK.shrink_shrink]

theorem oddOperatorK1KKInverseAllModuleUniverses_eq_comparison_symm
    (x : OperatorK1 B) :
    oddOperatorK1KKInverseAllModuleUniverses.{uB, uE} x =
      (oddKKOperatorK1AllModuleUniversesAddEquiv (B := B) :
        OddKK.{0, 0, uB, uE} α₁ β₁ ≃+ OperatorK1 B).symm x := by
  apply (oddKKOperatorK1AllModuleUniversesAddEquiv (B := B) :
    OddKK.{0, 0, uB, uE} α₁ β₁ ≃+ OperatorK1 B).injective
  rw [AddEquiv.apply_symm_apply, oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  exact oddOperatorK1KKInverseAllModuleUniverses_rightInverse_index x

end BC4lean.KKTheory
