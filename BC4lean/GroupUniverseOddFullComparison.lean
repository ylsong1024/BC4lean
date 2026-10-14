import BC4lean.GroupShrinkOddEquivalence
import BC4lean.GroupUniverseCliffordBridge
import BC4lean.OddKTheoryComparisonAddEquiv

/-! # Scalar odd and Clifford comparisons for every module universe

The genuine arbitrary-interval shrink equivalence places any original
complete countably generated module in the coefficient universe. The
proved canonical finite inverse then gives the comparison. The full
whole-cycle unitary invariance of the actual index identifies its forward
map with the original index in every module universe, including a module
universe smaller than the coefficient universe. Source and group remain
PUnit and ℂ in universe zero; coefficients retain their original universe.
-/

noncomputable section
universe uB uE
namespace BC4lean.KKTheory
variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

theorem oddKKOperatorK1Index_shrink (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1Index (OddKK.shrink.{0, 0, uB, uE, uB} x) = oddKKOperatorK1Index x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact (oddScalarKasparovOperatorK1Index_iso
    (c.shrinkIso : OddKasparovCycleIso c.cycle
      (c.shrink : BundledOddKasparovCycle.{0, 0, uB, uB} α₁ β₁).cycle)).symm

def oddKKOperatorK1AllModuleUniversesAddEquiv :
    OddKK.{0, 0, uB, uE} α₁ β₁ ≃+ OperatorKTheory.OperatorK1 B :=
  (OddKK.shrinkAddEquiv.{0, 0, uB, uE, uB}).trans oddKKOperatorK1AddEquiv

@[simp] theorem oddKKOperatorK1AllModuleUniversesAddEquiv_apply
    (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1AllModuleUniversesAddEquiv x = oddKKOperatorK1Index x :=
  oddKKOperatorK1Index_shrink x

theorem oddKKOperatorK1Index_allModuleUniverses_bijective :
    Function.Bijective (oddKKOperatorK1Index : OddKK.{0, 0, uB, uE} α₁ β₁ →
      OperatorKTheory.OperatorK1 B) := by
  have hfun :
      ((oddKKOperatorK1AllModuleUniversesAddEquiv (B := B) :
        OddKK.{0, 0, uB, uE} α₁ β₁ ≃+ OperatorKTheory.OperatorK1 B) :
        OddKK.{0, 0, uB, uE} α₁ β₁ → OperatorKTheory.OperatorK1 B) =
      (oddKKOperatorK1Index : OddKK.{0, 0, uB, uE} α₁ β₁ →
        OperatorKTheory.OperatorK1 B) := by
    funext x
    exact oddKKOperatorK1AllModuleUniversesAddEquiv_apply x
  rw [← hfun]
  exact (oddKKOperatorK1AllModuleUniversesAddEquiv (B := B) :
    OddKK.{0, 0, uB, uE} α₁ β₁ ≃+ OperatorKTheory.OperatorK1 B).bijective

def scalarCliffordOperatorK1AllModuleUniversesAddEquiv :
    GradedKasparovHomotopyClass.{0, 0, uB, uE} α₁ (cliffordTensorAction β₁)
      CStarGrading.trivial cliffordTensorGrading ≃+ OperatorKTheory.OperatorK1 B :=
  GroupUniverseCliffordBridge.oddAddEquivalence.trans
    oddKKOperatorK1AllModuleUniversesAddEquiv

end BC4lean.KKTheory
