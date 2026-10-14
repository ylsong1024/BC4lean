import BC4lean.OddKTheoryArbitraryCycleInverse
import BC4lean.OddKTheoryFiniteCornerAbsorption
import BC4lean.OddKTheoryTwoRowExponentialCorner

/-! # The actual additive odd scalar KK and nonunital OperatorK1 comparison

The finite inverse respects actual homotopy and identity stabilization
generators. Its exponential has the genuine embedded two-row recovery matrix,
whose stable unitary class is the original matrix class. The arbitrary-cycle
reflection homotopy proves the other inverse identity. Both proved identities
give an actual additive equivalence with the existing scalar-kernel OperatorK1.
-/

noncomputable section
universe uB
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

local instance oddContinuationOddKTheoryComparisonAddEquivLocalInstance01 {ι : Type} [Fintype ι] [DecidableEq ι] : CompleteSpace (FiniteStandardModule B ι) :=
  finiteStandardModule_complete

theorem oddKTheoryMatrixUnitaryCycle_operatorK1Index {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu).operatorK1Index =
      oddFredholmScalarIdentityUnitaryIndex u hu := by
  have hscalar : (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu).operatorK1Index =
      oddFredholmStabilizedIndex
        (oddKTheoryCountableFiniteRows_isCountablyGenerated (B := B) (ι := ι))
        (oddKTheoryMatrixLoopSelfAdjoint (B := B) (ι := ι) u)
        (oddKTheoryMatrixLoopPullback_square_isModuleCompact (B := B) (ι := ι) u hu) := by
    simpa only [oddKTheoryMatrixUnitaryCycle, oddKTheoryMatrixLoopSelfAdjoint] using
      (oddFredholmScalarCycle_operatorK1Index (B := B)
        (E := CountableHilbertModuleSum B (FiniteStandardModule B ι))
        (oddKTheoryCountableFiniteRows_isCountablyGenerated (B := B) (ι := ι))
        (oddKTheoryMatrixLoopSelfAdjoint (B := B) (ι := ι) u)
        (oddKTheoryMatrixLoopPullback_square_isModuleCompact (B := B) (ι := ι) u hu))
  exact hscalar.trans ((oddFredholmStabilizedIndex_finiteExponentialCorner (B := B)
    (E := CountableHilbertModuleSum B (FiniteStandardModule B ι)) (ι := ι ⊕ ι)
    (oddKTheoryCountableFiniteRows_isCountablyGenerated (B := B) (ι := ι))
    (oddKTheoryMatrixLoopSelfAdjoint (B := B) (ι := ι) u)
    (oddKTheoryMatrixLoopPullback_square_isModuleCompact (B := B) (ι := ι) u hu)
    (oddKTheoryTwoRowFiniteInclusion (B := B) (ι := ι))
    (oddKTheoryTwoRowFiniteInclusion_isometry (B := B) (ι := ι))
    (oddKTheoryFiniteExponentialRecovery (A := Unitization ℂ B) (ι := ι) u)
    (oddKTheoryFiniteExponentialRecovery_scalar (B := B) (ι := ι) u hu)
    (oddKTheoryMatrixLoopExponential_twoRowCorner (B := B) (ι := ι) u)).trans
      (oddKTheoryFiniteExponentialRecovery_operatorK1 (B := B) (ι := ι) u hu))

theorem oddOperatorK1KKInverse_rightInverse_index :
    Function.RightInverse (oddOperatorK1KKInverse (B := B))
      (oddKKOperatorK1Index : OddKK.{0, 0, uB, uB} α₁ β₁ → OperatorK1 B) := by
  intro x
  obtain ⟨n, u, hu, hx⟩ := oddKTheoryOperatorK1_exists_scalarIdentityRepresentative x
  rw [← hx, oddOperatorK1KKInverse_scalarIdentityUnitary]
  exact oddKTheoryMatrixUnitaryCycle_operatorK1Index u hu

/-- The genuine inverse built from actual finite matrix unitary cycles is
an additive equivalence; both inverse identities are proved from actual paths. -/
def oddOperatorK1KKAddEquiv : OperatorK1 B ≃+
    OddKK.{0, 0, uB, uB} α₁ β₁ where
  toFun := oddOperatorK1KKInverse
  invFun := oddKKOperatorK1Index
  left_inv := oddOperatorK1KKInverse_rightInverse_index
  right_inv := oddOperatorK1KKInverse_leftInverse_index
  map_add' := oddOperatorK1KKInverse.map_add

/-- Actual scalar odd Kasparov classes are the existing nonunital OperatorK1
group, with addition given by genuine whole-module direct sums. -/
def oddKKOperatorK1AddEquiv : OddKK.{0, 0, uB, uB} α₁ β₁ ≃+ OperatorK1 B :=
  oddOperatorK1KKAddEquiv.symm

@[simp] theorem oddKKOperatorK1AddEquiv_apply (x : OddKK.{0, 0, uB, uB} α₁ β₁) :
    oddKKOperatorK1AddEquiv x = oddKKOperatorK1Index x := rfl

@[simp] theorem oddKKOperatorK1AddEquiv_symm_apply (x : OperatorK1 B) :
    oddKKOperatorK1AddEquiv.symm x = oddOperatorK1KKInverse x := rfl

theorem oddKKOperatorK1Index_add (x y : OddKK.{0, 0, uB, uB} α₁ β₁) :
    oddKKOperatorK1Index (x + y) = oddKKOperatorK1Index x + oddKKOperatorK1Index y :=
  oddKKOperatorK1AddEquiv.map_add x y

def oddKKOperatorK1IndexHom : OddKK.{0, 0, uB, uB} α₁ β₁ →+ OperatorK1 B :=
  oddKKOperatorK1AddEquiv.toAddMonoidHom

end BC4lean.KKTheory
