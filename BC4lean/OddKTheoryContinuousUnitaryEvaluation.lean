import BC4lean.UnitizationContinuousProjectionEvaluation
import BC4lean.OddFredholmOperatorK1Index

/-! # Actual finite unitary paths from interval coefficient evaluation

Finite unitization matrices over C(I,B) evaluate to an actual norm path.
The full scalar identity is preserved throughout, so both endpoint classes
agree in the genuine nonunital OperatorK1 kernel.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open BC4lean.OperatorKTheory
open scoped CStarAlgebra

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationOddKTheoryContinuousUnitaryEvaluationLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryContinuousUnitaryEvaluationLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _

def oddKTheoryUnitizationUnitaryEvaluation (t : I)
    (U : unitary (CStarMatrix ι ι (Unitization ℂ C(I, B)))) :
    unitary (CStarMatrix ι ι (Unitization ℂ B)) :=
  by
    let φ : CStarMatrix ι ι (Unitization ℂ C(I, B)) →⋆ₐ[ℂ]
        CStarMatrix ι ι (Unitization ℂ B) :=
      matrixMap (A := Unitization ℂ C(I, B)) (B := Unitization ℂ B) (ι := ι)
        (unitizationContinuousEvaluation (B := B) (X := I) t)
    exact ⟨φ (U : CStarMatrix ι ι (Unitization ℂ C(I, B))),
      Unitary.map_mem φ U.property⟩

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryUnitizationUnitaryEvaluation_scalar
    [PartialOrder B] [StarOrderedRing B] (t : I)
    (U : unitary (CStarMatrix ι ι (Unitization ℂ C(I, B))))
    (hU : unitizationScalarMatrix (U : CStarMatrix ι ι (Unitization ℂ C(I, B))) = 1) :
    unitizationScalarMatrix (oddKTheoryUnitizationUnitaryEvaluation t U : CStarMatrix ι ι (Unitization ℂ B)) = 1 := by
  change unitizationScalarMatrix
    (unitizationContinuousMatrixEvaluation (B := B) (X := I) (ι := ι) t
      (U : CStarMatrix ι ι (Unitization ℂ C(I, B)))) = 1
  rw [unitizationScalarMatrix_continuousEvaluation, hU]

def oddKTheoryUnitizationUnitaryEvaluationPath
    (U : unitary (CStarMatrix ι ι (Unitization ℂ C(I, B)))) :
    Path (oddKTheoryUnitizationUnitaryEvaluation 0 U)
      (oddKTheoryUnitizationUnitaryEvaluation 1 U) where
  toFun t := oddKTheoryUnitizationUnitaryEvaluation t U
  continuous_toFun := (continuous_unitizationContinuousMatrixEvaluation (B := B) (X := I) (ι := ι)
    (U : CStarMatrix ι ι (Unitization ℂ C(I, B)))).subtype_mk _
  source' := rfl
  target' := rfl

theorem oddKTheoryUnitizationUnitaryEvaluation_operatorK1_endpoints
    (U : unitary (CStarMatrix ι ι (Unitization ℂ C(I, B))))
    (hU : unitizationScalarMatrix (U : CStarMatrix ι ι (Unitization ℂ C(I, B))) = 1) :
    oddFredholmScalarIdentityUnitaryIndex (oddKTheoryUnitizationUnitaryEvaluation 0 U)
        (oddKTheoryUnitizationUnitaryEvaluation_scalar 0 U hU) =
      oddFredholmScalarIdentityUnitaryIndex (oddKTheoryUnitizationUnitaryEvaluation 1 U)
        (oddKTheoryUnitizationUnitaryEvaluation_scalar 1 U hU) := by
  apply Subtype.ext
  exact K1.of_homotopic ⟨oddKTheoryUnitizationUnitaryEvaluationPath U⟩

end BC4lean.KKTheory
