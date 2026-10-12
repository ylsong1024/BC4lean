import BC4lean.OddKTheoryFiniteCoefficientTensorIso
import BC4lean.OddKTheoryComparisonAddEquiv

/-! # The actual finite odd inverse index after arbitrary coefficient extension

Coefficients may have independent universes. The completed tensor of the
finite unitary inverse is genuinely the true image-module inverse. Its
actual image interval homotopy identifies its index with the mapped finite
unitary index. This statement is independent of the quotient coefficient
product wrapper and supplies its finite naturality computation.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationOddKTheoryCoefficientTensorFiniteIndexLocalInstance01 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete

theorem oddKTheoryMatrixUnitaryCoefficientTensor_operatorK1Index
    (f : B →⋆ₙₐ[ℂ] C) (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    ((oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu).coefficientTensor f).operatorK1Index =
      operatorK1Map f (oddFredholmScalarIdentityUnitaryIndex u hu) := by
  calc
    _ = (coefficientImageFiniteUnitaryCycle f u hu).operatorK1Index :=
      oddScalarKasparovOperatorK1Index_iso (oddKTheoryMatrixUnitaryCoefficientTensorIso f u hu)
    _ = (oddKTheoryMatrixUnitaryCycle (Γ := PUnit)
        (matrixUnitaryMap (Unitization.starMap f) u)
        (oddKTheoryMatrixMap_scalarIdentity f u hu)).operatorK1Index :=
      (oddScalarKasparovOperatorK1Index_full
        (coefficientImageFiniteUnitaryFullHomotopy f u hu)).symm
    _ = oddFredholmScalarIdentityUnitaryIndex
        (matrixUnitaryMap (Unitization.starMap f) u)
        (oddKTheoryMatrixMap_scalarIdentity f u hu) :=
      oddKTheoryMatrixUnitaryCycle_operatorK1Index _ _
    _ = _ := (oddFredholmScalarIdentityUnitaryIndex_map f u hu).symm

end BC4lean.KKTheory
