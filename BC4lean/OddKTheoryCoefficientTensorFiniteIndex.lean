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

set_option maxHeartbeats 4000000 in
theorem oddKTheoryMatrixUnitaryCoefficientTensor_operatorK1Index
    (f : B →⋆ₙₐ[ℂ] C) (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    ((oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu).coefficientTensor f).operatorK1Index =
      operatorK1Map f (oddFredholmScalarIdentityUnitaryIndex u hu) := by
  let : CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
    finiteHilbertModuleSum_complete
  have hIso : OddKasparovCycleIso (Γ := PUnit) (A := ℂ) (B := C)
      (E := InteriorModuleTensor
        (E := CountableHilbertModuleSum B (FiniteStandardModule B ι))
        (standardCoefficientImageRepresentation (B := B) (C := C) f))
      (F := CountableHilbertModuleSum C
        (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι))
      ((oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (B := B) (ι := ι) u hu).coefficientTensor f)
      (coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu) :=
    oddKTheoryMatrixUnitaryCoefficientTensorIso (B := B) (C := C) (ι := ι) f u hu
  have hIndexIso :
      ((oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (B := B) (ι := ι) u hu).coefficientTensor f).operatorK1Index =
        (coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu).operatorK1Index :=
    oddScalarKasparovOperatorK1Index_iso (B := C)
      (E := InteriorModuleTensor
        (E := CountableHilbertModuleSum B (FiniteStandardModule B ι))
        (standardCoefficientImageRepresentation (B := B) (C := C) f))
      (N := CountableHilbertModuleSum C
        (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι))
      (c := (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (B := B) (ι := ι) u hu).coefficientTensor f)
      (d := coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu) hIso
  calc
    _ = (coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu).operatorK1Index :=
      hIndexIso
    _ = (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (B := C) (ι := ι)
        (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
          (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u)
        (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu)).operatorK1Index :=
      (oddScalarKasparovOperatorK1Index_full (B := C)
        (c := BundledOddKasparovCycle.of (Γ := PUnit) (A := ℂ) (B := C)
          (E := CountableHilbertModuleSum C (FiniteStandardModule C ι))
          (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (B := C) (ι := ι)
            (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
              (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u)
            (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu)))
        (d := BundledOddKasparovCycle.of (Γ := PUnit) (A := ℂ) (B := C)
          (E := CountableHilbertModuleSum C
            (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι))
          (coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu))
        (coefficientImageFiniteUnitaryFullHomotopy (B := B) (C := C) (ι := ι) f u hu)).symm
    _ = oddFredholmScalarIdentityUnitaryIndex (B := C) (ι := ι)
        (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
          (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u)
        (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu) :=
      oddKTheoryMatrixUnitaryCycle_operatorK1Index (B := C) (ι := ι)
        (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
          (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u)
        (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu)
    _ = _ := (oddFredholmScalarIdentityUnitaryIndex_map (B := B) (C := C) (ι := ι) f u hu).symm

end BC4lean.KKTheory
