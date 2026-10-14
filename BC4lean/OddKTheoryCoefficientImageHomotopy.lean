import BC4lean.CoefficientImageFiniteUnitary
import BC4lean.OddFredholmFullNormalization

/-! # A full odd inverse homotopy for every nonunital coefficient map

The arbitrary interval module is the actual finite sum of the right image
interval module. Its completed row fibres are identified by whole-cycle
unitaries. Thus the scalar-identity finite unitary on the full target
module and its true image-module inverse have the same full odd class.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationOddKTheoryCoefficientImageHomotopyLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryCoefficientImageHomotopyLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryCoefficientImageHomotopyLocalInstance03 : PartialOrder (Unitization ℂ C) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryCoefficientImageHomotopyLocalInstance04 : StarOrderedRing (Unitization ℂ C) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryCoefficientImageHomotopyLocalInstance05 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance oddContinuationOddKTheoryCoefficientImageHomotopyLocalInstance06 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance oddContinuationOddKTheoryCoefficientImageHomotopyLocalInstance07 : CompleteSpace (FiniteStandardModule C ι) := finiteStandardModule_complete

def coefficientImageFiniteUnitaryCycle (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C)
      (CountableHilbertModuleSum C (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι)) :=
  oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (B := C)
    (E := FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι)
    (finiteHilbertModuleSum_countablyGenerated (B := C) (E := CoefficientImageRightModule f) (ι := ι)
      (coefficientImageRightModule_countablyGenerated (B := B) (C := C) f))
    (finiteHilbertModuleCoefficientUnitary (A := B) (B := C)
      (E := CoefficientImageRightModule f) (ι := ι) (coefficientImageLeftMul (B := B) (C := C) f) u)
    (finiteHilbertModuleCoefficientUnitary_compact (A := B) (B := C)
      (E := CoefficientImageRightModule f) (ι := ι) (coefficientImageLeftMul (B := B) (C := C) f)
      (coefficientImageLeftMul_isModuleCompact (B := B) (C := C) f) u hu)

def coefficientImageFiniteIntervalUnitaryCycle (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C(unitInterval, C))
      (CountableHilbertModuleSum C(unitInterval, C)
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)) :=
  oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (B := C(unitInterval, C))
    (E := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
    (finiteHilbertModuleSum_countablyGenerated (B := C(unitInterval, C))
      (E := CoefficientImageIntervalModule f) (ι := ι)
      (coefficientImageIntervalModule_countablyGenerated (B := B) (C := C) f))
    (coefficientImageFiniteIntervalUnitary (B := B) (C := C) (ι := ι) f u)
    (coefficientImageFiniteIntervalUnitary_compact (B := B) (C := C) (ι := ι) f u hu)

set_option maxHeartbeats 4000000 in
def coefficientImageFiniteIntervalZeroIso (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycleIso (Γ := PUnit) (A := ℂ) (B := C)
      (E := HilbertModuleFibre C
        (CountableHilbertModuleSum C(unitInterval, C)
          (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι))
        (0 : unitInterval))
      (F := CountableHilbertModuleSum C (FiniteStandardModule C ι))
      ((coefficientImageFiniteIntervalUnitaryCycle (B := B) (C := C) (ι := ι) f u hu).fibre
        (Γ := PUnit) (A := ℂ) (B := C) (X := unitInterval)
        (M := CountableHilbertModuleSum C(unitInterval, C)
          (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι))
        (0 : unitInterval))
      (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (B := C) (ι := ι)
        (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
          (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u)
        (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu)) := by
  let hJ : IsCountablyGeneratedModule C(unitInterval, C)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) :=
    finiteHilbertModuleSum_countablyGenerated (B := C(unitInterval, C))
      (E := CoefficientImageIntervalModule f) (ι := ι)
      (coefficientImageIntervalModule_countablyGenerated (B := B) (C := C) f)
  let U : unitary (AdjointableMap C(unitInterval, C)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)) :=
    coefficientImageFiniteIntervalUnitary (B := B) (C := C) (ι := ι) f u
  let hU : IsModuleCompact ((U : AdjointableMap C(unitInterval, C)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)) - 1) :=
    coefficientImageFiniteIntervalUnitary_compact (B := B) (C := C) (ι := ι) f u hu
  let e : HilbertModuleEquiv C
      (HilbertModuleFibre C
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
        (0 : unitInterval)) (FiniteStandardModule C ι) :=
    coefficientImageFiniteZeroFibreEquiv (B := B) (C := C) (ι := ι) f
  have htransport := oddKTheoryCompactUnitaryTransportIso (B := C)
    (E := HilbertModuleFibre C
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (0 : unitInterval)) (F := FiniteStandardModule C ι)
    (hJ.fibre (B := C) (X := unitInterval)
      (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (0 : unitInterval))
    (finiteStandardModule_isCountablyGenerated_nonunital (B := C) (ι := ι)) e
    (oddFredholmModuleFibreUnitary (B := C) (X := unitInterval)
      (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (0 : unitInterval) U)
    (oddFredholmModuleFibreUnitary_compact (B := C) (X := unitInterval)
      (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (0 : unitInterval) U hU)
  let v : MatrixUnitary (Unitization ℂ C) ι :=
    matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
      (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u
  let hv : unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ C)) = 1 :=
    oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu
  have he : oddKTheoryTransportOperatorUnitary (B := C)
      (E := HilbertModuleFibre C
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
        (0 : unitInterval)) (F := FiniteStandardModule C ι) e
      (oddFredholmModuleFibreUnitary (B := C) (X := unitInterval)
        (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
        (0 : unitInterval) U) = oddKTheoryMatrixOperatorUnitary (B := C) (ι := ι) v :=
    coefficientImageFiniteZeroFibreEquiv_unitary (B := B) (C := C) (ι := ι) f u
  have htransport' : OddKasparovCycleIso
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (B := C)
        (E := HilbertModuleFibre C
          (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (0 : unitInterval))
        (hJ.fibre (B := C) (X := unitInterval)
          (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (0 : unitInterval))
        (oddFredholmModuleFibreUnitary (B := C) (X := unitInterval)
          (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (0 : unitInterval) U)
        (oddFredholmModuleFibreUnitary_compact (B := C) (X := unitInterval)
          (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (0 : unitInterval) U hU))
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (B := C)
        (E := FiniteStandardModule C ι)
        (finiteStandardModule_isCountablyGenerated_nonunital (B := C) (ι := ι))
        (oddKTheoryMatrixOperatorUnitary (B := C) (ι := ι) v)
        (oddKTheoryMatrixOperatorUnitary_compact (B := C) (ι := ι) v hv)) := by
    simpa only [he] using htransport
  exact (oddFredholmCompactUnitaryPullbackFibreIso (B := C) (X := unitInterval)
    (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
    (0 : unitInterval) hJ U hU).trans
      (htransport'.trans (oddKTheoryMatrixCompactPullbackCycleIso (B := C) (ι := ι) v hv).symm)

set_option maxHeartbeats 4000000 in
def coefficientImageFiniteIntervalOneIso (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycleIso (Γ := PUnit) (A := ℂ) (B := C)
      (E := HilbertModuleFibre C
        (CountableHilbertModuleSum C(unitInterval, C)
          (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι))
        (1 : unitInterval))
      (F := CountableHilbertModuleSum C (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι))
      ((coefficientImageFiniteIntervalUnitaryCycle (B := B) (C := C) (ι := ι) f u hu).fibre
        (Γ := PUnit) (A := ℂ) (B := C) (X := unitInterval)
        (M := CountableHilbertModuleSum C(unitInterval, C)
          (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι))
        (1 : unitInterval))
      (coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu) := by
  let hJ : IsCountablyGeneratedModule C(unitInterval, C)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) :=
    finiteHilbertModuleSum_countablyGenerated (B := C(unitInterval, C))
      (E := CoefficientImageIntervalModule f) (ι := ι)
      (coefficientImageIntervalModule_countablyGenerated (B := B) (C := C) f)
  let hI : IsCountablyGeneratedModule C (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
    finiteHilbertModuleSum_countablyGenerated (B := C) (E := CoefficientImageRightModule f) (ι := ι)
      (coefficientImageRightModule_countablyGenerated (B := B) (C := C) f)
  let U : unitary (AdjointableMap C(unitInterval, C)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)) :=
    coefficientImageFiniteIntervalUnitary (B := B) (C := C) (ι := ι) f u
  let hU : IsModuleCompact ((U : AdjointableMap C(unitInterval, C)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)) - 1) :=
    coefficientImageFiniteIntervalUnitary_compact (B := B) (C := C) (ι := ι) f u hu
  let e : HilbertModuleEquiv C
      (HilbertModuleFibre C
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
        (1 : unitInterval)) (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
    coefficientImageFiniteOneFibreEquiv (B := B) (C := C) (ι := ι) f
  have htransport := oddKTheoryCompactUnitaryTransportIso (B := C)
    (E := HilbertModuleFibre C
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (1 : unitInterval)) (F := FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι)
    (hJ.fibre (B := C) (X := unitInterval)
      (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (1 : unitInterval)) hI e
    (oddFredholmModuleFibreUnitary (B := C) (X := unitInterval)
      (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (1 : unitInterval) U)
    (oddFredholmModuleFibreUnitary_compact (B := C) (X := unitInterval)
      (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
      (1 : unitInterval) U hU)
  have he : oddKTheoryTransportOperatorUnitary (B := C)
      (E := HilbertModuleFibre C
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
        (1 : unitInterval)) (F := FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) e
      (oddFredholmModuleFibreUnitary (B := C) (X := unitInterval)
        (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
        (1 : unitInterval) U) =
      finiteHilbertModuleCoefficientUnitary (A := B) (B := C)
        (E := CoefficientImageRightModule f) (ι := ι)
        (coefficientImageLeftMul (B := B) (C := C) f) u :=
    coefficientImageFiniteOneFibreEquiv_unitary (B := B) (C := C) (ι := ι) f u
  have htransport' : OddKasparovCycleIso
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (B := C)
        (E := HilbertModuleFibre C
          (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (1 : unitInterval))
        (hJ.fibre (B := C) (X := unitInterval)
          (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (1 : unitInterval))
        (oddFredholmModuleFibreUnitary (B := C) (X := unitInterval)
          (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (1 : unitInterval) U)
        (oddFredholmModuleFibreUnitary_compact (B := C) (X := unitInterval)
          (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
          (1 : unitInterval) U hU))
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (B := C)
        (E := FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) hI
        (finiteHilbertModuleCoefficientUnitary (A := B) (B := C)
          (E := CoefficientImageRightModule f) (ι := ι)
          (coefficientImageLeftMul (B := B) (C := C) f) u)
        (finiteHilbertModuleCoefficientUnitary_compact (A := B) (B := C)
          (E := CoefficientImageRightModule f) (ι := ι)
          (coefficientImageLeftMul (B := B) (C := C) f)
          (coefficientImageLeftMul_isModuleCompact (B := B) (C := C) f) u hu)) := by
    simpa only [he] using htransport
  exact (oddFredholmCompactUnitaryPullbackFibreIso (B := C) (X := unitInterval)
    (M := FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
    (1 : unitInterval) hJ U hU).trans htransport'

set_option maxHeartbeats 4000000 in
/-- The witness uses the actual image interval, with true completed-fibre
unitaries at both endpoints, even for zero and degenerate coefficient maps. -/
def coefficientImageFiniteUnitaryFullHomotopy (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    FullOddKasparovHomotopy (Γ := PUnit) (A := ℂ) (B := C)
      (α := (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ))
      (β := (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C))
      (BundledOddKasparovCycle.of (Γ := PUnit) (A := ℂ) (B := C)
        (E := CountableHilbertModuleSum C (FiniteStandardModule C ι))
        (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (B := C) (ι := ι)
          (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
            (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u)
          (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu)))
      (BundledOddKasparovCycle.of (Γ := PUnit) (A := ℂ) (B := C)
        (E := CountableHilbertModuleSum C (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι))
        (coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu)) where
  intervalCycle := BundledOddKasparovCycle.of (Γ := PUnit) (A := ℂ) (B := C(unitInterval, C))
    (E := CountableHilbertModuleSum C(unitInterval, C)
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι))
    (coefficientImageFiniteIntervalUnitaryCycle (B := B) (C := C) (ι := ι) f u hu)
  sourceIso := coefficientImageFiniteIntervalZeroIso (B := B) (C := C) (ι := ι) f u hu
  targetIso := coefficientImageFiniteIntervalOneIso (B := B) (C := C) (ι := ι) f u hu

theorem oddKTheoryMatrixUnitaryClass_map_eq_imageClass (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    oddKTheoryMatrixUnitaryClass (B := C) (ι := ι)
      (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
        (Unitization.starMap (R := ℂ) (A := B) (B := C) f) u)
      (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu) =
    OddKK.mk (Γ := PUnit) (A := ℂ) (B := C)
      (BundledOddKasparovCycle.of (Γ := PUnit) (A := ℂ) (B := C)
        (E := CountableHilbertModuleSum C (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι))
        (coefficientImageFiniteUnitaryCycle (B := B) (C := C) (ι := ι) f u hu)) :=
  OddKK.mk_eq_of_full (Γ := PUnit) (A := ℂ) (B := C)
    (coefficientImageFiniteUnitaryFullHomotopy (B := B) (C := C) (ι := ι) f u hu)

end BC4lean.KKTheory
