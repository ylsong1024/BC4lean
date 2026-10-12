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
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :=
  oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
    (finiteHilbertModuleSum_countablyGenerated (coefficientImageRightModule_countablyGenerated f))
    (finiteHilbertModuleCoefficientUnitary (coefficientImageLeftMul f) u)
    (finiteHilbertModuleCoefficientUnitary_compact _ (coefficientImageLeftMul_isModuleCompact f) u hu)

def coefficientImageFiniteIntervalUnitaryCycle (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :=
  oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
    (finiteHilbertModuleSum_countablyGenerated (coefficientImageIntervalModule_countablyGenerated f))
    (coefficientImageFiniteIntervalUnitary f u) (coefficientImageFiniteIntervalUnitary_compact f u hu)

def coefficientImageFiniteIntervalZeroIso (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycleIso ((coefficientImageFiniteIntervalUnitaryCycle f u hu).fibre 0)
      (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (matrixUnitaryMap (Unitization.starMap f) u)
        (oddKTheoryMatrixMap_scalarIdentity f u hu)) := by
  let hJ := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageIntervalModule_countablyGenerated f)
  let U := coefficientImageFiniteIntervalUnitary f u
  let hU := coefficientImageFiniteIntervalUnitary_compact f u hu
  let e := coefficientImageFiniteZeroFibreEquiv (ι := ι) f
  have htransport := oddKTheoryCompactUnitaryTransportIso (hJ.fibre 0)
    finiteStandardModule_isCountablyGenerated_nonunital e
    (oddFredholmModuleFibreUnitary 0 U) (oddFredholmModuleFibreUnitary_compact 0 U hU)
  rw [coefficientImageFiniteZeroFibreEquiv_unitary] at htransport
  exact (oddFredholmCompactUnitaryPullbackFibreIso 0 hJ U hU).trans
    (htransport.trans (oddKTheoryMatrixCompactPullbackCycleIso _
      (oddKTheoryMatrixMap_scalarIdentity f u hu)).symm)

def coefficientImageFiniteIntervalOneIso (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycleIso ((coefficientImageFiniteIntervalUnitaryCycle f u hu).fibre 1)
      (coefficientImageFiniteUnitaryCycle f u hu) := by
  let hJ := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageIntervalModule_countablyGenerated f)
  let hI := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageRightModule_countablyGenerated f)
  let U := coefficientImageFiniteIntervalUnitary f u
  let hU := coefficientImageFiniteIntervalUnitary_compact f u hu
  let e := coefficientImageFiniteOneFibreEquiv (ι := ι) f
  have htransport := oddKTheoryCompactUnitaryTransportIso (hJ.fibre 1) hI e
    (oddFredholmModuleFibreUnitary 1 U) (oddFredholmModuleFibreUnitary_compact 1 U hU)
  rw [coefficientImageFiniteOneFibreEquiv_unitary] at htransport
  exact (oddFredholmCompactUnitaryPullbackFibreIso 1 hJ U hU).trans htransport

/-- The witness uses the actual image interval, with true completed-fibre
unitaries at both endpoints, even for zero and degenerate coefficient maps. -/
def coefficientImageFiniteUnitaryFullHomotopy (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    FullOddKasparovHomotopy
      (BundledOddKasparovCycle.of
        (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) (matrixUnitaryMap (Unitization.starMap f) u)
          (oddKTheoryMatrixMap_scalarIdentity f u hu)))
      (BundledOddKasparovCycle.of (coefficientImageFiniteUnitaryCycle f u hu)) where
  intervalCycle := BundledOddKasparovCycle.of (coefficientImageFiniteIntervalUnitaryCycle f u hu)
  sourceIso := coefficientImageFiniteIntervalZeroIso f u hu
  targetIso := coefficientImageFiniteIntervalOneIso f u hu

theorem oddKTheoryMatrixUnitaryClass_map_eq_imageClass (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    oddKTheoryMatrixUnitaryClass (matrixUnitaryMap (Unitization.starMap f) u)
      (oddKTheoryMatrixMap_scalarIdentity f u hu) =
    OddKK.mk (BundledOddKasparovCycle.of (coefficientImageFiniteUnitaryCycle f u hu)) :=
  OddKK.mk_eq_of_full (coefficientImageFiniteUnitaryFullHomotopy f u hu)

end BC4lean.KKTheory
