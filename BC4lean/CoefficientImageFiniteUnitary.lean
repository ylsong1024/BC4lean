import BC4lean.CoefficientImageFiniteFibreEquiv
import BC4lean.OddFredholmRowFibrePullback
import BC4lean.OddKTheoryMatrixUnitaryClass

/-! # The true image interval for a finite scalar-identity unitary

The finite unitary acts on the actual right interval module. Its compact
defect comes from the actual compact image multipliers. Whole finite and
countable completed fibre unitaries identify both endpoint cycles.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationCoefficientImageFiniteUnitaryLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationCoefficientImageFiniteUnitaryLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationCoefficientImageFiniteUnitaryLocalInstance03 : PartialOrder (Unitization ℂ C) := CStarAlgebra.spectralOrder _
local instance oddContinuationCoefficientImageFiniteUnitaryLocalInstance04 : StarOrderedRing (Unitization ℂ C) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationCoefficientImageFiniteUnitaryLocalInstance05 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance oddContinuationCoefficientImageFiniteUnitaryLocalInstance06 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance oddContinuationCoefficientImageFiniteUnitaryLocalInstance07 : CompleteSpace (FiniteStandardModule C ι) := finiteStandardModule_complete

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C] in
theorem oddKTheoryMatrixMap_scalarIdentity (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    unitizationScalarMatrix (matrixUnitaryMap (Unitization.starMap f) u :
      CStarMatrix ι ι (Unitization ℂ C)) = 1 := by
  change matrixMap (scalarQuotient C)
      (matrixMap (Unitization.starMap f) (u : CStarMatrix ι ι (Unitization ℂ B))) = 1
  rw [← StarAlgHom.comp_apply, ← matrixMap_comp, scalarQuotient_natural]
  exact hu

set_option maxHeartbeats 4000000 in
omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C] in
theorem oddFredholmScalarIdentityUnitaryIndex_map (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    operatorK1Map (A := B) (B := C) f
        (oddFredholmScalarIdentityUnitaryIndex (B := B) (ι := ι) u hu) =
      oddFredholmScalarIdentityUnitaryIndex (B := C) (ι := ι)
        (matrixUnitaryMap (A := Unitization ℂ B) (B := Unitization ℂ C) (ι := ι)
          (Unitization.starMap f) u)
        (oddKTheoryMatrixMap_scalarIdentity (B := B) (C := C) (ι := ι) f u hu) := by
  apply Subtype.ext
  change k1Map (Unitization.starMap f) (K1.of (FiniteUnitary.ofUnitary u)) =
    K1.of (FiniteUnitary.ofUnitary (matrixUnitaryMap (Unitization.starMap f) u))
  exact k1Map_of (Unitization.starMap f) (FiniteUnitary.ofUnitary u)

def coefficientImageFiniteIntervalUnitary (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι) :=
  finiteHilbertModuleCoefficientUnitary (coefficientImageIntervalLeftMul f) u

omit [TopologicalSpace.SeparableSpace C] in
theorem coefficientImageFiniteIntervalUnitary_compact (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    IsModuleCompact ((coefficientImageFiniteIntervalUnitary f u :
      AdjointableMap C(unitInterval, C)
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι)) - 1) := by
  exact finiteHilbertModuleCoefficientUnitary_compact
    (A := B) (B := C(unitInterval, C)) (E := CoefficientImageIntervalModule f) (ι := ι)
    (coefficientImageIntervalLeftMul f)
    (coefficientImageIntervalLeftMul_isModuleCompact f) u hu

theorem coefficientImageFiniteZeroFibreEquiv_unitary (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι) :
    oddKTheoryTransportOperatorUnitary (coefficientImageFiniteZeroFibreEquiv f)
      (oddFredholmModuleFibreUnitary 0 (coefficientImageFiniteIntervalUnitary f u)) =
      oddKTheoryMatrixOperatorUnitary (matrixUnitaryMap (Unitization.starMap f) u) := by
  apply Subtype.ext
  apply AdjointableMap.ext
  intro x
  change coefficientImageFiniteZeroFibreEquiv f
    (hilbertModuleFibreOperator (B := C) 0
      (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) u)
      ((coefficientImageFiniteZeroFibreEquiv f).symm x)) = _
  rw [coefficientImageFiniteZeroFibreEquiv_matrix, HilbertModuleEquiv.apply_symm_apply]
  rfl

theorem coefficientImageFiniteOneFibreEquiv_unitary (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι) :
    oddKTheoryTransportOperatorUnitary (coefficientImageFiniteOneFibreEquiv f)
      (oddFredholmModuleFibreUnitary 1 (coefficientImageFiniteIntervalUnitary f u)) =
      finiteHilbertModuleCoefficientUnitary (coefficientImageLeftMul f) u := by
  apply Subtype.ext
  apply AdjointableMap.ext
  intro x
  change coefficientImageFiniteOneFibreEquiv f
    (hilbertModuleFibreOperator (B := C) 1
      (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) u)
      ((coefficientImageFiniteOneFibreEquiv f).symm x)) = _
  rw [coefficientImageFiniteOneFibreEquiv_matrix, HilbertModuleEquiv.apply_symm_apply]
  rfl

end BC4lean.KKTheory
