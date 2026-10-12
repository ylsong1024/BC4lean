import BC4lean.CoefficientImageFiniteTensorEquiv
import BC4lean.OddKTheoryCompactUnitaryCoefficientTensor
import BC4lean.OddKTheoryCoefficientImageHomotopy

/-! # Actual finite-unitary inverse cycles extend to their true image modules

The completed finite tensor unitary and the genuine standard image tensor
unitary are composed on whole vectors. Their forced-unitization matrix
intertwining identifies the full periodic row inverse coefficient tensor.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationOddKTheoryFiniteCoefficientTensorIsoLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryFiniteCoefficientTensorIsoLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryFiniteCoefficientTensorIsoLocalInstance03 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryFiniteCoefficientTensorIsoLocalInstance04 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  finiteHilbertModuleSum_complete

theorem coefficientImageFiniteTensorEquiv_unitary (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι) :
    oddKTheoryTransportOperatorUnitary (coefficientImageFiniteTensorEquiv f)
      (oddFredholmTensorOperatorUnitary (standardCoefficientImageRepresentation f)
        (oddKTheoryMatrixOperatorUnitary u)) =
      finiteHilbertModuleCoefficientUnitary (coefficientImageLeftMul f) u := by
  apply Subtype.ext
  apply AdjointableMap.ext
  intro x
  change coefficientImageFiniteTensorEquiv f
    (interiorModuleTensorOperator (standardCoefficientImageRepresentation f)
      (unitizedModuleMatrixRepresentation u) ((coefficientImageFiniteTensorEquiv f).symm x)) = _
  rw [coefficientImageFiniteTensorEquiv_matrix, HilbertModuleEquiv.apply_symm_apply]
  rfl

/-- The actual first-factor tensor of the whole finite matrix inverse
cycle is the periodic inverse on the true finite image right module. -/
def oddKTheoryMatrixUnitaryCoefficientTensorIso (f : B →⋆ₙₐ[ℂ] C)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycleIso
      ((oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu).coefficientTensor f)
      (coefficientImageFiniteUnitaryCycle f u hu) := by
  let hE := finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι)
  let U := oddKTheoryMatrixOperatorUnitary u
  let hU := oddKTheoryMatrixOperatorUnitary_compact u hu
  let φ := standardCoefficientImageRepresentation f
  let hTensor := hE.interiorTensor standard_module_isCountablyGenerated φ
  let hImage := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageRightModule_countablyGenerated f)
  have htransport := oddKTheoryCompactUnitaryTransportIso hTensor hImage
    (coefficientImageFiniteTensorEquiv f) (oddFredholmTensorOperatorUnitary φ U)
    (oddFredholmTensorOperatorUnitary_compact f U hU)
  rw [coefficientImageFiniteTensorEquiv_unitary] at htransport
  exact ((oddKTheoryMatrixCompactPullbackCycleIso u hu).coefficientTensor f).trans
    ((oddKTheoryCompactUnitaryCoefficientTensorIso hE U hU f).trans htransport)

end BC4lean.KKTheory
