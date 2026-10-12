import BC4lean.RelativeProjectionCoefficientTensor
import BC4lean.CoefficientImageFiniteTensorEquiv
import BC4lean.CoefficientImageRelativeProjectionHomotopy

/-! # True finite relative projection coefficient tensor comparison

The actual finite tensor unitary lands in the coefficient image right
module. It intertwines every forced-unitization matrix, including its
scalar identity part. The true supported projection-range tensor units
therefore identify the entire coefficient-extended relative cycle with the
image cycle used in the genuine image-interval homotopy.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance standardUnitizedRelativeProjectionCoefficientTensorLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance standardUnitizedRelativeProjectionCoefficientTensorLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance standardUnitizedRelativeProjectionCoefficientTensorLocalInstance03 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance standardUnitizedRelativeProjectionCoefficientTensorLocalInstance04 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  finiteHilbertModuleSum_complete

def unitizedRelativeProjectionCoefficientTensorIso (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    KasparovCycleIso ((unitizedRelativeProjectionCycle (Γ := PUnit) p q h).scalarCoefficientTensor f)
      (coefficientImageRelativeProjectionCycle f p q h) := by
  let φ := standardCoefficientImageRepresentation f
  let P := unitizedProjectionOperator p
  let Q := unitizedProjectionOperator q
  let hP := unitizedProjectionOperator_isStarProjection p
  let hQ := unitizedProjectionOperator_isStarProjection q
  let hc := unitizedModuleMatrixRepresentation_sub_isModuleCompact p.val q.val h
  let hE := finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι)
  let P' := finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) p.val
  let Q' := finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) q.val
  let hP' := p.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f))
  let hQ' := q.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f))
  let hc' := finiteHilbertModuleCoefficientMatrix_sub_compact _
    (coefficientImageLeftMul_isModuleCompact f) p.val q.val h
  let hI := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageRightModule_countablyGenerated f)
  have hcTensor : IsModuleCompact (interiorModuleTensorOperator φ P - interiorModuleTensorOperator φ Q) := by
    have hh := hc.interiorModuleTensorOperator φ
      (fun b => standardLeftMul_mem_moduleCompact (f b))
    change IsModuleCompact ((interiorModuleTensorOperatorHom φ) (P - Q)) at hh
    simpa only [map_sub, interiorModuleTensorOperatorHom_apply] using hh
  exact (relativeProjectionCoefficientTensorCycleIso f P Q hP hQ hc hE).trans
    (relativeProjectionIntertwiningCycleIso (Γ := PUnit) (coefficientImageFiniteTensorEquiv f)
      (interiorModuleTensorOperator φ P) (interiorModuleTensorOperator φ Q) P' Q'
      (hP.map (interiorModuleTensorOperatorHom φ)) (hQ.map (interiorModuleTensorOperatorHom φ))
      hP' hQ' hcTensor hc' (hE.interiorTensor standard_module_isCountablyGenerated φ) hI
      (coefficientImageFiniteTensorEquiv_matrix f p.val)
      (coefficientImageFiniteTensorEquiv_matrix f q.val))

end BC4lean.KKTheory
