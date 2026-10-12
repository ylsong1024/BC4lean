import BC4lean.CoefficientImageFiniteFibreEquiv
import BC4lean.RelativeProjectionCycleFibre
import BC4lean.RelativeProjectionIntertwiningCycleIso
import BC4lean.KasparovHomotopyGroup

/-! # The genuine image interval for a finite relative projection pair

Equal full scalar matrices give a compact difference on the true finite
image interval module. Its whole relative-cycle fibres identify the mapped
pair on the full target module and the pair on the actual image right
module. This includes zero and degenerate coefficient maps.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance standardCoefficientImageRelativeProjectionHomotopyLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance standardCoefficientImageRelativeProjectionHomotopyLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance standardCoefficientImageRelativeProjectionHomotopyLocalInstance03 : PartialOrder (Unitization ℂ C) := CStarAlgebra.spectralOrder _
local instance standardCoefficientImageRelativeProjectionHomotopyLocalInstance04 : StarOrderedRing (Unitization ℂ C) := CStarAlgebra.spectralOrderedRing _
local instance standardCoefficientImageRelativeProjectionHomotopyLocalInstance05 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance standardCoefficientImageRelativeProjectionHomotopyLocalInstance06 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance standardCoefficientImageRelativeProjectionHomotopyLocalInstance07 : CompleteSpace (FiniteStandardModule C ι) := finiteStandardModule_complete

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C] in
theorem coefficientImageRelativeProjection_scalar_map (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hs : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    ∀ i j, ((matrixProjectionMap (Unitization.starMap f) p).val i j).fst =
      ((matrixProjectionMap (Unitization.starMap f) q).val i j).fst := by
  intro i j
  change (Unitization.starMap f (p.val i j)).fst =
    (Unitization.starMap f (q.val i j)).fst
  calc
    _ = (p.val i j).fst := DFunLike.congr_fun (scalarQuotient_natural f) (p.val i j)
    _ = (q.val i j).fst := hs i j
    _ = _ := (DFunLike.congr_fun (scalarQuotient_natural f) (q.val i j)).symm

def coefficientImageRelativeProjectionCycle (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hs : ∀ i j, (p.val i j).fst = (q.val i j).fst) :=
  relativeProjectionCycle (Γ := PUnit)
    (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) p.val)
    (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) q.val)
    (p.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f)))
    (q.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f)))
    (finiteHilbertModuleCoefficientMatrix_sub_compact _
      (coefficientImageLeftMul_isModuleCompact f) p.val q.val hs)
    (finiteHilbertModuleSum_countablyGenerated (coefficientImageRightModule_countablyGenerated f))

def coefficientImageIntervalRelativeProjectionCycle (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hs : ∀ i j, (p.val i j).fst = (q.val i j).fst) :=
  relativeProjectionCycle (Γ := PUnit)
    (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) p.val)
    (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) q.val)
    (p.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f)))
    (q.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f)))
    (finiteHilbertModuleCoefficientMatrix_sub_compact _
      (coefficientImageIntervalLeftMul_isModuleCompact f) p.val q.val hs)
    (finiteHilbertModuleSum_countablyGenerated (coefficientImageIntervalModule_countablyGenerated f))

def coefficientImageRelativeProjectionZeroIso (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hs : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    KasparovCycleIso ((coefficientImageIntervalRelativeProjectionCycle f p q hs).fibre 0)
      (unitizedRelativeProjectionCycle (Γ := PUnit)
        (matrixProjectionMap (Unitization.starMap f) p) (matrixProjectionMap (Unitization.starMap f) q)
        (coefficientImageRelativeProjection_scalar_map f p q hs)) := by
  let P := finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) p.val
  let Q := finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) q.val
  let hP := p.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f))
  let hQ := q.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f))
  let hc := finiteHilbertModuleCoefficientMatrix_sub_compact _
    (coefficientImageIntervalLeftMul_isModuleCompact f) p.val q.val hs
  let hJ := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageIntervalModule_countablyGenerated f)
  let p' := matrixProjectionMap (Unitization.starMap f) p
  let q' := matrixProjectionMap (Unitization.starMap f) q
  exact (relativeProjectionCycleFibreIso P Q hP hQ hc hJ 0).trans
    (relativeProjectionIntertwiningCycleIso (Γ := PUnit) (coefficientImageFiniteZeroFibreEquiv f)
      (hilbertModuleFibreOperator (B := C) (X := unitInterval) 0 P) (hilbertModuleFibreOperator (B := C) (X := unitInterval) 0 Q)
      (unitizedProjectionOperator p') (unitizedProjectionOperator q')
      (hP.map (hilbertModuleFibreOperatorHom (B := C) (X := unitInterval) 0)) (hQ.map (hilbertModuleFibreOperatorHom (B := C) (X := unitInterval) 0))
      (unitizedProjectionOperator_isStarProjection p') (unitizedProjectionOperator_isStarProjection q')
      (relativeProjectionFibre_difference_compact P Q hc 0)
      (unitizedModuleMatrixRepresentation_sub_isModuleCompact p'.val q'.val
        (coefficientImageRelativeProjection_scalar_map f p q hs))
      (hJ.fibre 0) finiteStandardModule_isCountablyGenerated_nonunital
      (coefficientImageFiniteZeroFibreEquiv_matrix f p.val)
      (coefficientImageFiniteZeroFibreEquiv_matrix f q.val))

def coefficientImageRelativeProjectionOneIso (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hs : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    KasparovCycleIso ((coefficientImageIntervalRelativeProjectionCycle f p q hs).fibre 1)
      (coefficientImageRelativeProjectionCycle f p q hs) := by
  let P := finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) p.val
  let Q := finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) q.val
  let hP := p.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f))
  let hQ := q.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f))
  let hc := finiteHilbertModuleCoefficientMatrix_sub_compact _
    (coefficientImageIntervalLeftMul_isModuleCompact f) p.val q.val hs
  let hJ := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageIntervalModule_countablyGenerated f)
  let hI := finiteHilbertModuleSum_countablyGenerated
    (ι := ι) (coefficientImageRightModule_countablyGenerated f)
  exact (relativeProjectionCycleFibreIso P Q hP hQ hc hJ 1).trans
    (relativeProjectionIntertwiningCycleIso (Γ := PUnit) (coefficientImageFiniteOneFibreEquiv f)
      (hilbertModuleFibreOperator (B := C) (X := unitInterval) 1 P) (hilbertModuleFibreOperator (B := C) (X := unitInterval) 1 Q)
      (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) p.val)
      (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) q.val)
      (hP.map (hilbertModuleFibreOperatorHom (B := C) (X := unitInterval) 1)) (hQ.map (hilbertModuleFibreOperatorHom (B := C) (X := unitInterval) 1))
      (p.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f)))
      (q.property.map (finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f)))
      (relativeProjectionFibre_difference_compact P Q hc 1)
      (finiteHilbertModuleCoefficientMatrix_sub_compact _
        (coefficientImageLeftMul_isModuleCompact f) p.val q.val hs)
      (hJ.fibre 1) hI (coefficientImageFiniteOneFibreEquiv_matrix f p.val)
      (coefficientImageFiniteOneFibreEquiv_matrix f q.val))

def coefficientImageRelativeProjectionFullHomotopy (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hs : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    FullKasparovHomotopy
      (BundledKasparovCycle.of (unitizedRelativeProjectionCycle (Γ := PUnit)
        (matrixProjectionMap (Unitization.starMap f) p) (matrixProjectionMap (Unitization.starMap f) q)
        (coefficientImageRelativeProjection_scalar_map f p q hs)))
      (BundledKasparovCycle.of (coefficientImageRelativeProjectionCycle f p q hs)) where
  intervalCycle := BundledKasparovCycle.of (coefficientImageIntervalRelativeProjectionCycle f p q hs)
  sourceIso := coefficientImageRelativeProjectionZeroIso f p q hs
  targetIso := coefficientImageRelativeProjectionOneIso f p q hs

theorem coefficientImageRelativeProjection_class (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hs : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of (unitizedRelativeProjectionCycle (Γ := PUnit)
      (matrixProjectionMap (Unitization.starMap f) p) (matrixProjectionMap (Unitization.starMap f) q)
      (coefficientImageRelativeProjection_scalar_map f p q hs))) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of (coefficientImageRelativeProjectionCycle f p q hs)) :=
  KasparovHomotopyClass.mk_eq_of_full (coefficientImageRelativeProjectionFullHomotopy f p q hs)

end BC4lean.KKTheory
