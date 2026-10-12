import BC4lean.CoefficientImageIntervalRepresentation
import BC4lean.FiniteHilbertModuleEquiv

/-! # Whole finite fibres of the true coefficient-image interval module

The completed endpoint fibres of the finite right interval module identify
with the full target finite module at zero and the true image right module
at one. Whole forced-unitization matrix actions intertwine at both endpoints.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationCoefficientImageFiniteFibreEquivLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationCoefficientImageFiniteFibreEquivLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationCoefficientImageFiniteFibreEquivLocalInstance03 : PartialOrder (Unitization ℂ C) := CStarAlgebra.spectralOrder _
local instance oddContinuationCoefficientImageFiniteFibreEquivLocalInstance04 : StarOrderedRing (Unitization ℂ C) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationCoefficientImageFiniteFibreEquivLocalInstance05 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance oddContinuationCoefficientImageFiniteFibreEquivLocalInstance06 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  finiteHilbertModuleSum_complete
local instance oddContinuationCoefficientImageFiniteFibreEquivLocalInstance07 : CompleteSpace (FiniteStandardModule C ι) := finiteStandardModule_complete

def coefficientImageFiniteZeroFibreEquiv (f : B →⋆ₙₐ[ℂ] C) :
    HilbertModuleEquiv C
      (HilbertModuleFibre C
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) (0 : unitInterval))
      (FiniteStandardModule C ι) :=
  (finiteHilbertModuleFibreEquiv (0 : unitInterval)).trans
    (finiteHilbertModuleEquiv (coefficientImageIntervalZeroFibreEquiv f))

def coefficientImageFiniteOneFibreEquiv (f : B →⋆ₙₐ[ℂ] C) :
    HilbertModuleEquiv C
      (HilbertModuleFibre C
        (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) (1 : unitInterval))
      (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  (finiteHilbertModuleFibreEquiv (1 : unitInterval)).trans
    (finiteHilbertModuleEquiv (coefficientImageIntervalOneFibreEquiv f))

omit [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace C] in
theorem coefficientImageFiniteZeroFibreEquiv_matrix
    [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace C] (f : B →⋆ₙₐ[ℂ] C)
    (M : CStarMatrix ι ι (Unitization ℂ B))
    (z : HilbertModuleFibre C
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) (0 : unitInterval)) :
    coefficientImageFiniteZeroFibreEquiv f
      (hilbertModuleFibreOperator (B := C) (0 : unitInterval)
        (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) M) z) =
    unitizedModuleMatrixRepresentation (matrixMap (Unitization.starMap f) M)
      (coefficientImageFiniteZeroFibreEquiv f z) := by
  let m : ι → ι → Unitization ℂ B := Matrix.of.symm (CStarMatrix.ofMatrix.symm M)
  have hm : CStarMatrix.ofMatrix (Matrix.of m) = M :=
    (congrArg (fun N : Matrix ι ι (Unitization ℂ B) => CStarMatrix.ofMatrix N)
      (Matrix.of.apply_symm_apply (CStarMatrix.ofMatrix.symm M))).trans
        (CStarMatrix.ofMatrix.apply_symm_apply M)
  rw [← hm]
  simp only [coefficientImageFiniteZeroFibreEquiv, HilbertModuleEquiv.trans_apply]
  rw [finiteHilbertModuleFibreEquiv_coefficientMatrix
    (A := B) (B := C) (X := unitInterval) (M := CoefficientImageIntervalModule f) (ι := ι)]
  have he := finiteHilbertModuleEquiv_coefficientMatrix (A := B) (B := C)
    (E := HilbertModuleFibre C (CoefficientImageIntervalModule f) (0 : unitInterval))
    (F := Cᵐᵒᵖ) (ι := ι)
    (coefficientImageIntervalZeroFibreEquiv (B := B) (C := C) f)
    (finiteHilbertModuleFibreRepresentation (A := B) (B := C) (X := unitInterval)
      (M := CoefficientImageIntervalModule f) (0 : unitInterval) (coefficientImageIntervalLeftMul f))
    ((standardLeftMul (B := C)).comp f)
    (coefficientImageIntervalZeroFibreEquiv_leftMul (B := B) (C := C) f)
    (CStarMatrix.ofMatrix (Matrix.of m))
    (finiteHilbertModuleFibreEquiv (B := C) (X := unitInterval)
      (M := CoefficientImageIntervalModule f) (ι := ι) (0 : unitInterval) z)
  refine he.trans ?_
  ext i
  simp only [finiteHilbertModuleCoefficientMatrixHom_apply,
    unitizedModuleMatrixRepresentation_apply, matrixMap_apply,
    CStarMatrix.ofMatrix_apply, Matrix.of_apply]
  have hρ : Unitization.starLift ((standardLeftMul (B := C)).comp f) =
      (unitizedStandardLeftMul (B := C)).comp (Unitization.starMap f) := by
    apply Unitization.starAlgHom_ext
    apply DFunLike.ext
    intro b
    change Unitization.starLift ((standardLeftMul (B := C)).comp f) (Unitization.inr b) =
      unitizedStandardLeftMul (B := C) (Unitization.starMap f (Unitization.inr b))
    rw [Unitization.starMap_inr]
    rfl
  apply Finset.sum_congr rfl
  intro j _
  have hj := DFunLike.congr_fun hρ (m i j)
  exact congrArg (fun T : AdjointableMap C Cᵐᵒᵖ Cᵐᵒᵖ => T.toCLM
    ((finiteHilbertModuleEquiv (B := C)
      (E := HilbertModuleFibre C (CoefficientImageIntervalModule f) (0 : unitInterval))
      (F := Cᵐᵒᵖ) (ι := ι) (coefficientImageIntervalZeroFibreEquiv (B := B) (C := C) f)).linearIsometryEquiv
      ((finiteHilbertModuleFibreEquiv (B := C) (X := unitInterval)
        (M := CoefficientImageIntervalModule f) (ι := ι) (0 : unitInterval)).linearIsometryEquiv z) j)) hj

omit [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace C] in
theorem coefficientImageFiniteOneFibreEquiv_matrix
    [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace C] (f : B →⋆ₙₐ[ℂ] C)
    (M : CStarMatrix ι ι (Unitization ℂ B))
    (z : HilbertModuleFibre C
      (FiniteHilbertModuleSum C(unitInterval, C) (CoefficientImageIntervalModule f) ι) (1 : unitInterval)) :
    coefficientImageFiniteOneFibreEquiv f
      (hilbertModuleFibreOperator (B := C) (1 : unitInterval)
        (finiteHilbertModuleCoefficientMatrixHom (coefficientImageIntervalLeftMul f) M) z) =
    finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) M
      (coefficientImageFiniteOneFibreEquiv f z) := by
  let m : ι → ι → Unitization ℂ B := Matrix.of.symm (CStarMatrix.ofMatrix.symm M)
  have hm : CStarMatrix.ofMatrix (Matrix.of m) = M :=
    (congrArg (fun N : Matrix ι ι (Unitization ℂ B) => CStarMatrix.ofMatrix N)
      (Matrix.of.apply_symm_apply (CStarMatrix.ofMatrix.symm M))).trans
        (CStarMatrix.ofMatrix.apply_symm_apply M)
  rw [← hm]
  simp only [coefficientImageFiniteOneFibreEquiv, HilbertModuleEquiv.trans_apply]
  rw [finiteHilbertModuleFibreEquiv_coefficientMatrix
    (A := B) (B := C) (X := unitInterval) (M := CoefficientImageIntervalModule f) (ι := ι)]
  exact finiteHilbertModuleEquiv_coefficientMatrix (A := B) (B := C) (ι := ι)
    (coefficientImageIntervalOneFibreEquiv f)
    (finiteHilbertModuleFibreRepresentation (A := B) (B := C) (X := unitInterval)
      (M := CoefficientImageIntervalModule f) (1 : unitInterval) (coefficientImageIntervalLeftMul f))
    (coefficientImageLeftMul f) (coefficientImageIntervalOneFibreEquiv_leftMul f)
    (CStarMatrix.ofMatrix (Matrix.of m))
    (finiteHilbertModuleFibreEquiv (B := C) (X := unitInterval)
      (M := CoefficientImageIntervalModule f) (ι := ι) (1 : unitInterval) z)

end BC4lean.KKTheory
