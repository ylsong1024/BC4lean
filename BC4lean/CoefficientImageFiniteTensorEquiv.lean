import BC4lean.FiniteHilbertModuleTensor
import BC4lean.FiniteHilbertModuleEquiv
import BC4lean.FiniteHilbertModuleCoefficientMatrix
import BC4lean.StandardCoefficientImageTensor

/-! # Completed finite coefficient-image tensor equivalence

The finite tensor unitary maps into the true image right module. It preserves
whole coefficient-valued inner products and intertwines forced-unitization
matrix actions. Arbitrary nonunital coefficient homomorphisms are allowed.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationCoefficientImageFiniteTensorEquivLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationCoefficientImageFiniteTensorEquivLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationCoefficientImageFiniteTensorEquivLocalInstance03 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance oddContinuationCoefficientImageFiniteTensorEquivLocalInstance04 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  finiteHilbertModuleSum_complete

def coefficientImageFiniteTensorEquiv (f : B →⋆ₙₐ[ℂ] C) :
    HilbertModuleEquiv C
      (InteriorModuleTensor (E := FiniteStandardModule B ι) (standardCoefficientImageRepresentation f))
      (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) :=
  (finiteHilbertModuleTensorEquiv (standardCoefficientImageRepresentation f)).trans
    (finiteHilbertModuleEquiv (standardCoefficientImageTensorEquiv f))

omit [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] in
theorem standardCoefficientImageTensorEquiv_unitized (f : B →⋆ₙₐ[ℂ] C)
    (a : Unitization ℂ B)
    (z : InteriorModuleTensor (E := Bᵐᵒᵖ) (standardCoefficientImageRepresentation f)) :
    standardCoefficientImageTensorEquiv f
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) (unitizedStandardLeftMul a) z) =
    Unitization.starLift (coefficientImageLeftMul f) a (standardCoefficientImageTensorEquiv f z) := by
  have ha : unitizedStandardLeftMul a = a.fst • 1 + standardLeftMul a.snd := by
    ext x
    rw [unitizedStandardLeftMul_apply]
    rfl
  rw [ha]
  change standardCoefficientImageTensorEquiv f
    (interiorModuleTensorOperatorHom (standardCoefficientImageRepresentation f)
      (a.fst • 1 + standardLeftMul a.snd) z) = _
  rw [map_add, map_smul, map_one]
  change standardCoefficientImageTensorEquiv f
    (a.fst • z + interiorModuleTensorOperator (standardCoefficientImageRepresentation f)
      (standardLeftMul a.snd) z) =
    a.fst • standardCoefficientImageTensorEquiv f z +
      coefficientImageLeftMul f a.snd (standardCoefficientImageTensorEquiv f z)
  rw [HilbertModuleEquiv.map_add, HilbertModuleEquiv.map_smul,
    standardCoefficientImageTensorEquiv_leftMul]

omit [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] in
theorem coefficientImageFiniteTensorEquiv_matrix
    [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] (f : B →⋆ₙₐ[ℂ] C)
    (M : CStarMatrix ι ι (Unitization ℂ B))
    (z : InteriorModuleTensor (E := FiniteStandardModule B ι) (standardCoefficientImageRepresentation f)) :
    coefficientImageFiniteTensorEquiv f
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation f)
        (unitizedModuleMatrixRepresentation M) z) =
    finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f) M
      (coefficientImageFiniteTensorEquiv f z) := by
  let m : ι → ι → Unitization ℂ B := Matrix.of.symm (CStarMatrix.ofMatrix.symm M)
  have hm : CStarMatrix.ofMatrix (Matrix.of m) = M :=
    (congrArg (fun N : Matrix ι ι (Unitization ℂ B) => CStarMatrix.ofMatrix N)
      (Matrix.of.apply_symm_apply (CStarMatrix.ofMatrix.symm M))).trans
        (CStarMatrix.ofMatrix.apply_symm_apply M)
  rw [← hm]
  have hM : unitizedModuleMatrixRepresentation (CStarMatrix.ofMatrix (Matrix.of m)) =
      finiteHilbertModuleOperatorMatrix
        (Matrix.of (fun i j : ι => unitizedStandardLeftMul (m i j))) := by
    ext x i
    rw [unitizedModuleMatrixRepresentation_apply]
    simp only [CStarMatrix.ofMatrix_apply, Matrix.of_apply]
    exact (finiteHilbertModuleOperatorMatrix_apply (B := B) (E := Bᵐᵒᵖ)
      (Matrix.of (fun i j : ι => unitizedStandardLeftMul (m i j))) x i).symm
  change finiteHilbertModuleEquiv (standardCoefficientImageTensorEquiv f)
    (finiteHilbertModuleTensorEquiv (E := Bᵐᵒᵖ) (standardCoefficientImageRepresentation f)
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation f)
        (unitizedModuleMatrixRepresentation (CStarMatrix.ofMatrix (Matrix.of m))) z)) =
    finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f)
      (CStarMatrix.ofMatrix (Matrix.of m))
      (finiteHilbertModuleEquiv (standardCoefficientImageTensorEquiv f)
        (finiteHilbertModuleTensorEquiv (E := Bᵐᵒᵖ) (standardCoefficientImageRepresentation f) z))
  rw [hM]
  have ht := finiteHilbertModuleTensorEquiv_operatorMatrix
    (B := B) (C := C) (E := Bᵐᵒᵖ) (F := Cᵐᵒᵖ) (ι := ι)
    (standardCoefficientImageRepresentation f)
    (Matrix.of (fun i j : ι => unitizedStandardLeftMul (m i j))) z
  calc
    _ = finiteHilbertModuleEquiv (standardCoefficientImageTensorEquiv f)
        (finiteHilbertModuleOperatorMatrix
          (Matrix.of (fun i j : ι =>
            interiorModuleTensorOperator (standardCoefficientImageRepresentation f)
              (unitizedStandardLeftMul (m i j))))
          (finiteHilbertModuleTensorEquiv (E := Bᵐᵒᵖ) (standardCoefficientImageRepresentation f) z)) :=
      congrArg (fun w : FiniteHilbertModuleSum C
        (InteriorModuleTensor (E := Bᵐᵒᵖ) (standardCoefficientImageRepresentation f)) ι =>
          finiteHilbertModuleEquiv (standardCoefficientImageTensorEquiv f) w) ht
    _ = _ := by
      apply (WithCStarModule.equiv Cᵐᵒᵖ (ι → CoefficientImageRightModule f)).injective
      funext i
      change standardCoefficientImageTensorEquiv f
        (finiteHilbertModuleOperatorMatrix
          (Matrix.of (fun i j : ι =>
            interiorModuleTensorOperator (standardCoefficientImageRepresentation f)
              (unitizedStandardLeftMul (m i j))))
          (finiteHilbertModuleTensorEquiv (E := Bᵐᵒᵖ) (standardCoefficientImageRepresentation f) z) i) =
        finiteHilbertModuleCoefficientMatrixHom (coefficientImageLeftMul f)
          (CStarMatrix.ofMatrix (Matrix.of m))
          (finiteHilbertModuleEquiv (standardCoefficientImageTensorEquiv f)
            (finiteHilbertModuleTensorEquiv (E := Bᵐᵒᵖ) (standardCoefficientImageRepresentation f) z)) i
      rw [finiteHilbertModuleOperatorMatrix_apply, finiteHilbertModuleCoefficientMatrixHom_apply]
      simp only [Matrix.of_apply, CStarMatrix.ofMatrix_apply, finiteHilbertModuleEquiv_apply]
      rw [map_sum (standardCoefficientImageTensorEquiv f).linearIsometryEquiv]
      exact Finset.sum_congr rfl (fun _ _ => standardCoefficientImageTensorEquiv_unitized f _ _)

end BC4lean.KKTheory
