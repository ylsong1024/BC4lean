import BC4lean.MatrixHilbertModuleCoordinateEmbedding
import BC4lean.ModuleTensorOperator

/-! # Actual matrix action and first-factor operators in row coordinates

The full matrix Gram form determines the actual right matrix action on
both coordinates. First-factor operator compatibility follows on coefficient
approximate-unit vectors from genuine pure tensor formulas and passes to
all vectors by strong convergence. No identity coefficient is used.
-/

noncomputable section
namespace BC4lean.KKTheory.MatrixRowCoordinateAction
open scoped InnerProductSpace Topology
open MatrixHilbertModuleCoordinateEmbedding

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]

/-- The genuine completed row coordinates have actual right matrix multiplication. -/
theorem coordinateSum_op_smul (M : GradedMatrixMoritaMatrix C) (x : H × H) :
    MulOpposite.op M • coordinateSum (C := C) (H := H) x =
      coordinateSum (C := C) (H := H)
        (MulOpposite.op (M 0 0) • x.1 + MulOpposite.op (M 1 0) • x.2,
         MulOpposite.op (M 0 1) • x.1 + MulOpposite.op (M 1 1) • x.2) := by
  apply module_inner_ext_right (B := GradedMatrixMoritaMatrix C)
  intro z
  obtain ⟨y, rfl⟩ := coordinateSum_surjective (C := C) (H := H) z
  apply MulOpposite.unop_injective
  simp only [CStarModule.inner_op_smul_right, MulOpposite.unop_mul,
    MulOpposite.unop_op, coordinateSum_inner_matrix (C := C) (H := H)]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [CStarMatrix.mul_apply, Fin.sum_univ_two,
      CStarModule.inner_add_right (A := Cᵐᵒᵖ) (E := H),
      CStarModule.inner_op_smul_right (A := Cᵐᵒᵖ) (E := H)]

/-- First-factor operators act on the genuine j-th row-module coordinate. -/
theorem operator_coordinate (T : AdjointableMap C H H) (j : Fin 2) (x : H) :
    interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction T (coordinate (C := C) (H := H) j x) =
      coordinate (C := C) (H := H) j (T x) := by
  have hleft :=
    ((interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction T).toCLM.continuous.tendsto
      (coordinate (C := C) (H := H) j x)).comp
      (((coordinate (C := C) (H := H) j).continuous.tendsto x).comp
        (tendsto_coefficient_approximateUnit_smul (D := Cᵐᵒᵖ) x))
  have hright := ((coordinate (C := C) (H := H) j).continuous.tendsto (T x)).comp
    (tendsto_coefficient_approximateUnit_smul (D := Cᵐᵒᵖ) (T x))
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall fun a => by
    change coordinate (C := C) (H := H) j (a • T x) =
      interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction T
        (coordinate (C := C) (H := H) j (a • x))
    calc
      _ = interiorModuleTensorMk (GradedMatrixMoritaRow.leftAction (B := C)) (T x)
          (rowElement (C := C) j a) := coordinate_smul (C := C) (H := H) j a (T x)
      _ = interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction T
          (interiorModuleTensorMk (GradedMatrixMoritaRow.leftAction (B := C)) x
            (rowElement (C := C) j a)) :=
        (interiorModuleTensorOperator_mk (GradedMatrixMoritaRow.leftAction (B := C)) T x
          (rowElement (C := C) j a)).symm
      _ = _ := congrArg (interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction T)
        (coordinate_smul (C := C) (H := H) j a x).symm

theorem operator_coordinateSum (T : AdjointableMap C H H) (x : H × H) :
    interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction T (coordinateSum (C := C) (H := H) x) =
      coordinateSum (C := C) (H := H) (T x.1, T x.2) := by
  simp only [coordinateSum_apply (C := C) (H := H), map_add, operator_coordinate]

end BC4lean.KKTheory.MatrixRowCoordinateAction
