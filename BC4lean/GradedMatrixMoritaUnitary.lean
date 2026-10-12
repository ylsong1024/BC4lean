import BC4lean.GradedMatrixMoritaCompletion

/-! # Grading compatibility of the actual completed Morita unitaries

Both genuine completed contraction unitaries intertwine the actual factor
tensor gradings with the regular coefficient gradings. This establishes graded
module equivalences. No cycle, homotopy-quotient, or Kasparov product equivalence
is inferred here without its additional construction.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

namespace GradedMatrixMoritaUnitary

section RegularGrading

variable {C : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

def regularGrading (δ : CStarGrading C) : GradedHilbertModule δ Cᵐᵒᵖ where
  grading :=
    { toLinearEquiv :=
        { toFun := opStarAlgEquiv δ.automorphism
          invFun := (opStarAlgEquiv δ.automorphism).symm
          left_inv := (opStarAlgEquiv δ.automorphism).symm_apply_apply
          right_inv := (opStarAlgEquiv δ.automorphism).apply_symm_apply
          map_add' := map_add _
          map_smul' := map_smul _ }
      norm_map' x := StarAlgEquiv.norm_map (opStarAlgEquiv δ.automorphism) x }
  involutive x := δ.op_automorphism_sq x
  inner_grading x y := by
    apply MulOpposite.unop_injective
    change star (δ.automorphism (MulOpposite.unop x)) * δ.automorphism (MulOpposite.unop y) =
      δ.automorphism (star (MulOpposite.unop x) * MulOpposite.unop y)
    rw [map_mul, map_star]

@[simp] theorem regularGrading_apply (δ : CStarGrading C) (x : Cᵐᵒᵖ) :
    (regularGrading δ).grading x = opStarAlgEquiv δ.automorphism x := rfl

end RegularGrading

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def columnRowTensorGrading : GradedHilbertModule (GradedMatrixMoritaMatrix.grading (B := B))
    (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaRow.leftAction (B := B))) :=
  (GradedMatrixMoritaColumn.grading (B := B)).interiorTensor
    (φ := GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaRow.grading (B := B)) (by
    intro b y
    exact GradedMatrixMoritaRow.leftAction_graded b y)

def rowColumnTensorGrading : GradedHilbertModule (CStarGrading.trivial : CStarGrading B)
    (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B))) :=
  (GradedMatrixMoritaRow.grading (B := B)).interiorTensor
    (φ := GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaColumn.grading (B := B)) (by
    intro M y
    exact GradedMatrixMoritaColumn.leftAction_graded M y)

open GradedMatrixMoritaCompletion GradedMatrixMoritaContractions

/-- The actual outer-product completed unitary intertwines matrix grading. -/
theorem columnRowUnitary_graded
    (u : InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaRow.leftAction (B := B))) :
    columnRowUnitary (B := B) ((columnRowTensorGrading (B := B)).grading u) =
      (regularGrading (GradedMatrixMoritaMatrix.grading (B := B))).grading (columnRowUnitary (B := B) u) := by
  let f := (columnRowCompleted (B := B)).toContinuousLinearMap.comp
    (columnRowTensorGrading (B := B)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let g := ((regularGrading (GradedMatrixMoritaMatrix.grading (B := B))).grading.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (columnRowCompleted (B := B)).toContinuousLinearMap
  have h : f = g := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (φ := GradedMatrixMoritaRow.leftAction (B := B))
    intro x y
    change columnRowCompleted (B := B)
      ((columnRowTensorGrading (B := B)).grading (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaRow.leftAction (B := B)) x y)) =
      (regularGrading (GradedMatrixMoritaMatrix.grading (B := B))).grading
        (columnRowCompleted (B := B) (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaRow.leftAction (B := B)) x y))
    have hgrading : (columnRowTensorGrading (B := B)).grading
        (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
          (GradedMatrixMoritaRow.leftAction (B := B)) x y) =
        interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
          (GradedMatrixMoritaRow.leftAction (B := B))
          ((GradedMatrixMoritaColumn.grading (B := B)).grading x)
          ((GradedMatrixMoritaRow.grading (B := B)).grading y) :=
      GradedHilbertModule.interiorTensor_grading_mk
        (φ := GradedMatrixMoritaRow.leftAction (B := B))
        (GradedMatrixMoritaColumn.grading (B := B))
        (GradedMatrixMoritaRow.grading (B := B))
        (by intro b z; exact GradedMatrixMoritaRow.leftAction_graded b z) x y
    rw [hgrading, columnRowCompleted_mk, columnRowCompleted_mk, regularGrading_apply]
    exact columnRow_graded x y
  exact DFunLike.congr_fun h u

/-- The actual dot-product completed unitary intertwines the trivial B grading. -/
theorem rowColumnUnitary_graded
    (u : InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B))) :
    rowColumnUnitary (B := B) ((rowColumnTensorGrading (B := B)).grading u) = rowColumnUnitary (B := B) u := by
  let f := (rowColumnCompleted (B := B)).toContinuousLinearMap.comp
    (rowColumnTensorGrading (B := B)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : f = (rowColumnCompleted (B := B)).toContinuousLinearMap := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (φ := GradedMatrixMoritaColumn.leftAction (B := B))
    intro x y
    change rowColumnCompleted (B := B)
      ((rowColumnTensorGrading (B := B)).grading (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaColumn.leftAction (B := B)) x y)) =
      rowColumnCompleted (B := B) (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaColumn.leftAction (B := B)) x y)
    have hgrading : (rowColumnTensorGrading (B := B)).grading
        (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
          (GradedMatrixMoritaColumn.leftAction (B := B)) x y) =
        interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
          (GradedMatrixMoritaColumn.leftAction (B := B))
          ((GradedMatrixMoritaRow.grading (B := B)).grading x)
          ((GradedMatrixMoritaColumn.grading (B := B)).grading y) :=
      GradedHilbertModule.interiorTensor_grading_mk
        (φ := GradedMatrixMoritaColumn.leftAction (B := B))
        (GradedMatrixMoritaRow.grading (B := B))
        (GradedMatrixMoritaColumn.grading (B := B))
        (by intro M z; exact GradedMatrixMoritaColumn.leftAction_graded M z) x y
    rw [hgrading, rowColumnCompleted_mk, rowColumnCompleted_mk]
    exact rowColumn_graded x y
  exact DFunLike.congr_fun h u

end GradedMatrixMoritaUnitary
end BC4lean.KKTheory
