import BC4lean.CliffordExternalOddCoordinates
import BC4lean.CliffordExternalOddCoefficient
import BC4lean.MatrixRowCoordinateAction
import Mathlib.Tactic.Module

/-! # The genuine Koszul action on the completed odd external module

The coefficient action is the actual right matrix action on the completed
row tensor. Its elementary tensor formula is the graded external action:
the odd second Clifford factor crosses the original coefficient grading.
The proofs retain all four matrix entries and use no coefficient identity.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddModule
open scoped InnerProductSpace TensorProduct
open CliffordExternalOddCoordinates

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]

local instance cliffordExternalOddModuleLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

private theorem coefficient_sub_smul {C H : Type*} [NonUnitalCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (a b : Cᵐᵒᵖ) (x : H) :
    (a - b) • x = a • x - b • x := by
  apply module_inner_ext_right (B := C)
  intro z
  simp only [CStarModule.inner_op_smul_right, CStarModule.inner_sub_right, sub_mul]

/-- The actual right matrix action, written in the two complete row coordinates. -/
def rightColumns (M : GradedMatrixMoritaMatrix C)
    (x : RowCoordinates (C := C) (H := H)) : RowCoordinates (C := C) (H := H) :=
  (MulOpposite.op (M 0 0) • x.1 + MulOpposite.op (M 1 0) • x.2,
   MulOpposite.op (M 0 1) • x.1 + MulOpposite.op (M 1 1) • x.2)

/-- A genuine coefficient-linear row unitary commutes with column mixing. -/
theorem rightColumns_hilbertEquiv {C H : Type*} [NonUnitalCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (M : GradedMatrixMoritaMatrix C)
    (U : HilbertModuleEquiv C (HilbertModuleSum C H H) (HilbertModuleSum C H H))
    (x : RowCoordinates (C := C) (H := H)) :
    rightColumns M (U x.1, U x.2) =
      (U (rightColumns M x).1, U (rightColumns M x).2) := by
  simp only [rightColumns, HilbertModuleEquiv.map_add, HilbertModuleEquiv.map_op_smul]

/-- Full elementary external action, including the odd crossing sign. -/
theorem pureColumns_right (a : C × C) (z w : CliffordOne)
    (y : CliffordPairModule C H) :
    rightColumns (CliffordExternalOddCoefficient.pureMatrix a w) (pureColumns y z) =
      pureColumns (MulOpposite.op a • y) (CliffordTwo.evenPart z * w) +
        pureColumns (MulOpposite.op (a.2, a.1) • y) (CliffordTwo.oddPart z * w) := by
  have hEvenAction (x : H) :
      MulOpposite.op (CliffordExternalOddCoefficient.evenCoefficient a) • x =
        (2 : ℂ)⁻¹ • (MulOpposite.op a.1 • x + MulOpposite.op a.2 • x) := by
    rw [CliffordExternalOddCoefficient.evenCoefficient, MulOpposite.op_smul,
      module_complex_smul, MulOpposite.op_add, module_add_smul]
  have hOddAction (x : H) :
      MulOpposite.op (CliffordExternalOddCoefficient.oddCoefficient a) • x =
        (2 : ℂ)⁻¹ • (MulOpposite.op a.1 • x - MulOpposite.op a.2 • x) := by
    rw [CliffordExternalOddCoefficient.oddCoefficient, MulOpposite.op_smul,
      module_complex_smul, MulOpposite.op_sub, coefficient_sub_smul]
  have hEvenEven : CliffordTwo.evenCoefficient (CliffordTwo.evenPart z * w) =
      CliffordTwo.evenCoefficient z * CliffordTwo.evenCoefficient w := by
    change ((CliffordTwo.evenCoefficient z * (1 : ℂ)) * w.1 +
      (CliffordTwo.evenCoefficient z * (1 : ℂ)) * w.2) / 2 =
        CliffordTwo.evenCoefficient z * ((w.1 + w.2) / 2)
    ring
  have hEvenOdd : CliffordTwo.oddCoefficient (CliffordTwo.evenPart z * w) =
      CliffordTwo.evenCoefficient z * CliffordTwo.oddCoefficient w := by
    change ((CliffordTwo.evenCoefficient z * (1 : ℂ)) * w.1 -
      (CliffordTwo.evenCoefficient z * (1 : ℂ)) * w.2) / 2 =
        CliffordTwo.evenCoefficient z * ((w.1 - w.2) / 2)
    ring
  have hOddEven : CliffordTwo.evenCoefficient (CliffordTwo.oddPart z * w) =
      CliffordTwo.oddCoefficient z * CliffordTwo.oddCoefficient w := by
    change ((CliffordTwo.oddCoefficient z * (1 : ℂ)) * w.1 +
      (CliffordTwo.oddCoefficient z * (-1 : ℂ)) * w.2) / 2 =
        CliffordTwo.oddCoefficient z * ((w.1 - w.2) / 2)
    ring
  have hOddOdd : CliffordTwo.oddCoefficient (CliffordTwo.oddPart z * w) =
      CliffordTwo.oddCoefficient z * CliffordTwo.evenCoefficient w := by
    change ((CliffordTwo.oddCoefficient z * (1 : ℂ)) * w.1 -
      (CliffordTwo.oddCoefficient z * (-1 : ℂ)) * w.2) / 2 =
        CliffordTwo.oddCoefficient z * ((w.1 + w.2) / 2)
    ring
  have h00 : CliffordExternalOddCoefficient.pureMatrix a w (0 : Fin 2) (0 : Fin 2) =
      CliffordTwo.evenCoefficient w • CliffordExternalOddCoefficient.evenCoefficient a +
        (Complex.I * CliffordTwo.oddCoefficient w) • CliffordExternalOddCoefficient.oddCoefficient a := rfl
  have h01 : CliffordExternalOddCoefficient.pureMatrix a w (0 : Fin 2) (1 : Fin 2) =
      CliffordTwo.evenCoefficient w • CliffordExternalOddCoefficient.oddCoefficient a +
        (-Complex.I * CliffordTwo.oddCoefficient w) • CliffordExternalOddCoefficient.evenCoefficient a := rfl
  have h10 : CliffordExternalOddCoefficient.pureMatrix a w (1 : Fin 2) (0 : Fin 2) =
      CliffordTwo.evenCoefficient w • CliffordExternalOddCoefficient.oddCoefficient a +
        (Complex.I * CliffordTwo.oddCoefficient w) • CliffordExternalOddCoefficient.evenCoefficient a := rfl
  have h11 : CliffordExternalOddCoefficient.pureMatrix a w (1 : Fin 2) (1 : Fin 2) =
      CliffordTwo.evenCoefficient w • CliffordExternalOddCoefficient.evenCoefficient a +
        (-Complex.I * CliffordTwo.oddCoefficient w) • CliffordExternalOddCoefficient.oddCoefficient a := rfl
  change rightColumns (CliffordExternalOddCoefficient.pureMatrix a w)
      (pureColumns (cliffordPairMk (B := C) y.1 y.2) z) =
    pureColumns (cliffordPairMk (B := C)
      (MulOpposite.op a.1 • y.1) (MulOpposite.op a.2 • y.2)) (CliffordTwo.evenPart z * w) +
    pureColumns (cliffordPairMk (B := C)
      (MulOpposite.op a.2 • y.1) (MulOpposite.op a.1 • y.2)) (CliffordTwo.oddPart z * w)
  simp only [rightColumns, h00, h01, h10, h11]
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [pureColumns, cliffordPairMk,
      WithCStarModule.add_fst, WithCStarModule.add_snd,
      WithCStarModule.smul_fst, WithCStarModule.smul_snd,
      Prod.fst_add, Prod.snd_add, sumMk_fst, sumMk_snd]
    simp only [moduleCoefficient_smul_complex, MulOpposite.op_add,
      MulOpposite.op_smul, module_add_smul, module_complex_smul,
      hEvenAction, hOddAction, hEvenEven, hEvenOdd, hOddEven, hOddOdd]
    generalize MulOpposite.op a.1 • y.1 = v11
    generalize MulOpposite.op a.1 • y.2 = v12
    generalize MulOpposite.op a.2 • y.1 = v21
    generalize MulOpposite.op a.2 • y.2 = v22
    match_scalars
  all_goals
    ring_nf
  all_goals
    simp only [Complex.I_sq]
  all_goals
    ring

/-- The proved coordinates realize the actual graded external coefficient action. -/
theorem coordinates_right_tmul (a : C × C) (z w : CliffordOne)
    (y : CliffordPairModule C H) :
    MulOpposite.op (CliffordExternalOddCoefficient.pureMatrix a w) •
      coordinates (y ⊗ₜ[ℂ] z) =
        coordinates ((MulOpposite.op a • y) ⊗ₜ[ℂ] (CliffordTwo.evenPart z * w) +
          (MulOpposite.op (a.2, a.1) • y) ⊗ₜ[ℂ] (CliffordTwo.oddPart z * w)) := by
  rw [coordinates_apply, coordinates_apply, MatrixRowCoordinateAction.coordinateSum_op_smul]
  change MatrixHilbertModuleCoordinateEmbedding.coordinateSum
    (rightColumns (CliffordExternalOddCoefficient.pureMatrix a w)
      (rowCoordinates (y ⊗ₜ[ℂ] z))) = _
  rw [rowCoordinates_tmul, rightColumns_hilbertEquiv]
  rw [pureColumns_right, map_add, rowCoordinates_tmul, rowCoordinates_tmul]
  apply congrArg (MatrixHilbertModuleCoordinateEmbedding.coordinateSum
    (C := C) (H := HilbertModuleSum C H H))
  apply Prod.ext <;>
    simp only [Prod.fst_add, Prod.snd_add, HilbertModuleEquiv.map_add]

/-- The original signed odd operator acts on both genuine matrix columns. -/
theorem pureColumns_signedOperator {C H : Type*} [NonUnitalCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (T : AdjointableMap C H H)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    (sumMap T (-T) (pureColumns y z).1,
      sumMap T (-T) (pureColumns y z).2) =
        pureColumns (cliffordPairMap T (-T) y) z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [pureColumns, sumMap_apply, sumMk_fst, sumMk_snd,
      cliffordPairMap_apply, cliffordPairMk, map_smul,
      AdjointableMap.coe_neg_apply, smul_neg]

/-- Undoing the genuine Pauli row unitary turns the signed operator into σ_y. -/
theorem operator_rotation_symm (T : AdjointableMap C H H)
    (x : HilbertModuleSum C H H) :
    CliffordOddSourceCycle.operator T (CliffordOddPauliRotation.hilbertEquiv.symm x) =
      CliffordOddPauliRotation.hilbertEquiv.symm (sumMap T (-T) x) := by
  apply (CliffordOddPauliRotation.hilbertEquiv (C := C) (H := H)).injective
  calc
    CliffordOddPauliRotation.hilbertEquiv
        (CliffordOddSourceCycle.operator T (CliffordOddPauliRotation.hilbertEquiv.symm x)) =
        sumMap T (-T)
          (CliffordOddPauliRotation.hilbertEquiv
            (CliffordOddPauliRotation.hilbertEquiv.symm x)) :=
      CliffordOddPauliRotation.rotation_operator T
        (CliffordOddPauliRotation.hilbertEquiv.symm x)
    _ = sumMap T (-T) x :=
      congrArg (sumMap T (-T))
        (HilbertModuleEquiv.apply_symm_apply CliffordOddPauliRotation.hilbertEquiv x)
    _ = CliffordOddPauliRotation.hilbertEquiv
        (CliffordOddPauliRotation.hilbertEquiv.symm (sumMap T (-T) x)) :=
      (HilbertModuleEquiv.apply_symm_apply CliffordOddPauliRotation.hilbertEquiv
        (sumMap T (-T) x)).symm

set_option maxHeartbeats 600000 in
/-- The actual completed first-factor operator is the external original operator. -/
theorem coordinates_operator_tmul (T : AdjointableMap C H H)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction
      (CliffordOddSourceCycle.operator T) (coordinates (y ⊗ₜ[ℂ] z)) =
        coordinates ((cliffordPairMap T (-T) y) ⊗ₜ[ℂ] z) := by
  rw [coordinates_apply,
    MatrixRowCoordinateAction.operator_coordinateSum (C := C) (H := HilbertModuleSum C H H),
    coordinates_apply, rowCoordinates_tmul, rowCoordinates_tmul,
    operator_rotation_symm, operator_rotation_symm]
  have h := pureColumns_signedOperator (C := C) (H := H) T y z
  apply congrArg MatrixHilbertModuleCoordinateEmbedding.coordinateSum
  exact congrArg (fun p : RowCoordinates (C := C) (H := H) =>
      (CliffordOddPauliRotation.hilbertEquiv.symm p.1,
        CliffordOddPauliRotation.hilbertEquiv.symm p.2)) h

end BC4lean.KKTheory.CliffordExternalOddModule
