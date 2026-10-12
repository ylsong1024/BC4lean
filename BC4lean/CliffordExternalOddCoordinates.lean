import BC4lean.CliffordOddPauliRotation
import BC4lean.MatrixHilbertModuleCoordinateEmbedding
import BC4lean.CliffordPairModule
import BC4lean.CliffordTwoCoordinates
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Actual coordinates of the odd external Clifford module

The source is the genuine complex algebraic tensor of the original
Cl₁(C)-pair module with Cl₁. The target is the actual completed interior
tensor (H⊕H) ⊗_C Row(M₂(C)). Tensor distributivity, explicit invertible
four-coordinate changes, the genuine Pauli unitary and the proved onto
row-coordinate equivalence give a bijection. The full matrix-valued form
is recorded below; off-diagonal entries are retained.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddCoordinates
open scoped TensorProduct InnerProductSpace

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]

local instance cliffordExternalOddCoordinatesLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

abbrev RowCoordinates := HilbertModuleSum C H H × HilbertModuleSum C H H
abbrev ExternalTensor := CliffordPairModule C H ⊗[ℂ] CliffordOne
abbrev ExternalModule := InteriorModuleTensor (E := HilbertModuleSum C H H)
  (GradedMatrixMoritaRow.leftAction (B := C))

def tensorCoordinates : ExternalTensor (C := C) (H := H) ≃ₗ[ℂ]
    CliffordPairModule C H × CliffordPairModule C H :=
  (TensorProduct.prodRight ℂ ℂ (CliffordPairModule C H) ℂ ℂ).trans
    ((TensorProduct.rid ℂ (CliffordPairModule C H)).prodCongr
      (TensorProduct.rid ℂ (CliffordPairModule C H)))

omit [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H] [CompleteSpace H] in
@[simp] theorem tensorCoordinates_tmul (y : CliffordPairModule C H) (z : CliffordOne) :
    tensorCoordinates (y ⊗ₜ[ℂ] z) = (z.1 • y, z.2 • y) := by
  simp [tensorCoordinates]

def regroup : (CliffordPairModule C H × CliffordPairModule C H) ≃ₗ[ℂ]
    RowCoordinates (C := C) (H := H) where
  toFun x := (sumMk x.1.1 x.2.1, sumMk x.1.2 x.2.2)
  invFun x := ((x.1.fst, x.2.fst), (x.1.snd, x.2.snd))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Repack rotated source pairs into the two actual matrix columns. -/
def repack : RowCoordinates (C := C) (H := H) ≃ₗ[ℂ] RowCoordinates (C := C) (H := H) where
  toFun x := (sumMk x.1.fst x.2.snd, sumMk x.1.snd (-x.2.fst))
  invFun x := (sumMk x.1.fst x.2.fst, sumMk (-x.2.snd) x.1.snd)
  left_inv x := by apply Prod.ext <;> apply Prod.ext <;> simp only [sumMk_fst, sumMk_snd, neg_neg]
  right_inv x := by apply Prod.ext <;> apply Prod.ext <;> simp only [sumMk_fst, sumMk_snd, neg_neg]
  map_add' x y := by
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [WithCStarModule.add_fst, WithCStarModule.add_snd,
        Prod.fst_add, Prod.snd_add, sumMk_fst, sumMk_snd, neg_add]
  map_smul' a x := by
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [WithCStarModule.smul_fst, WithCStarModule.smul_snd,
        Prod.smul_fst, Prod.smul_snd, sumMk_fst, sumMk_snd, smul_neg, RingHom.id_apply]

private theorem alpha_ne_zero : CliffordOddPauliRotation.alpha ≠ 0 := by
  intro h
  have hphase : (1 + Complex.I : ℂ) = 0 := by
    calc
      1 + Complex.I = 2 * CliffordOddPauliRotation.alpha := by
        unfold CliffordOddPauliRotation.alpha
        ring
      _ = 0 := by rw [h, mul_zero]
  have hre := congrArg Complex.re hphase
  norm_num at hre

/-- Actual algebraic tensor coordinates before undoing the row Pauli rotation. -/
def rawCoordinates : ExternalTensor (C := C) (H := H) ≃ₗ[ℂ]
    RowCoordinates (C := C) (H := H) :=
  tensorCoordinates.trans (regroup.trans
    ((CliffordOddPauliRotation.hilbertEquiv.linearIsometryEquiv.toLinearEquiv.prodCongr
      CliffordOddPauliRotation.hilbertEquiv.linearIsometryEquiv.toLinearEquiv).trans
      (repack.trans (LinearEquiv.smulOfNeZero ℂ (RowCoordinates (C := C) (H := H))
        CliffordOddPauliRotation.alpha alpha_ne_zero))))

/-- The actual two matrix columns of an elementary external vector tensor. -/
def pureColumns (y : CliffordPairModule C H) (z : CliffordOne) :
    RowCoordinates (C := C) (H := H) :=
  (sumMk
      ((CliffordOddPauliRotation.alpha *
        (CliffordTwo.evenCoefficient z + Complex.I * CliffordTwo.oddCoefficient z)) • y.1)
      ((CliffordOddPauliRotation.alpha *
        (CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z)) • y.2),
    sumMk
      ((CliffordOddPauliRotation.alpha *
        (CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z)) • y.1)
      ((CliffordOddPauliRotation.alpha *
        (-CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z)) • y.2))

theorem rawCoordinates_tmul (y : CliffordPairModule C H) (z : CliffordOne) :
    rawCoordinates (y ⊗ₜ[ℂ] z) = pureColumns y z := by
  simp only [rawCoordinates, LinearEquiv.trans_apply,
    tensorCoordinates_tmul (C := C) (H := H),
    LinearEquiv.prodCongr_apply]
  change CliffordOddPauliRotation.alpha •
    repack
      (CliffordOddPauliRotation.hilbertEquiv (sumMk (z.1 • y.1) (z.2 • y.1)),
       CliffordOddPauliRotation.hilbertEquiv (sumMk (z.1 • y.2) (z.2 • y.2))) = _
  have hplus : CliffordOddPauliRotation.alpha * z.1 + CliffordOddPauliRotation.beta * z.2 =
      CliffordTwo.evenCoefficient z + Complex.I * CliffordTwo.oddCoefficient z := by
    unfold CliffordOddPauliRotation.alpha CliffordOddPauliRotation.beta
      CliffordTwo.evenCoefficient CliffordTwo.oddCoefficient
    ring
  have hminus : CliffordOddPauliRotation.beta * z.1 + CliffordOddPauliRotation.alpha * z.2 =
      CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z := by
    unfold CliffordOddPauliRotation.alpha CliffordOddPauliRotation.beta
      CliffordTwo.evenCoefficient CliffordTwo.oddCoefficient
    ring
  have hrotation (a b : ℂ) (x : H) :
      CliffordOddPauliRotation.hilbertEquiv (C := C) (H := H) (sumMk (a • x) (b • x)) =
        sumMk ((CliffordOddPauliRotation.alpha * a + CliffordOddPauliRotation.beta * b) • x)
          ((CliffordOddPauliRotation.beta * a + CliffordOddPauliRotation.alpha * b) • x) := by
    rw [CliffordOddPauliRotation.hilbertEquiv_apply]
    apply Prod.ext <;> simp only [sumMk_fst, sumMk_snd, smul_smul, ← add_smul]
  simp only [hrotation, hplus, hminus]
  change CliffordOddPauliRotation.alpha •
      (sumMk ((CliffordTwo.evenCoefficient z + Complex.I * CliffordTwo.oddCoefficient z) • y.1)
        ((CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z) • y.2),
       sumMk ((CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z) • y.1)
        (-((CliffordTwo.evenCoefficient z + Complex.I * CliffordTwo.oddCoefficient z) • y.2))) =
    pureColumns y z
  have hnegative : CliffordOddPauliRotation.alpha *
      (-CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z) =
        -(CliffordOddPauliRotation.alpha *
          (CliffordTwo.evenCoefficient z + Complex.I * CliffordTwo.oddCoefficient z)) := by
    ring
  apply Prod.ext
  · apply Prod.ext
    · change CliffordOddPauliRotation.alpha •
        ((CliffordTwo.evenCoefficient z + Complex.I * CliffordTwo.oddCoefficient z) • y.1) = _
      exact smul_smul _ _ _
    · change CliffordOddPauliRotation.alpha •
        ((CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z) • y.2) = _
      exact smul_smul _ _ _
  · apply Prod.ext
    · change CliffordOddPauliRotation.alpha •
        ((CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z) • y.1) = _
      exact smul_smul _ _ _
    · change CliffordOddPauliRotation.alpha •
        (-((CliffordTwo.evenCoefficient z + Complex.I * CliffordTwo.oddCoefficient z) • y.2)) =
          (CliffordOddPauliRotation.alpha *
            (-CliffordTwo.evenCoefficient z - Complex.I * CliffordTwo.oddCoefficient z)) • y.2
      rw [smul_neg, smul_smul, hnegative, neg_smul]

def rowCoordinates : ExternalTensor (C := C) (H := H) ≃ₗ[ℂ]
    RowCoordinates (C := C) (H := H) :=
  rawCoordinates.trans
    (CliffordOddPauliRotation.hilbertEquiv.symm.linearIsometryEquiv.toLinearEquiv.prodCongr
      CliffordOddPauliRotation.hilbertEquiv.symm.linearIsometryEquiv.toLinearEquiv)

/-- A genuine bijection onto the actual complete matrix-coefficient module. -/
def coordinates : ExternalTensor (C := C) (H := H) ≃ₗ[ℂ]
    ExternalModule (C := C) (H := H) :=
  rowCoordinates.trans MatrixHilbertModuleCoordinateEmbedding.coordinateEquiv.toLinearEquiv

@[simp] theorem coordinates_apply (x : ExternalTensor (C := C) (H := H)) :
    coordinates x = MatrixHilbertModuleCoordinateEmbedding.coordinateSum (rowCoordinates x) := rfl

theorem rowCoordinates_tmul (y : CliffordPairModule C H) (z : CliffordOne) :
    rowCoordinates (y ⊗ₜ[ℂ] z) =
      (CliffordOddPauliRotation.hilbertEquiv.symm (pureColumns y z).1,
       CliffordOddPauliRotation.hilbertEquiv.symm (pureColumns y z).2) := by
  simp only [rowCoordinates, LinearEquiv.trans_apply, rawCoordinates_tmul,
    LinearEquiv.prodCongr_apply]
  rfl

theorem coordinates_surjective : Function.Surjective (coordinates (C := C) (H := H)) :=
  coordinates.surjective

/-- The explicit full coefficient form of the actual external module. -/
theorem coordinates_inner (x y : ExternalTensor (C := C) (H := H)) :
    MulOpposite.unop ⟪coordinates x, coordinates y⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      CStarMatrix.ofMatrix !![
        MulOpposite.unop ⟪(rowCoordinates x).1, (rowCoordinates y).1⟫_(Cᵐᵒᵖ),
        MulOpposite.unop ⟪(rowCoordinates x).1, (rowCoordinates y).2⟫_(Cᵐᵒᵖ);
        MulOpposite.unop ⟪(rowCoordinates x).2, (rowCoordinates y).1⟫_(Cᵐᵒᵖ),
        MulOpposite.unop ⟪(rowCoordinates x).2, (rowCoordinates y).2⟫_(Cᵐᵒᵖ)] :=
  MatrixHilbertModuleCoordinateEmbedding.coordinateSum_inner_matrix
    (rowCoordinates x) (rowCoordinates y)

/-- The actual external norm, inherited through the proved onto full coordinates. -/
def tensorNorm (x : ExternalTensor (C := C) (H := H)) : ℝ := ‖coordinates x‖

theorem tensorNorm_eq_zero_iff (x : ExternalTensor (C := C) (H := H)) :
    tensorNorm x = 0 ↔ x = 0 := by
  rw [tensorNorm, norm_eq_zero]
  constructor
  · intro h
    apply coordinates.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

end BC4lean.KKTheory.CliffordExternalOddCoordinates
