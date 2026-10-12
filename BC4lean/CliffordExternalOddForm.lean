import BC4lean.CliffordExternalOddModule

/-! # The full inner product of the genuine odd external tensor

The completed row tensor retains every matrix entry. On elementary vectors
its form is exactly the graded external form: the odd part of the adjoint
second Clifford coefficient crosses the original coefficient grading. This
identifies the Hilbert-module norm with the actual external tensor norm.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddForm
open scoped InnerProductSpace TensorProduct
open CliffordExternalOddCoordinates

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [formComplete : CompleteSpace H]

local instance cliffordExternalOddFormLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

/-- The complete two-column matrix Gram form before the genuine row rotation. -/
def columnInner (x y : RowCoordinates (C := C) (H := H)) : GradedMatrixMoritaMatrix C :=
  CStarMatrix.ofMatrix !![
    MulOpposite.unop ⟪x.1, y.1⟫_(Cᵐᵒᵖ), MulOpposite.unop ⟪x.1, y.2⟫_(Cᵐᵒᵖ);
    MulOpposite.unop ⟪x.2, y.1⟫_(Cᵐᵒᵖ), MulOpposite.unop ⟪x.2, y.2⟫_(Cᵐᵒᵖ)]

/-- The actual Hilbert-module row unitary preserves all four Gram entries. -/
theorem coordinates_inner_tmul_columns
    (x y : CliffordPairModule C H) (z w : CliffordOne) :
    MulOpposite.unop ⟪coordinates (x ⊗ₜ[ℂ] z), coordinates (y ⊗ₜ[ℂ] w)⟫_
      ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) = columnInner (pureColumns x z) (pureColumns y w) := by
  rw [coordinates_inner, rowCoordinates_tmul, rowCoordinates_tmul]
  simp only [columnInner, HilbertModuleEquiv.inner_map]

omit formComplete in
/-- Every coefficient entry agrees with the genuine graded external form. -/
theorem pureColumns_inner [CompleteSpace H] (x y : CliffordPairModule C H) (z w : CliffordOne) :
    columnInner (pureColumns x z) (pureColumns y w) =
      CliffordExternalOddCoefficient.pureMatrix
        (MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)) (CliffordTwo.evenPart (star z) * w) +
      CliffordExternalOddCoefficient.pureMatrix
        ((MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).2,
          (MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).1)
        (CliffordTwo.oddPart (star z) * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [columnInner, pureColumns, CliffordExternalOddCoefficient.pureMatrix,
      CliffordExternalOddCoefficient.evenCoefficient,
      CliffordExternalOddCoefficient.oddCoefficient,
      CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordTwo.evenPart, CliffordTwo.oddPart, CliffordOne.epsilon,
      CliffordOddPauliRotation.alpha, inner_sum, cliffordPair_inner,
      CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
      Complex.conj_I, smul_smul] <;>
    match_scalars <;> ring_nf <;>
    simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

/-- The genuine completed pairing is the full graded external tensor pairing. -/
theorem coordinates_inner_tmul (x y : CliffordPairModule C H) (z w : CliffordOne) :
    MulOpposite.unop ⟪coordinates (x ⊗ₜ[ℂ] z), coordinates (y ⊗ₜ[ℂ] w)⟫_
      ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      CliffordExternalOddCoefficient.coordinates
        ((MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)) ⊗ₜ[ℂ]
          (CliffordTwo.evenPart (star z) * w) +
        ((MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).2,
          (MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).1) ⊗ₜ[ℂ]
          (CliffordTwo.oddPart (star z) * w)) := by
  rw [coordinates_inner_tmul_columns, pureColumns_inner, map_add,
    CliffordExternalOddCoefficient.coordinates_tmul,
    CliffordExternalOddCoefficient.coordinates_tmul]

end BC4lean.KKTheory.CliffordExternalOddForm
