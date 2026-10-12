import BC4lean.RectangularEquivalence
import Mathlib.Tactic.NoncommRing

/-! # An explicit unitary from a projection partial isometry

The doubled Halmos matrix is constructed from an actual Murray--von Neumann
witness. Its unitarity and conjugation identity are proved by block matrix
multiplication and the support equations derived from the C*-identity.
-/

noncomputable section
namespace BC4lean.OperatorKTheory
open scoped Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation by an actual matrix unitary preserves projection equations. -/
def unitaryProjectionConjugate (w : unitary (CStarMatrix ι ι A)) (p : MatrixProjection A ι) :
    MatrixProjection A ι :=
  ⟨(w : CStarMatrix ι ι A) * p.val * star (w : CStarMatrix ι ι A),
    ⟨by
      calc
        (w.val * p.val * star w.val) * (w.val * p.val * star w.val) =
            w.val * p.val * (star w.val * w.val) * p.val * star w.val := by
          simp only [mul_assoc]
        _ = w.val * p.val * p.val * star w.val := by rw [w.property.1, mul_one]
        _ = w.val * p.val * star w.val := by
          rw [mul_assoc w.val p.val p.val, p.property.isIdempotentElem.eq]
      , by
          change star (w.val * p.val * star w.val) = w.val * p.val * star w.val
          simp only [star_mul, star_star, p.property.isSelfAdjoint.star_eq, mul_assoc]⟩⟩

theorem unitaryProjectionConjugate_equivalent
    (w : unitary (CStarMatrix ι ι A)) (p : MatrixProjection A ι) :
    Projection.Equivalent p (unitaryProjectionConjugate w p) := by
  refine ⟨w.val * p.val, ?_, ?_⟩
  · calc
      star (w.val * p.val) * (w.val * p.val) = p.val * (star w.val * w.val) * p.val := by
        simp only [star_mul, p.property.isSelfAdjoint.star_eq, mul_assoc]
      _ = p.val := by rw [w.property.1, mul_one, p.property.isIdempotentElem.eq]
  · change (w.val * p.val) * star (w.val * p.val) = w.val * p.val * star w.val
    simp only [star_mul, p.property.isSelfAdjoint.star_eq, mul_assoc]
    rw [← mul_assoc p.val p.val (star w.val), p.property.isIdempotentElem.eq]

def projectionHalmosMatrix (p q : MatrixProjection A ι) (v : CStarMatrix ι ι A) :
    CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm v)
    (1 - projectionMatrix q) (1 - projectionMatrix p)
    (-(CStarMatrix.ofMatrix.symm v)ᴴ))

theorem projectionHalmosMatrix_star_mul_self (p q : MatrixProjection A ι)
    (v : CStarMatrix ι ι A) (hvp : star v * v = p.val) (hvq : v * star v = q.val) :
    star (projectionHalmosMatrix p q v) * projectionHalmosMatrix p q v = 1 := by
  let V := CStarMatrix.ofMatrix.symm v
  have hP : Vᴴ * V = projectionMatrix p := hvp
  have hQ : V * Vᴴ = projectionMatrix q := hvq
  have hVP : V * projectionMatrix p = V := Projection.right_support p v hvp
  have hVQ : Vᴴ * projectionMatrix q = Vᴴ :=
    Projection.right_support q (star v) (by simpa only [star_star] using hvq)
  have hPV : projectionMatrix p * Vᴴ = Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, projectionMatrix_star,
      Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose hVP
  have hQV : projectionMatrix q * V = V := by
    simpa only [Matrix.conjTranspose_mul, projectionMatrix_star,
      Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose hVQ
  change (Matrix.fromBlocks V (1 - projectionMatrix q) (1 - projectionMatrix p) (-Vᴴ))ᴴ *
    Matrix.fromBlocks V (1 - projectionMatrix q) (1 - projectionMatrix p) (-Vᴴ) = 1
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, projectionMatrix_star, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  apply Eq.trans (b := Matrix.fromBlocks (1 : Matrix ι ι A) 0 0 1)
  · apply Matrix.fromBlocks_inj.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hP]
      noncomm_ring [projectionMatrix_mul p]
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        hPV, hVQ, sub_self, neg_zero, add_zero]
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        hVP, hQV, sub_self, neg_zero, add_zero]
    · rw [hQ]
      noncomm_ring [projectionMatrix_mul q]
  · exact Matrix.fromBlocks_one

theorem projectionHalmosMatrix_mul_star_self (p q : MatrixProjection A ι)
    (v : CStarMatrix ι ι A) (hvp : star v * v = p.val) (hvq : v * star v = q.val) :
    projectionHalmosMatrix p q v * star (projectionHalmosMatrix p q v) = 1 := by
  have hs : star (projectionHalmosMatrix p q v) = projectionHalmosMatrix q p (star v) := by
    have hStar : CStarMatrix.ofMatrix.symm (star v) = (CStarMatrix.ofMatrix.symm v)ᴴ := by
      ext i j
      rfl
    change (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm v)
      (1 - projectionMatrix q) (1 - projectionMatrix p)
      (-(CStarMatrix.ofMatrix.symm v)ᴴ))ᴴ =
      Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (star v))
        (1 - projectionMatrix p) (1 - projectionMatrix q)
        (-(CStarMatrix.ofMatrix.symm (star v))ᴴ)
    rw [hStar]
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, projectionMatrix_star, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose]
  have h := projectionHalmosMatrix_star_mul_self q p (star v)
    (by simpa only [star_star] using hvq) (by simpa only [star_star] using hvp)
  rw [← hs, star_star] at h
  exact h

/-- A genuine doubled matrix unitary, with both inverse equations proved. -/
def projectionHalmosUnitary (p q : MatrixProjection A ι)
    (v : CStarMatrix ι ι A) (hvp : star v * v = p.val) (hvq : v * star v = q.val) :
    unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) :=
  ⟨projectionHalmosMatrix p q v,
    ⟨projectionHalmosMatrix_star_mul_self p q v hvp hvq,
      projectionHalmosMatrix_mul_star_self p q v hvp hvq⟩⟩

/-- The explicit unitary sends the padded initial projection to the padded final one. -/
theorem projectionHalmosMatrix_conjugate (p q : MatrixProjection A ι)
    (v : CStarMatrix ι ι A) (hvp : star v * v = p.val) (hvq : v * star v = q.val) :
    projectionHalmosMatrix p q v * matrixBlockSum p.val 0 *
        star (projectionHalmosMatrix p q v) = matrixBlockSum q.val 0 := by
  let V := CStarMatrix.ofMatrix.symm v
  have hVP : V * projectionMatrix p = V := Projection.right_support p v hvp
  have hQ : V * Vᴴ = projectionMatrix q := hvq
  have hzero : (1 - projectionMatrix p) * projectionMatrix p = 0 := by
    simp only [Matrix.sub_mul, Matrix.one_mul, projectionMatrix_mul, sub_self]
  have hzero' : V * (1 - projectionMatrix p) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_one, hVP, sub_self]
  change (Matrix.fromBlocks V (1 - projectionMatrix q) (1 - projectionMatrix p) (-Vᴴ) :
        Matrix (ι ⊕ ι) (ι ⊕ ι) A) *
      (Matrix.fromBlocks (projectionMatrix p) 0 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) A) *
      (Matrix.fromBlocks V (1 - projectionMatrix q) (1 - projectionMatrix p) (-Vᴴ) :
        Matrix (ι ⊕ ι) (ι ⊕ ι) A)ᴴ =
    (Matrix.fromBlocks (projectionMatrix q) 0 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) A)
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, projectionMatrix_star,
    Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, hVP, hzero, hQ, hzero']

end BC4lean.OperatorKTheory
