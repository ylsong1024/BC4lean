import BC4lean.FiniteProjectionOrthogonalK0
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NoncommRing

/-! # The genuine finite Julia recovery projection

For projections p and q the positive compression p-pqp has its actual positive
square root s. The column (s,qp) has initial projection p. Its final projection
is orthogonal to the lower complementary projection 1-q. Their sum is the
finite Julia recovery projection, whose K₀ difference from diag(0,1) is [p]-[q].
-/

noncomputable section
namespace BC4lean.OperatorKTheory
open scoped Matrix

variable {A : Type*} {ι : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι] [DecidableEq ι]

local instance gradeFiniteJuliaRecoverySpectralOrder (D : Type*) [CStarAlgebra D] :
    PartialOrder D := CStarAlgebra.spectralOrder D
local instance gradeFiniteJuliaRecoverySpectralOrderedRing (D : Type*) [CStarAlgebra D] :
    StarOrderedRing D := CStarAlgebra.spectralOrderedRing D

omit [DecidableEq ι] in
local instance gradeFiniteJuliaRecoveryRealFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint := by
  with_unfolding_all
    exact (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
      (A := CStarMatrix ι ι A)).toNonUnitalContinuousFunctionalCalculus

local instance gradeFiniteJuliaRecoveryRealNonnegSpectrum :
    NonnegSpectrumClass ℝ (CStarMatrix ι ι A) := by
  with_unfolding_all
    exact CStarAlgebra.instNonnegSpectrumClass' (A := CStarMatrix ι ι A)

def finiteJuliaCompression (p q : MatrixProjection A ι) : CStarMatrix ι ι A :=
  (p : CStarMatrix ι ι A) - p * q * p

theorem finiteJuliaCompression_nonneg (p q : MatrixProjection A ι) :
    0 ≤ finiteJuliaCompression p q := by
  change 0 ≤ (p : CStarMatrix ι ι A) - p * q * p
  have h := star_left_conjugate_nonneg q.property.one_sub.nonneg
    (p : CStarMatrix ι ι A)
  simpa only [Projection.star_coe, mul_sub, mul_one, sub_mul, Projection.mul_self] using h

def finiteJuliaCompressionRoot (p q : MatrixProjection A ι) : CStarMatrix ι ι A :=
  CFC.sqrt (finiteJuliaCompression p q)

@[simp] theorem finiteJuliaCompressionRoot_star (p q : MatrixProjection A ι) :
    star (finiteJuliaCompressionRoot p q) = finiteJuliaCompressionRoot p q := by
  change star (CFC.sqrt (finiteJuliaCompression p q)) = CFC.sqrt (finiteJuliaCompression p q)
  exact (CFC.sqrt_nonneg (finiteJuliaCompression p q)).isSelfAdjoint.star_eq

theorem finiteJuliaCompressionRoot_square (p q : MatrixProjection A ι) :
    finiteJuliaCompressionRoot p q * finiteJuliaCompressionRoot p q =
      finiteJuliaCompression p q := by
  change CFC.sqrt (finiteJuliaCompression p q) * CFC.sqrt (finiteJuliaCompression p q) =
    finiteJuliaCompression p q
  exact CFC.sqrt_mul_sqrt_self (finiteJuliaCompression p q) (finiteJuliaCompression_nonneg p q)

theorem finiteJuliaCompressionRoot_right_support (p q : MatrixProjection A ι) :
    finiteJuliaCompressionRoot p q * p = finiteJuliaCompressionRoot p q := by
  let s := finiteJuliaCompressionRoot p q
  have ha : finiteJuliaCompression p q * (1 - p) = 0 := by
    change ((p : CStarMatrix ι ι A) - p * q * p) * (1 - p) = 0
    calc
      _ = (p : CStarMatrix ι ι A) * (1 - p) -
        (p * q) * (p * (1 - p)) := by noncomm_ring
      _ = 0 := by rw [p.property.mul_one_sub_self, mul_zero, sub_self]
  have hz : s * (1 - p) = 0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    rw [star_mul, star_sub, star_one, Projection.star_coe, finiteJuliaCompressionRoot_star]
    calc
      ((1 - p) * s) * (s * (1 - p)) = (1 - p) * (s * s) * (1 - p) := by
        simp only [mul_assoc]
      _ = (1 - p) * finiteJuliaCompression p q * (1 - p) := by
        rw [finiteJuliaCompressionRoot_square]
      _ = 0 := by rw [mul_assoc, ha, mul_zero]
  rw [mul_sub, mul_one] at hz
  exact (sub_eq_zero.mp hz).symm

theorem finiteJuliaCompressionRoot_left_support (p q : MatrixProjection A ι) :
    (p : CStarMatrix ι ι A) * finiteJuliaCompressionRoot p q = finiteJuliaCompressionRoot p q := by
  simpa only [star_mul, Projection.star_coe, finiteJuliaCompressionRoot_star] using
    congrArg star (finiteJuliaCompressionRoot_right_support p q)

def finiteJuliaRecoveryPartialIsometry (p q : MatrixProjection A ι) :
    CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks
    (CStarMatrix.ofMatrix.symm (finiteJuliaCompressionRoot p q)) 0
    (projectionMatrix q * projectionMatrix p) 0)

theorem finiteJuliaRecoveryPartialIsometry_initial (p q : MatrixProjection A ι) :
    star (finiteJuliaRecoveryPartialIsometry p q) * finiteJuliaRecoveryPartialIsometry p q =
      matrixBlockSum p (0 : CStarMatrix ι ι A) := by
  let s := CStarMatrix.ofMatrix.symm (finiteJuliaCompressionRoot p q)
  have hs : sᴴ = s := finiteJuliaCompressionRoot_star p q
  have hss : s * s = projectionMatrix p - projectionMatrix p * projectionMatrix q * projectionMatrix p :=
    finiteJuliaCompressionRoot_square p q
  change (Matrix.fromBlocks s (0 : Matrix ι ι A)
    (projectionMatrix q * projectionMatrix p) (0 : Matrix ι ι A))ᴴ *
    Matrix.fromBlocks s 0 (projectionMatrix q * projectionMatrix p) 0 =
      Matrix.fromBlocks (projectionMatrix p) 0 0 0
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul, projectionMatrix_star,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, hs]
  have hprod : (projectionMatrix p * projectionMatrix q) *
      (projectionMatrix q * projectionMatrix p) =
        projectionMatrix p * projectionMatrix q * projectionMatrix p := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (projectionMatrix q)
      (projectionMatrix q) (projectionMatrix p), projectionMatrix_mul]
  rw [hss, hprod, sub_add_cancel]

def finiteJuliaRecoveryRange (p q : MatrixProjection A ι) :
    CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A :=
  finiteJuliaRecoveryPartialIsometry p q * star (finiteJuliaRecoveryPartialIsometry p q)

theorem finiteJuliaRecoveryRange_isStarProjection (p q : MatrixProjection A ι) :
    IsStarProjection (finiteJuliaRecoveryRange p q) := by
  let V := finiteJuliaRecoveryPartialIsometry p q
  have hVp := Projection.right_support
    (projectionBlockSum p (Projection.zero : MatrixProjection A ι)) V
      (finiteJuliaRecoveryPartialIsometry_initial p q)
  change V * matrixBlockSum (p : CStarMatrix ι ι A) (0 : CStarMatrix ι ι A) = V at hVp
  constructor
  · change (V * star V) * (V * star V) = V * star V
    calc
      _ = (V * (star V * V)) * star V := by simp only [mul_assoc]
      _ = (V * matrixBlockSum p (0 : CStarMatrix ι ι A)) * star V := by
        rw [finiteJuliaRecoveryPartialIsometry_initial]
      _ = V * star V := by rw [hVp]
  · change star (V * star V) = V * star V
    rw [star_mul, star_star]

def finiteJuliaRecoveryComplement (q : MatrixProjection A ι) : MatrixProjection A (ι ⊕ ι) :=
  projectionBlockSum (Projection.zero : MatrixProjection A ι) (Projection.complement q)

theorem finiteJuliaRecoveryRange_orthogonal (p q : MatrixProjection A ι) :
    finiteJuliaRecoveryRange p q * finiteJuliaRecoveryComplement q = 0 := by
  have hc : star (finiteJuliaRecoveryPartialIsometry p q) * finiteJuliaRecoveryComplement q = 0 := by
    change (Matrix.fromBlocks
        (CStarMatrix.ofMatrix.symm (finiteJuliaCompressionRoot p q)) (0 : Matrix ι ι A)
        (projectionMatrix q * projectionMatrix p) (0 : Matrix ι ι A))ᴴ *
      Matrix.fromBlocks (0 : Matrix ι ι A) (0 : Matrix ι ι A) (0 : Matrix ι ι A)
        (1 - projectionMatrix q) = 0
    have hq : projectionMatrix q * (1 - projectionMatrix q) = 0 := q.property.mul_one_sub_self
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul,
      projectionMatrix_star, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.mul_assoc, hq,
      Matrix.fromBlocks_zero]
  rw [finiteJuliaRecoveryRange, mul_assoc, hc, mul_zero]

def finiteJuliaRecoveryProjection (p q : MatrixProjection A ι) : MatrixProjection A (ι ⊕ ι) :=
  ⟨finiteJuliaRecoveryRange p q + finiteJuliaRecoveryComplement q,
    (finiteJuliaRecoveryRange_isStarProjection p q).add
      (finiteJuliaRecoveryComplement q).property (finiteJuliaRecoveryRange_orthogonal p q)⟩

theorem finiteJuliaRecoveryProjection_k0 (p q : MatrixProjection A ι) :
    k0Projection (FiniteProjection.ofProjection (finiteJuliaRecoveryProjection p q)) -
      k0Projection (FiniteProjection.ofProjection
        (projectionBlockSum (Projection.zero : MatrixProjection A ι)
          (Projection.one : MatrixProjection A ι))) =
      k0Projection (FiniteProjection.ofProjection p) - k0Projection (FiniteProjection.ofProjection q) := by
  have he : Projection.Equivalent (projectionBlockSum p (Projection.zero : MatrixProjection A ι))
      (⟨finiteJuliaRecoveryRange p q, finiteJuliaRecoveryRange_isStarProjection p q⟩ :
        MatrixProjection A (ι ⊕ ι)) :=
    ⟨finiteJuliaRecoveryPartialIsometry p q, finiteJuliaRecoveryPartialIsometry_initial p q, rfl⟩
  have hEquiv : FiniteProjection.Equivalent
      (FiniteProjection.ofProjection
        (projectionBlockSum p (Projection.zero : MatrixProjection A ι)))
      (FiniteProjection.ofProjection
        (⟨finiteJuliaRecoveryRange p q, finiteJuliaRecoveryRange_isStarProjection p q⟩ :
          MatrixProjection A (ι ⊕ ι))) :=
    (rectEquivalent_iff_equivalent
      (projectionBlockSum p (Projection.zero : MatrixProjection A ι))
      (⟨finiteJuliaRecoveryRange p q, finiteJuliaRecoveryRange_isStarProjection p q⟩ :
        MatrixProjection A (ι ⊕ ι))).mpr he
  have hk := k0Projection_eq_of_equivalent hEquiv
  change k0Projection (FiniteProjection.blockSum (FiniteProjection.ofProjection p)
    (FiniteProjection.ofProjection (Projection.zero : MatrixProjection A ι))) = _ at hk
  rw [k0Projection_blockSum, k0Projection_zero_matrix, add_zero] at hk
  have hadd := k0Projection_orthogonal_add
    (⟨finiteJuliaRecoveryRange p q, finiteJuliaRecoveryRange_isStarProjection p q⟩ :
      MatrixProjection A (ι ⊕ ι)) (finiteJuliaRecoveryComplement q)
    (finiteJuliaRecoveryRange_orthogonal p q)
  change k0Projection (FiniteProjection.ofProjection (finiteJuliaRecoveryProjection p q)) =
    k0Projection (FiniteProjection.ofProjection
      (⟨finiteJuliaRecoveryRange p q, finiteJuliaRecoveryRange_isStarProjection p q⟩ :
        MatrixProjection A (ι ⊕ ι))) +
    k0Projection (FiniteProjection.ofProjection (finiteJuliaRecoveryComplement q)) at hadd
  rw [hadd]
  rw [← hk]
  change _ + k0Projection (FiniteProjection.blockSum
    (FiniteProjection.ofProjection (Projection.zero : MatrixProjection A ι))
    (FiniteProjection.ofProjection (Projection.complement q))) -
      k0Projection (FiniteProjection.blockSum
        (FiniteProjection.ofProjection (Projection.zero : MatrixProjection A ι))
        (FiniteProjection.ofProjection (Projection.one : MatrixProjection A ι))) = _
  rw [k0Projection_blockSum, k0Projection_blockSum, k0Projection_zero_matrix,
    zero_add, zero_add, k0Projection_complement]
  abel

end BC4lean.OperatorKTheory
