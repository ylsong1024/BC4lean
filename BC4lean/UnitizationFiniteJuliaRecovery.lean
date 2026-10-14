import BC4lean.FiniteJuliaProjectionRecovery
import BC4lean.UnitizationRelativeProjectionK0
import BC4lean.UnitizedFiniteMatrixBlocks

/-! # The finite Julia recovery in the actual scalar kernel

Equal complete scalar matrices make the positive compression vanish after the
scalar quotient. Its actual positive root therefore also vanishes there. The
recovered finite projection has exactly the canonical scalar reference.
-/

noncomputable section
open scoped CStarAlgebra
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open scoped Matrix

variable {B : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [Fintype ι] [DecidableEq ι]

local instance standardUnitizationFiniteJuliaRecoveryLocalInstance01 (A : Type*) [CStarAlgebra A] : PartialOrder A := CStarAlgebra.spectralOrder A
local instance standardUnitizationFiniteJuliaRecoveryLocalInstance02 (A : Type*) [CStarAlgebra A] : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem finiteJuliaCompression_scalar_zero
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B)) =
      unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B))) :
    unitizationScalarMatrix (finiteJuliaCompression p q) = 0 := by
  let φ := matrixMap (ι := ι) (scalarQuotient B)
  have hp : IsStarProjection (φ p) := p.property.map φ
  change φ ((p : CStarMatrix ι ι (Unitization ℂ B)) - p * q * p) = 0
  have hφ : φ p = φ q := hScalar
  rw [map_sub, map_mul, map_mul, ← hφ, hp.isIdempotentElem.eq,
    hp.isIdempotentElem.eq, sub_self]

theorem finiteJuliaCompressionRoot_scalar_zero
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B)) =
      unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B))) :
    unitizationScalarMatrix (finiteJuliaCompressionRoot p q) = 0 := by
  let : NonUnitalContinuousFunctionalCalculus ℝ
      (CStarMatrix ι ι (Unitization ℂ B)) IsSelfAdjoint := by
    with_unfolding_all
      exact (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
        (A := CStarMatrix ι ι (Unitization ℂ B))).toNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι (Unitization ℂ B)) := by
    with_unfolding_all
      exact CStarAlgebra.instNonnegSpectrumClass' (A := CStarMatrix ι ι (Unitization ℂ B))
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint := by
    with_unfolding_all
      exact (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
        (A := CStarMatrix ι ι ℂ)).toNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) := by
    with_unfolding_all
      exact CStarAlgebra.instNonnegSpectrumClass' (A := CStarMatrix ι ι ℂ)
  let φ := matrixMap (ι := ι) (scalarQuotient B)
  have hz : φ (finiteJuliaCompression p q) = 0 := finiteJuliaCompression_scalar_zero p q hScalar
  change φ (cfcₙ NNReal.sqrt (finiteJuliaCompression p q)) = 0
  have hφ : Continuous φ :=
    AddMonoidHomClass.continuous_of_bound φ 1 (fun a => by
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a)
  have hmap := φ.toNonUnitalStarAlgHom.map_cfcₙ (R := NNReal) NNReal.sqrt
    (finiteJuliaCompression p q) NNReal.continuous_sqrt.continuousOn NNReal.sqrt_zero hφ
    (finiteJuliaCompression_nonneg p q) (by
      change 0 ≤ φ (finiteJuliaCompression p q)
      rw [hz])
  change φ (cfcₙ NNReal.sqrt (finiteJuliaCompression p q)) =
    cfcₙ NNReal.sqrt (φ (finiteJuliaCompression p q)) at hmap
  rw [hmap, hz]
  simp

theorem finiteJuliaRecoveryProjection_difference_fourBlocks
    (p q : MatrixProjection (Unitization ℂ B) ι) :
    (finiteJuliaRecoveryProjection p q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) -
      matrixBlockSum (0 : CStarMatrix ι ι (Unitization ℂ B)) 1 =
    unitizedFiniteFourBlockMatrix (finiteJuliaCompression p q)
      ((q : CStarMatrix ι ι (Unitization ℂ B)) * p * q - q)
      (finiteJuliaCompressionRoot p q * p * q)
      ((q : CStarMatrix ι ι (Unitization ℂ B)) * p * finiteJuliaCompressionRoot p q) := by
  let s := CStarMatrix.ofMatrix.symm (finiteJuliaCompressionRoot p q)
  have hs : sᴴ = s := finiteJuliaCompressionRoot_star p q
  have hss : s * s = projectionMatrix p - projectionMatrix p * projectionMatrix q * projectionMatrix p :=
    finiteJuliaCompressionRoot_square p q
  have hprod : (projectionMatrix q * projectionMatrix p) *
      (projectionMatrix p * projectionMatrix q) = projectionMatrix q * projectionMatrix p * projectionMatrix q := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (projectionMatrix p)
      (projectionMatrix p) (projectionMatrix q), projectionMatrix_mul]
  change Matrix.fromBlocks s (0 : Matrix ι ι (Unitization ℂ B))
      (projectionMatrix q * projectionMatrix p) 0 *
      (Matrix.fromBlocks s (0 : Matrix ι ι (Unitization ℂ B))
        (projectionMatrix q * projectionMatrix p) 0)ᴴ +
      Matrix.fromBlocks (0 : Matrix ι ι (Unitization ℂ B)) 0 0 (1 - projectionMatrix q) -
      Matrix.fromBlocks (0 : Matrix ι ι (Unitization ℂ B)) 0 0 1 =
    Matrix.fromBlocks (projectionMatrix p - projectionMatrix p * projectionMatrix q * projectionMatrix p)
      (s * projectionMatrix p * projectionMatrix q)
      (projectionMatrix q * projectionMatrix p * s)
      (projectionMatrix q * projectionMatrix p * projectionMatrix q - projectionMatrix q)
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul, projectionMatrix_star,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    add_zero, hs]
  rw [Matrix.fromBlocks_add]
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change (s * s) i j + 0 - 0 =
        (projectionMatrix p - projectionMatrix p * projectionMatrix q * projectionMatrix p) i j
      rw [add_zero, sub_zero, hss]
    | inr j =>
      change (s * (projectionMatrix p * projectionMatrix q)) i j + 0 - 0 =
        (s * projectionMatrix p * projectionMatrix q) i j
      rw [add_zero, sub_zero, Matrix.mul_assoc]
  | inr i =>
    cases j with
    | inl j =>
      change (projectionMatrix q * projectionMatrix p * s) i j + 0 - 0 =
        (projectionMatrix q * projectionMatrix p * s) i j
      rw [add_zero, sub_zero]
    | inr j =>
      change ((projectionMatrix q * projectionMatrix p) *
        (projectionMatrix p * projectionMatrix q)) i j +
          (1 - projectionMatrix q) i j - (1 : Matrix ι ι (Unitization ℂ B)) i j =
        (projectionMatrix q * projectionMatrix p * projectionMatrix q - projectionMatrix q) i j
      rw [hprod]
      change (projectionMatrix q * projectionMatrix p * projectionMatrix q) i j +
        ((1 : Matrix ι ι (Unitization ℂ B)) i j - projectionMatrix q i j) -
          (1 : Matrix ι ι (Unitization ℂ B)) i j =
        (projectionMatrix q * projectionMatrix p * projectionMatrix q) i j - projectionMatrix q i j
      abel

theorem finiteJuliaRecoveryProjection_scalar
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B)) =
      unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B))) :
    unitizationScalarMatrix (finiteJuliaRecoveryProjection p q :
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) =
      matrixBlockSum (0 : CStarMatrix ι ι ℂ) (1 : CStarMatrix ι ι ℂ) := by
  let r := unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B))
  have hr : IsStarProjection r := p.property.map (matrixMap (scalarQuotient B))
  let W : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    CStarMatrix.ofMatrix (Matrix.fromBlocks (0 : Matrix ι ι ℂ) 0
      (CStarMatrix.ofMatrix.symm r) 0)
  have hV : unitizationScalarMatrix (finiteJuliaRecoveryPartialIsometry p q) = W := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg (fun M => M i j) (finiteJuliaCompressionRoot_scalar_zero p q hScalar)
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        change (matrixMap (scalarQuotient B)
          ((q : CStarMatrix ι ι (Unitization ℂ B)) *
            (p : CStarMatrix ι ι (Unitization ℂ B)))) i j = r i j
        rw [map_mul]
        change (unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B)) * r) i j = r i j
        rw [← hScalar, hr.isIdempotentElem.eq]
      | inr j => rfl
  have hC : unitizationScalarMatrix (finiteJuliaRecoveryComplement q :
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) =
      matrixBlockSum (0 : CStarMatrix ι ι ℂ) (1 - r) := by
    have hOne : unitizationScalarMatrix (1 : CStarMatrix ι ι (Unitization ℂ B)) = 1 :=
      map_one (matrixMap (scalarQuotient B))
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change unitizationScalarMatrix (1 - (q : CStarMatrix ι ι (Unitization ℂ B))) i j = (1 - r) i j
        rw [unitizationScalarMatrix_sub, hOne, ← hScalar]
  change unitizationScalarMatrix (finiteJuliaRecoveryRange p q +
    (finiteJuliaRecoveryComplement q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B))) = _
  rw [unitizationScalarMatrix_add, finiteJuliaRecoveryRange,
    unitizationScalarMatrix_mul, unitizationScalarMatrix_star, hV, hC]
  change Matrix.fromBlocks (0 : Matrix ι ι ℂ) 0 (CStarMatrix.ofMatrix.symm r) 0 *
      (Matrix.fromBlocks (0 : Matrix ι ι ℂ) 0 (CStarMatrix.ofMatrix.symm r) 0)ᴴ +
      Matrix.fromBlocks (0 : Matrix ι ι ℂ) 0 0 (1 - CStarMatrix.ofMatrix.symm r) =
    Matrix.fromBlocks (0 : Matrix ι ι ℂ) 0 0 1
  have hrs : (CStarMatrix.ofMatrix.symm r)ᴴ = CStarMatrix.ofMatrix.symm r := hr.isSelfAdjoint.star_eq
  have hrr : CStarMatrix.ofMatrix.symm r * CStarMatrix.ofMatrix.symm r =
      CStarMatrix.ofMatrix.symm r := hr.isIdempotentElem.eq
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    hrs, hrr]
  rw [Matrix.fromBlocks_add]
  congr 1 <;> abel

theorem finiteJuliaRecoveryProjection_relativeK0
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B)) =
      unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B))) :
    unitizationRelativeProjectionK0 (B := B) (ι := ι ⊕ ι)
      (finiteJuliaRecoveryProjection p q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B))
      (matrixBlockSum (0 : CStarMatrix ι ι (Unitization ℂ B))
        (1 : CStarMatrix ι ι (Unitization ℂ B)))
      (finiteJuliaRecoveryProjection p q).property
      (projectionBlockSum (Projection.zero : MatrixProjection (Unitization ℂ B) ι) Projection.one).property
      (by
        rw [finiteJuliaRecoveryProjection_scalar p q hScalar]
        have hOne : unitizationScalarMatrix (1 : CStarMatrix ι ι (Unitization ℂ B)) = 1 :=
          map_one (matrixMap (scalarQuotient B))
        ext i j
        cases i with
        | inl i => cases j <;> rfl
        | inr i =>
          cases j with
          | inl j => rfl
          | inr j => exact (congrArg (fun M => M i j) hOne).symm) =
      unitizationRelativeProjectionK0 (B := B) (ι := ι)
        (p : CStarMatrix ι ι (Unitization ℂ B))
        (q : CStarMatrix ι ι (Unitization ℂ B)) p.property q.property hScalar := by
  apply Subtype.ext
  exact finiteJuliaRecoveryProjection_k0 p q

end BC4lean.KKTheory
