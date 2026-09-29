import BC4lean.UnitaryHomotopy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Block rotation and the inverse homotopy for matrix unitaries

The explicit rotation path gives the inverse mechanism for stable K₁.
The stable quotient and its group structure are separate constructions.
-/

noncomputable section
namespace BC4lean.OperatorKTheory
open scoped Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar block rotation through angle `t`, with identity blocks indexed by `ι`. -/
def rotationMatrix (t : ℝ) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks
    (Real.cos t • (1 : Matrix ι ι A)) (-Real.sin t • (1 : Matrix ι ι A))
    (Real.sin t • (1 : Matrix ι ι A)) (Real.cos t • (1 : Matrix ι ι A)))

omit [PartialOrder A] [StarOrderedRing A] in
theorem rotationMatrix_mem_unitary (t : ℝ) :
    rotationMatrix (A := A) (ι := ι) t ∈ unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) := by
  have h : Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have h' : Real.sin t * Real.sin t + Real.cos t * Real.cos t = 1 := by
    simpa only [add_comm] using h
  rw [Unitary.mem_iff]
  let M : Matrix (ι ⊕ ι) (ι ⊕ ι) A := Matrix.fromBlocks
    (Real.cos t • (1 : Matrix ι ι A)) (-Real.sin t • (1 : Matrix ι ι A))
    (Real.sin t • (1 : Matrix ι ι A)) (Real.cos t • (1 : Matrix ι ι A))
  change (Mᴴ * M = 1) ∧ (M * Mᴴ = 1)
  dsimp [M]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
    star_trivial, Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  constructor <;>
    simp [mul_neg, neg_smul, ← add_smul, h, h', mul_comm, Matrix.fromBlocks_one]

/-- Scalar rotations, bundled as matrix unitaries. -/
def rotationUnitary (t : ℝ) : MatrixUnitary A (ι ⊕ ι) :=
  ⟨rotationMatrix t, rotationMatrix_mem_unitary t⟩

theorem continuous_rotationUnitary :
    Continuous (rotationUnitary (A := A) (ι := ι)) := by
  apply Continuous.subtype_mk
  exact CStarMatrix.ofMatrixL.continuous.comp
    ((Real.continuous_cos.smul continuous_const).matrix_fromBlocks
      (Real.continuous_sin.neg.smul continuous_const)
      (Real.continuous_sin.smul continuous_const)
      (Real.continuous_cos.smul continuous_const))

@[simp] theorem rotationUnitary_zero : rotationUnitary (A := A) (ι := ι) 0 = 1 := by
  apply Subtype.ext
  change rotationMatrix 0 = 1
  simp only [rotationMatrix, Real.cos_zero, Real.sin_zero, neg_zero,
    one_smul, zero_smul, Matrix.fromBlocks_one]
  rfl

@[simp] theorem unitaryBlockSum_one :
    unitaryBlockSum (1 : MatrixUnitary A ι) (1 : MatrixUnitary A ι) = 1 := by
  apply Subtype.ext
  exact matrixBlockSum_one

theorem unitaryBlockSum_mul (u v w z : MatrixUnitary A ι) :
    unitaryBlockSum u v * unitaryBlockSum w z = unitaryBlockSum (u * w) (v * z) := by
  apply Subtype.ext
  change matrixBlockSum (u : CStarMatrix ι ι A) (v : CStarMatrix ι ι A) *
    matrixBlockSum (w : CStarMatrix ι ι A) (z : CStarMatrix ι ι A) =
    matrixBlockSum ((u : CStarMatrix ι ι A) * (w : CStarMatrix ι ι A))
      ((v : CStarMatrix ι ι A) * (z : CStarMatrix ι ι A))
  exact matrixBlockSum_mul (u : CStarMatrix ι ι A) (w : CStarMatrix ι ι A)
    (v : CStarMatrix ι ι A) (z : CStarMatrix ι ι A)

/-- A quarter-turn exchanges diagonal blocks by conjugation. -/
theorem rotationUnitary_conjugate (u v : MatrixUnitary A ι) :
    rotationUnitary (Real.pi / 2) * unitaryBlockSum u v *
      (rotationUnitary (Real.pi / 2))⁻¹ = unitaryBlockSum v u := by
  apply Subtype.ext
  let U : Matrix ι ι A := CStarMatrix.ofMatrix.symm u
  let V : Matrix ι ι A := CStarMatrix.ofMatrix.symm v
  let R : Matrix (ι ⊕ ι) (ι ⊕ ι) A := Matrix.fromBlocks
    (Real.cos (Real.pi / 2) • (1 : Matrix ι ι A))
    (-Real.sin (Real.pi / 2) • (1 : Matrix ι ι A))
    (Real.sin (Real.pi / 2) • (1 : Matrix ι ι A))
    (Real.cos (Real.pi / 2) • (1 : Matrix ι ι A))
  change R * Matrix.fromBlocks U 0 0 V * Rᴴ = Matrix.fromBlocks V 0 0 U
  dsimp [R]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- Rotate the second factor from the lower block into the upper block. -/
def unitaryBlockProductPath (u v : MatrixUnitary A ι) :
    Path (unitaryBlockSum u v) (unitaryBlockSum (u * v) 1) where
  toFun t := unitaryBlockSum u 1 * rotationUnitary ((t : ℝ) * (Real.pi / 2)) *
    unitaryBlockSum 1 v * (rotationUnitary ((t : ℝ) * (Real.pi / 2)))⁻¹
  continuous_toFun := by
    have h : Continuous (fun t : unitInterval =>
        rotationUnitary (A := A) (ι := ι) ((t : ℝ) * (Real.pi / 2))) :=
      continuous_rotationUnitary.comp
      (continuous_subtype_val.mul_const (Real.pi / 2))
    exact ((continuous_const.mul h).mul continuous_const).mul h.inv
  source' := by
    simp [unitaryBlockSum_mul]
  target' := by
    simp only [Set.Icc.coe_one, one_mul]
    rw [mul_assoc (unitaryBlockSum u 1), mul_assoc (unitaryBlockSum u 1),
      rotationUnitary_conjugate]
    simp only [unitaryBlockSum_mul, one_mul]

/-- After doubling the matrix size, block sum agrees with multiplication up to norm homotopy. -/
theorem unitaryHomotopic_blockSum_mul (u v : MatrixUnitary A ι) :
    UnitaryHomotopic (unitaryBlockSum u v) (unitaryBlockSum (u * v) 1) :=
  ⟨unitaryBlockProductPath u v⟩

/-- The block sum of a unitary and its adjoint has an explicit path to the identity. -/
def unitaryInversePath (u : MatrixUnitary A ι) :
    Path (unitaryBlockSum u (star u)) 1 := by
  simpa using unitaryBlockProductPath u (star u)

theorem unitaryHomotopic_blockSum_star (u : MatrixUnitary A ι) :
    UnitaryHomotopic (unitaryBlockSum u (star u)) 1 :=
  ⟨unitaryInversePath u⟩

theorem unitaryHomotopic_star_blockSum (u : MatrixUnitary A ι) :
    UnitaryHomotopic (unitaryBlockSum (star u) u) 1 := by
  simpa using unitaryHomotopic_blockSum_star (star u)

end BC4lean.OperatorKTheory
