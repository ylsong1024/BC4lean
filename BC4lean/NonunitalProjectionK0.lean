import BC4lean.NonunitalOperatorK

/-! # A genuine projection in the nonunital operator K₀ group

A projection in a possibly nonunital complex C⋆-algebra gives the singleton
matrix projection in its forced unitization. Its scalar matrix is zero, so its
ordinary projection class lies in the actual scalar kernel defining OperatorK0.
A mixed partial isometry gives equality of these classes by the existing stable
Murray–von Neumann equivalence, without assuming a K-theory invariance law.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

local instance projectionSpectralOrder (B : Type*) [CStarAlgebra B] : PartialOrder B :=
  CStarAlgebra.spectralOrder B
local instance projectionSpectralOrderedRing (B : Type*) [CStarAlgebra B] :
    StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The actual one-by-one matrix of an element inside its forced unitization. -/
def nonunitalProjectionMatrix (p : A) : CStarMatrix PUnit.{1} PUnit.{1} (Unitization ℂ A) :=
  CStarMatrix.ofMatrix fun _ _ => (p : Unitization ℂ A)

omit [NonUnitalCStarAlgebra A] in
@[simp] theorem nonunitalProjectionMatrix_apply (p : A) (i j : PUnit.{1}) :
    nonunitalProjectionMatrix p i j = (p : Unitization ℂ A) := rfl

@[simp] theorem nonunitalProjectionMatrix_star (p : A) :
    star (nonunitalProjectionMatrix p) = nonunitalProjectionMatrix (star p) := by
  apply CStarMatrix.ext
  intro i j
  change star (p : Unitization ℂ A) = ((star p : A) : Unitization ℂ A)
  exact (Unitization.inr_star p).symm

@[simp] theorem nonunitalProjectionMatrix_mul (p q : A) :
    nonunitalProjectionMatrix p * nonunitalProjectionMatrix q =
      nonunitalProjectionMatrix (p * q) := by
  apply CStarMatrix.ext
  intro i j
  change (∑ _ : PUnit.{1}, (p : Unitization ℂ A) * (q : Unitization ℂ A)) =
    ((p * q : A) : Unitization ℂ A)
  simpa only [Fintype.sum_unique] using (Unitization.inr_mul ℂ p q).symm

theorem nonunitalProjectionMatrix_isStarProjection (p : A) (hp : IsStarProjection p) :
    IsStarProjection (nonunitalProjectionMatrix p) := by
  apply isStarProjection_iff'.mpr
  constructor
  · rw [nonunitalProjectionMatrix_mul, hp.isIdempotentElem.eq]
  · rw [nonunitalProjectionMatrix_star, hp.isSelfAdjoint.star_eq]

/-- The singleton matrix projection, retaining its genuine finite index type. -/
def nonunitalFiniteProjection (p : A) (hp : IsStarProjection p) :
    FiniteProjection (Unitization ℂ A) :=
  FiniteProjection.ofProjection
    (⟨nonunitalProjectionMatrix p, nonunitalProjectionMatrix_isStarProjection p hp⟩ :
      MatrixProjection (Unitization ℂ A) PUnit.{1})

/-- The entrywise scalar quotient of this singleton projection is zero. -/
theorem nonunitalFiniteProjection_scalar (p : A) (hp : IsStarProjection p) :
    FiniteProjection.map (scalarQuotient A) (nonunitalFiniteProjection p hp) =
      FiniteProjection.ofProjection (Projection.zero : MatrixProjection ℂ PUnit.{1}) := by
  apply congrArg (FiniteProjection.ofProjection (A := ℂ) (ι := PUnit.{1}))
  apply Subtype.ext
  ext i j
  change (p : Unitization ℂ A).fst = 0
  rfl

/-- The singleton projection class lies in the actual scalar-quotient kernel. -/
theorem nonunitalProjectionK0_scalar_zero (p : A) (hp : IsStarProjection p) :
    k0Map (scalarQuotient A) (k0Projection (nonunitalFiniteProjection p hp)) = 0 := by
  rw [k0Map_projection, nonunitalFiniteProjection_scalar]
  simp only [k0Projection, StableProjectionMonoid.of_zeroProjection, map_zero]

/-- The genuine nonunital K₀ class of an actual projection. -/
def nonunitalProjectionK0 (p : A) (hp : IsStarProjection p) : OperatorK0 A :=
  ⟨k0Projection (nonunitalFiniteProjection p hp), nonunitalProjectionK0_scalar_zero p hp⟩

@[simp] theorem operatorK0Inclusion_nonunitalProjectionK0 (p : A) (hp : IsStarProjection p) :
    operatorK0Inclusion A (nonunitalProjectionK0 p hp) =
      k0Projection (nonunitalFiniteProjection p hp) := rfl

/-- A mixed partial isometry proves equality in the existing K₀ group. -/
theorem nonunitalProjectionK0_eq_of_partialIsometry {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (v : A)
    (hvp : star v * v = p) (hvq : v * star v = q) :
    nonunitalProjectionK0 p hp = nonunitalProjectionK0 q hq := by
  apply Subtype.ext
  apply k0Projection_eq_of_equivalent
  apply (rectEquivalent_iff_equivalent _ _).mpr
  refine ⟨nonunitalProjectionMatrix v, ?_, ?_⟩
  · change star (nonunitalProjectionMatrix v) * nonunitalProjectionMatrix v =
      nonunitalProjectionMatrix p
    rw [nonunitalProjectionMatrix_star, nonunitalProjectionMatrix_mul, hvp]
  · change nonunitalProjectionMatrix v * star (nonunitalProjectionMatrix v) =
      nonunitalProjectionMatrix q
    rw [nonunitalProjectionMatrix_star, nonunitalProjectionMatrix_mul, hvq]

end BC4lean.OperatorKTheory
