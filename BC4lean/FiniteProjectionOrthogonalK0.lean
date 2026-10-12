import BC4lean.OperatorK0

/-! # Actual K₀ addition of orthogonal finite projections

A concrete matrix partial isometry compares the orthogonal sum with the
block sum. The equality is derived in the existing Grothendieck group, without
assuming cancellation in the stable projection monoid.
-/

noncomputable section
namespace BC4lean.OperatorKTheory
open scoped Matrix

variable {A : Type*} {ι : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι] [DecidableEq ι]

theorem k0Projection_zero_matrix :
    k0Projection (FiniteProjection.ofProjection (Projection.zero : MatrixProjection A ι)) = 0 := by
  rw [k0Projection_eq_of_equivalent FiniteProjection.equivalent_zero, k0Projection_zero]

theorem k0Projection_orthogonal_add (p q : MatrixProjection A ι)
    (hpq : (p : CStarMatrix ι ι A) * q = 0) :
    k0Projection (FiniteProjection.ofProjection
      (⟨(p : CStarMatrix ι ι A) + q, p.property.add q.property hpq⟩ : MatrixProjection A ι)) =
      k0Projection (FiniteProjection.ofProjection p) + k0Projection (FiniteProjection.ofProjection q) := by
  let r : MatrixProjection A ι := ⟨(p : CStarMatrix ι ι A) + q, p.property.add q.property hpq⟩
  have hqp : (q : CStarMatrix ι ι A) * p = 0 := by
    simpa only [star_mul, Projection.star_coe, star_zero] using congrArg star hpq
  let W : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A :=
    CStarMatrix.ofMatrix (Matrix.fromBlocks (projectionMatrix p) (projectionMatrix q) 0 0)
  have hW : Projection.Equivalent (projectionBlockSum p q)
      (projectionBlockSum r (Projection.zero : MatrixProjection A ι)) := by
    refine ⟨W, ?_, ?_⟩
    · change (Matrix.fromBlocks (projectionMatrix p) (projectionMatrix q) 0 0 :
        Matrix (ι ⊕ ι) (ι ⊕ ι) A)ᴴ *
        (Matrix.fromBlocks (projectionMatrix p) (projectionMatrix q) 0 0 :
          Matrix (ι ⊕ ι) (ι ⊕ ι) A) =
          (Matrix.fromBlocks (projectionMatrix p) 0 0 (projectionMatrix q) :
            Matrix (ι ⊕ ι) (ι ⊕ ι) A)
      have hpq' : projectionMatrix p * projectionMatrix q = 0 := hpq
      have hqp' : projectionMatrix q * projectionMatrix p = 0 := hqp
      simp only [Matrix.fromBlocks_conjTranspose, projectionMatrix_star,
        Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.zero_mul,
        add_zero, projectionMatrix_mul, hpq', hqp']
    · change (Matrix.fromBlocks (projectionMatrix p) (projectionMatrix q) 0 0 :
        Matrix (ι ⊕ ι) (ι ⊕ ι) A) *
        (Matrix.fromBlocks (projectionMatrix p) (projectionMatrix q) 0 0 :
          Matrix (ι ⊕ ι) (ι ⊕ ι) A)ᴴ =
          (Matrix.fromBlocks (projectionMatrix p + projectionMatrix q) 0 0 0 :
            Matrix (ι ⊕ ι) (ι ⊕ ι) A)
      simp only [Matrix.fromBlocks_conjTranspose, projectionMatrix_star,
        Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.zero_mul,
        Matrix.mul_zero, add_zero, projectionMatrix_mul]
  have hEquiv : FiniteProjection.Equivalent
      (FiniteProjection.blockSum (FiniteProjection.ofProjection p)
        (FiniteProjection.ofProjection q))
      (FiniteProjection.blockSum (FiniteProjection.ofProjection r)
        (FiniteProjection.ofProjection (Projection.zero : MatrixProjection A ι))) :=
    (rectEquivalent_iff_equivalent (projectionBlockSum p q)
      (projectionBlockSum r (Projection.zero : MatrixProjection A ι))).mpr hW
  have hk := k0Projection_eq_of_equivalent hEquiv
  change k0Projection (FiniteProjection.blockSum (FiniteProjection.ofProjection p)
      (FiniteProjection.ofProjection q)) =
    k0Projection (FiniteProjection.blockSum (FiniteProjection.ofProjection r)
      (FiniteProjection.ofProjection (Projection.zero : MatrixProjection A ι))) at hk
  rw [k0Projection_blockSum, k0Projection_blockSum, k0Projection_zero_matrix, add_zero] at hk
  exact hk.symm

theorem k0Projection_complement (p : MatrixProjection A ι) :
    k0Projection (FiniteProjection.ofProjection (Projection.complement p)) =
      k0Projection (FiniteProjection.ofProjection (Projection.one : MatrixProjection A ι)) -
        k0Projection (FiniteProjection.ofProjection p) := by
  have h := k0Projection_orthogonal_add p (Projection.complement p)
    p.property.mul_one_sub_self
  have he : (⟨(p : CStarMatrix ι ι A) + (Projection.complement p : CStarMatrix ι ι A),
      p.property.add (Projection.complement p).property p.property.mul_one_sub_self⟩ :
        MatrixProjection A ι) = Projection.one := by
    apply Subtype.ext
    change (p : CStarMatrix ι ι A) + (1 - p) = 1
    abel
  rw [he] at h
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact h.symm

end BC4lean.OperatorKTheory
