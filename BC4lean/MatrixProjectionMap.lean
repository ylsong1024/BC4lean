import BC4lean.StableProjectionMonoid

/-! # Entrywise maps of finite matrix projections

A unital complex ⋆-homomorphism acts on rectangular witnesses entrywise.
Consequently it preserves stable Murray–von Neumann equivalence and block sums.
-/

noncomputable section
open scoped Matrix
namespace BC4lean.OperatorKTheory

universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The entrywise map, bundled on square matrices with the C⋆-matrix norm. -/
def matrixMap (φ : A →⋆ₐ[ℂ] B) : CStarMatrix ι ι A →⋆ₐ[ℂ] CStarMatrix ι ι B :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (({ φ.toAlgHom.mapMatrix with
        map_star' := fun _ => Matrix.conjTranspose_map φ (fun a => map_star φ a) } :
          Matrix ι ι A →⋆ₐ[ℂ] Matrix ι ι B).comp
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

@[simp] theorem matrixMap_apply (φ : A →⋆ₐ[ℂ] B) (M : CStarMatrix ι ι A) (i j : ι) :
    matrixMap φ M i j = φ (M i j) := rfl

@[simp] theorem matrixMap_id :
    matrixMap (ι := ι) (StarAlgHom.id ℂ A) = StarAlgHom.id ℂ (CStarMatrix ι ι A) := by
  ext M i j
  rfl

@[simp] theorem matrixMap_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) :
    matrixMap (ι := ι) (ψ.comp φ) = (matrixMap ψ).comp (matrixMap φ) := by
  ext M i j
  rfl

variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder C] [StarOrderedRing C]

/-- Applying the entrywise homomorphism to a matrix projection. -/
def matrixProjectionMap (φ : A →⋆ₐ[ℂ] B) (p : MatrixProjection A ι) : MatrixProjection B ι :=
  Projection.map (matrixMap φ) p

@[simp] theorem projectionMatrix_map (φ : A →⋆ₐ[ℂ] B) (p : MatrixProjection A ι) :
    projectionMatrix (matrixProjectionMap φ p) = (projectionMatrix p).map φ := rfl

@[simp] theorem matrixProjectionMap_id (p : MatrixProjection A ι) :
    matrixProjectionMap (StarAlgHom.id ℂ A) p = p := by
  apply Subtype.ext
  rfl

@[simp] theorem matrixProjectionMap_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B)
    (p : MatrixProjection A ι) :
    matrixProjectionMap (ψ.comp φ) p = matrixProjectionMap ψ (matrixProjectionMap φ p) := rfl

@[simp] theorem matrixProjectionMap_zero (φ : A →⋆ₐ[ℂ] B) :
    matrixProjectionMap φ (Projection.zero : MatrixProjection A ι) = Projection.zero :=
  Projection.map_zero _

@[simp] theorem matrixProjectionMap_blockSum (φ : A →⋆ₐ[ℂ] B)
    (p : MatrixProjection A ι) (q : MatrixProjection A κ) :
    matrixProjectionMap φ (projectionBlockSum p q) =
      projectionBlockSum (matrixProjectionMap φ p) (matrixProjectionMap φ q) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> simp [matrixProjectionMap, Projection.map,
    matrixMap_apply, projectionBlockSum, matrixBlockSum, Matrix.fromBlocks]

/-- Map the actual rectangular witness; no injectivity of φ is required. -/
theorem rectEquivalent_map (φ : A →⋆ₐ[ℂ] B)
    {p : MatrixProjection A ι} {q : MatrixProjection A κ} (h : RectEquivalent p q) :
    RectEquivalent (matrixProjectionMap φ p) (matrixProjectionMap φ q) := by
  obtain ⟨v, hv, hv'⟩ := h
  refine ⟨v.map φ, ?_, ?_⟩
  · simpa only [Matrix.map_mul, Matrix.conjTranspose_map φ (fun a => map_star φ a),
      projectionMatrix_map] using congrArg (fun M => M.map φ) hv
  · simpa only [Matrix.map_mul, Matrix.conjTranspose_map φ (fun a => map_star φ a),
      projectionMatrix_map] using congrArg (fun M => M.map φ) hv'

namespace FiniteProjection

/-- Entrywise transport keeps the finite index type. -/
def map (φ : A →⋆ₐ[ℂ] B) (p : FiniteProjection A) : FiniteProjection B where
  Index := p.Index
  projection := matrixProjectionMap φ p.projection

@[simp] theorem map_id (p : FiniteProjection A) : map (StarAlgHom.id ℂ A) p = p := by
  cases p
  simp only [map, matrixProjectionMap_id]

@[simp] theorem map_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) (p : FiniteProjection A) :
    map (ψ.comp φ) p = map ψ (map φ p) := rfl

@[simp] theorem map_zero (φ : A →⋆ₐ[ℂ] B) : map φ zero = zero := by
  exact congrArg (fun p : MatrixProjection B Empty => ofProjection p) (matrixProjectionMap_zero φ)

@[simp] theorem map_blockSum (φ : A →⋆ₐ[ℂ] B) (p q : FiniteProjection A) :
    map φ (blockSum p q) = blockSum (map φ p) (map φ q) := by
  exact congrArg (fun r : MatrixProjection B (p.Index ⊕ q.Index) => ofProjection r)
    (matrixProjectionMap_blockSum φ p.projection q.projection)

theorem equivalent_map (φ : A →⋆ₐ[ℂ] B) {p q : FiniteProjection A}
    (h : Equivalent p q) : Equivalent (map φ p) (map φ q) := rectEquivalent_map φ h

end FiniteProjection
end BC4lean.OperatorKTheory
