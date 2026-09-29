import BC4lean.OperatorK0Functoriality

/-! # Nonunital homomorphisms on the projection definition of unital K₀ -/
noncomputable section
open scoped Matrix
namespace BC4lean.OperatorKTheory
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder C] [StarOrderedRing C]
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def projectionMapNU (φ : A →⋆ₙₐ[ℂ] B) (p : MatrixProjection A ι) : MatrixProjection B ι :=
  ⟨CStarMatrix.ofMatrix ((projectionMatrix p).map φ), ⟨by
    change (projectionMatrix p).map φ * (projectionMatrix p).map φ = (projectionMatrix p).map φ
    rw [← Matrix.map_mul, projectionMatrix_mul], by
    change ((projectionMatrix p).map φ)ᴴ = (projectionMatrix p).map φ
    rw [← Matrix.conjTranspose_map φ (fun x => map_star φ x), projectionMatrix_star]⟩⟩

@[simp] theorem projectionMatrix_mapNU (φ : A →⋆ₙₐ[ℂ] B) (p : MatrixProjection A ι) :
    projectionMatrix (projectionMapNU φ p) = (projectionMatrix p).map φ := rfl

theorem rectEquivalent_mapNU (φ : A →⋆ₙₐ[ℂ] B)
    {p : MatrixProjection A ι} {q : MatrixProjection A κ} (h : RectEquivalent p q) :
    RectEquivalent (projectionMapNU φ p) (projectionMapNU φ q) := by
  obtain ⟨v, hv, hv'⟩ := h
  refine ⟨v.map φ, ?_, ?_⟩
  · simpa only [Matrix.map_mul, Matrix.conjTranspose_map φ (fun a => map_star φ a),
      projectionMatrix_mapNU] using congrArg (fun M => M.map φ) hv
  · simpa only [Matrix.map_mul, Matrix.conjTranspose_map φ (fun a => map_star φ a),
      projectionMatrix_mapNU] using congrArg (fun M => M.map φ) hv'

namespace FiniteProjection

def mapNU (φ : A →⋆ₙₐ[ℂ] B) (p : FiniteProjection A) : FiniteProjection B :=
  ofProjection (projectionMapNU φ p.projection)

@[simp] theorem mapNU_blockSum (φ : A →⋆ₙₐ[ℂ] B) (p q : FiniteProjection A) :
    mapNU φ (blockSum p q) = blockSum (mapNU φ p) (mapNU φ q) := by
  apply congrArg (fun p : MatrixProjection B (p.Index ⊕ q.Index) => ofProjection p)
  apply Subtype.ext
  change (Matrix.fromBlocks (projectionMatrix p.projection) (0 : Matrix p.Index q.Index A)
    (0 : Matrix q.Index p.Index A) (projectionMatrix q.projection)).map φ =
    Matrix.fromBlocks ((projectionMatrix p.projection).map φ) 0 0 ((projectionMatrix q.projection).map φ)
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

@[simp] theorem mapNU_zero (φ : A →⋆ₙₐ[ℂ] B) : mapNU φ zero = zero := by
  apply congrArg (fun p : MatrixProjection B Empty => ofProjection p)
  apply Subtype.ext
  ext i
  exact i.elim

theorem equivalent_mapNU (φ : A →⋆ₙₐ[ℂ] B) {p q : FiniteProjection A} (h : Equivalent p q) :
    Equivalent (mapNU φ p) (mapNU φ q) := rectEquivalent_mapNU φ h

@[simp] theorem mapNU_id (p : FiniteProjection A) : mapNU (NonUnitalStarAlgHom.id ℂ A) p = p := by
  cases p
  rfl

@[simp] theorem mapNU_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) (p : FiniteProjection A) :
    mapNU (ψ.comp φ) p = mapNU ψ (mapNU φ p) := rfl

@[simp] theorem mapNU_unital (φ : A →⋆ₐ[ℂ] B) (p : FiniteProjection A) :
    mapNU φ.toNonUnitalStarAlgHom p = map φ p := rfl
end FiniteProjection

namespace StableProjectionMonoid

def mapNU (φ : A →⋆ₙₐ[ℂ] B) : StableProjectionMonoid A →+ StableProjectionMonoid B where
  toFun := Quotient.map (FiniteProjection.mapNU φ) (fun _ _ h => FiniteProjection.equivalent_mapNU φ h)
  map_zero' := congrArg of (FiniteProjection.mapNU_zero φ)
  map_add' p q := by
    refine Quotient.inductionOn₂ p q ?_
    intro p q
    exact congrArg of (FiniteProjection.mapNU_blockSum φ p q)

@[simp] theorem mapNU_of (φ : A →⋆ₙₐ[ℂ] B) (p : FiniteProjection A) :
    mapNU φ (of p) = of (FiniteProjection.mapNU φ p) := rfl
end StableProjectionMonoid

def k0MapNU (φ : A →⋆ₙₐ[ℂ] B) : K0 A →+ K0 B :=
  k0Universal (k0Class.comp (StableProjectionMonoid.mapNU φ))

@[simp] theorem k0MapNU_projection (φ : A →⋆ₙₐ[ℂ] B) (p : FiniteProjection A) :
    k0MapNU φ (k0Projection p) = k0Projection (FiniteProjection.mapNU φ p) := k0Universal_class _ _

@[simp] theorem k0MapNU_id : k0MapNU (NonUnitalStarAlgHom.id ℂ A) = AddMonoidHom.id (K0 A) := by
  apply k0Hom_ext
  intro p
  simp only [k0MapNU_projection, FiniteProjection.mapNU_id, AddMonoidHom.id_apply]

@[simp] theorem k0MapNU_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    k0MapNU (ψ.comp φ) = (k0MapNU ψ).comp (k0MapNU φ) := by
  apply k0Hom_ext
  intro p
  simp only [k0MapNU_projection, FiniteProjection.mapNU_comp, AddMonoidHom.comp_apply]

@[simp] theorem k0MapNU_unital (φ : A →⋆ₐ[ℂ] B) : k0MapNU φ.toNonUnitalStarAlgHom = k0Map φ := by
  apply k0Hom_ext
  intro p
  simp only [k0MapNU_projection, FiniteProjection.mapNU_unital, k0Map_projection]

end BC4lean.OperatorKTheory
