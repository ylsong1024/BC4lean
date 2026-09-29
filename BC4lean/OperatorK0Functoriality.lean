import BC4lean.MatrixProjectionMap
import BC4lean.OperatorK0

/-! # Functoriality of unital operator K₀

First descend entrywise maps to the stable projection monoid, then use the
Grothendieck group universal property. No cancellation hypothesis is needed.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

universe u v w t
variable {A : Type u} {B : Type v} {C : Type w}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder C] [StarOrderedRing C]

namespace StableProjectionMonoid

/-- The additive map on stable projection classes induced by a unital ⋆-homomorphism. -/
def map (φ : A →⋆ₐ[ℂ] B) : StableProjectionMonoid A →+ StableProjectionMonoid B where
  toFun := Quotient.map (FiniteProjection.map φ) (fun _ _ h => FiniteProjection.equivalent_map φ h)
  map_zero' := by
    change of (FiniteProjection.map φ FiniteProjection.zero) = of FiniteProjection.zero
    rw [FiniteProjection.map_zero]
  map_add' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    change of (FiniteProjection.map φ (FiniteProjection.blockSum p q)) =
      of (FiniteProjection.blockSum (FiniteProjection.map φ p) (FiniteProjection.map φ q))
    rw [FiniteProjection.map_blockSum]

@[simp] theorem map_of (φ : A →⋆ₐ[ℂ] B) (p : FiniteProjection A) :
    map φ (of p) = of (FiniteProjection.map φ p) := rfl

@[simp] theorem map_id : map (StarAlgHom.id ℂ A) = AddMonoidHom.id (StableProjectionMonoid A) := by
  ext x
  refine Quotient.inductionOn x ?_
  intro p
  change of (FiniteProjection.map (StarAlgHom.id ℂ A) p) = of p
  rw [FiniteProjection.map_id]

@[simp] theorem map_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext x
  refine Quotient.inductionOn x ?_
  intro p
  rfl

end StableProjectionMonoid

/-- The homomorphism K₀(A) → K₀(B) induced by a unital complex ⋆-homomorphism. -/
def k0Map (φ : A →⋆ₐ[ℂ] B) : K0 A →+ K0 B :=
  k0Universal (k0Class.comp (StableProjectionMonoid.map φ))

@[simp] theorem k0Map_class (φ : A →⋆ₐ[ℂ] B) (x : StableProjectionMonoid A) :
    k0Map φ (k0Class x) = k0Class (StableProjectionMonoid.map φ x) :=
  k0Universal_class _ x

/-- Naturality of the canonical group-completion homomorphism. -/
theorem k0Map_comp_class (φ : A →⋆ₐ[ℂ] B) :
    (k0Map φ).comp k0Class = k0Class.comp (StableProjectionMonoid.map φ) :=
  k0Universal_comp _

@[simp] theorem k0Map_projection (φ : A →⋆ₐ[ℂ] B) (p : FiniteProjection A) :
    k0Map φ (k0Projection p) = k0Projection (FiniteProjection.map φ p) :=
  k0Map_class φ (StableProjectionMonoid.of p)

/-- Homomorphisms out of K₀ are determined by their values on projection classes. -/
theorem k0Hom_ext {G : Type t} [AddCommGroup G] {f g : K0 A →+ G}
    (h : ∀ p : FiniteProjection A, f (k0Projection p) = g (k0Projection p)) : f = g := by
  apply k0Universal.symm.injective
  change f.comp k0Class = g.comp k0Class
  ext x
  refine Quotient.inductionOn x ?_
  intro p
  exact h p

@[simp] theorem k0Map_id : k0Map (StarAlgHom.id ℂ A) = AddMonoidHom.id (K0 A) := by
  apply k0Hom_ext
  intro p
  simp only [k0Map_projection, FiniteProjection.map_id, AddMonoidHom.id_apply]

@[simp] theorem k0Map_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) :
    k0Map (ψ.comp φ) = (k0Map ψ).comp (k0Map φ) := by
  apply k0Hom_ext
  intro p
  simp only [k0Map_projection, FiniteProjection.map_comp, AddMonoidHom.comp_apply]

/-- The induced map is the unique homomorphism with the entrywise projection-class formula. -/
theorem k0Map_unique (φ : A →⋆ₐ[ℂ] B) (f : K0 A →+ K0 B)
    (h : ∀ p : FiniteProjection A, f (k0Projection p) = k0Projection (FiniteProjection.map φ p)) :
    k0Map φ = f := by
  apply k0Hom_ext
  intro p
  exact (k0Map_projection φ p).trans (h p).symm

end BC4lean.OperatorKTheory
