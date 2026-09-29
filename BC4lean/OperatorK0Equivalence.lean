import BC4lean.OperatorK0Functoriality

/-! # Invariance of unital K₀ under star-algebra equivalence

The forward map comes from the given equivalence and the inverse map from its
inverse. Both inverse laws follow from functoriality. The compatible star orders
remain the explicit implementation assumptions of the matrix-algebra API.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder C] [StarOrderedRing C]

namespace StableProjectionMonoid

theorem map_leftInverse (e : A ≃⋆ₐ[ℂ] B) :
    Function.LeftInverse (map e.symm.toStarAlgHom) (map e.toStarAlgHom) := by
  intro x
  have h : e.symm.toStarAlgHom.comp e.toStarAlgHom = StarAlgHom.id ℂ A := by
    ext a
    exact e.symm_apply_apply a
  change ((map e.symm.toStarAlgHom).comp (map e.toStarAlgHom)) x = x
  rw [← map_comp, h, map_id]
  rfl

theorem map_rightInverse (e : A ≃⋆ₐ[ℂ] B) :
    Function.RightInverse (map e.symm.toStarAlgHom) (map e.toStarAlgHom) := by
  intro x
  have h : e.toStarAlgHom.comp e.symm.toStarAlgHom = StarAlgHom.id ℂ B := by
    ext a
    exact e.apply_symm_apply a
  change ((map e.toStarAlgHom).comp (map e.symm.toStarAlgHom)) x = x
  rw [← map_comp, h, map_id]
  rfl

/-- A unital star-algebra equivalence induces an additive equivalence of stable projection monoids. -/
def mapEquiv (e : A ≃⋆ₐ[ℂ] B) : StableProjectionMonoid A ≃+ StableProjectionMonoid B where
  toFun := map e.toStarAlgHom
  invFun := map e.symm.toStarAlgHom
  left_inv := map_leftInverse e
  right_inv := map_rightInverse e
  map_add' := (map e.toStarAlgHom).map_add

@[simp] theorem mapEquiv_toAddMonoidHom (e : A ≃⋆ₐ[ℂ] B) :
    (mapEquiv e).toAddMonoidHom = map e.toStarAlgHom := rfl

@[simp] theorem mapEquiv_of (e : A ≃⋆ₐ[ℂ] B) (p : FiniteProjection A) :
    mapEquiv e (of p) = of (FiniteProjection.map e.toStarAlgHom p) := rfl

@[simp] theorem mapEquiv_refl :
    mapEquiv (StarAlgEquiv.refl ℂ A) = AddEquiv.refl (StableProjectionMonoid A) := by
  ext x
  change map (StarAlgHom.id ℂ A) x = x
  rw [map_id]
  rfl

@[simp] theorem mapEquiv_symm (e : A ≃⋆ₐ[ℂ] B) : mapEquiv e.symm = (mapEquiv e).symm := by
  ext x
  rfl

@[simp] theorem mapEquiv_trans (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) :
    mapEquiv (e.trans f) = (mapEquiv e).trans (mapEquiv f) := by
  ext x
  exact DFunLike.congr_fun (map_comp f.toStarAlgHom e.toStarAlgHom) x

end StableProjectionMonoid

theorem k0Map_leftInverse (e : A ≃⋆ₐ[ℂ] B) :
    Function.LeftInverse (k0Map e.symm.toStarAlgHom) (k0Map e.toStarAlgHom) := by
  intro x
  have h : e.symm.toStarAlgHom.comp e.toStarAlgHom = StarAlgHom.id ℂ A := by
    ext a
    exact e.symm_apply_apply a
  change ((k0Map e.symm.toStarAlgHom).comp (k0Map e.toStarAlgHom)) x = x
  rw [← k0Map_comp, h, k0Map_id]
  rfl

theorem k0Map_rightInverse (e : A ≃⋆ₐ[ℂ] B) :
    Function.RightInverse (k0Map e.symm.toStarAlgHom) (k0Map e.toStarAlgHom) := by
  intro x
  have h : e.toStarAlgHom.comp e.symm.toStarAlgHom = StarAlgHom.id ℂ B := by
    ext a
    exact e.apply_symm_apply a
  change ((k0Map e.toStarAlgHom).comp (k0Map e.symm.toStarAlgHom)) x = x
  rw [← k0Map_comp, h, k0Map_id]
  rfl

/-- The canonical additive equivalence on unital K₀ induced by a star-algebra equivalence. -/
def k0Equiv (e : A ≃⋆ₐ[ℂ] B) : K0 A ≃+ K0 B where
  toFun := k0Map e.toStarAlgHom
  invFun := k0Map e.symm.toStarAlgHom
  left_inv := k0Map_leftInverse e
  right_inv := k0Map_rightInverse e
  map_add' := (k0Map e.toStarAlgHom).map_add

@[simp] theorem k0Equiv_toAddMonoidHom (e : A ≃⋆ₐ[ℂ] B) :
    (k0Equiv e).toAddMonoidHom = k0Map e.toStarAlgHom := rfl

@[simp] theorem k0Equiv_class (e : A ≃⋆ₐ[ℂ] B) (x : StableProjectionMonoid A) :
    k0Equiv e (k0Class x) = k0Class (StableProjectionMonoid.mapEquiv e x) :=
  k0Map_class e.toStarAlgHom x

@[simp] theorem k0Equiv_projection (e : A ≃⋆ₐ[ℂ] B) (p : FiniteProjection A) :
    k0Equiv e (k0Projection p) = k0Projection (FiniteProjection.map e.toStarAlgHom p) :=
  k0Map_projection e.toStarAlgHom p

@[simp] theorem k0Equiv_refl : k0Equiv (StarAlgEquiv.refl ℂ A) = AddEquiv.refl (K0 A) := by
  ext x
  change k0Map (StarAlgHom.id ℂ A) x = x
  rw [k0Map_id]
  rfl

@[simp] theorem k0Equiv_symm (e : A ≃⋆ₐ[ℂ] B) : k0Equiv e.symm = (k0Equiv e).symm := by
  ext x
  rfl

@[simp] theorem k0Equiv_trans (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) :
    k0Equiv (e.trans f) = (k0Equiv e).trans (k0Equiv f) := by
  ext x
  exact DFunLike.congr_fun (k0Map_comp f.toStarAlgHom e.toStarAlgHom) x

end BC4lean.OperatorKTheory
