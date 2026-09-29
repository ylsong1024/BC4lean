import BC4lean.OperatorK1Functoriality

/-! # Isomorphism invariance of unital K₁ -/
noncomputable section
namespace BC4lean.OperatorKTheory
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder C] [StarOrderedRing C]

theorem k1Map_leftInverse (e : A ≃⋆ₐ[ℂ] B) :
    Function.LeftInverse (k1Map e.symm.toStarAlgHom) (k1Map e.toStarAlgHom) := by
  intro x
  have h : e.symm.toStarAlgHom.comp e.toStarAlgHom = StarAlgHom.id ℂ A := by
    ext a
    exact e.symm_apply_apply a
  change ((k1Map e.symm.toStarAlgHom).comp (k1Map e.toStarAlgHom)) x = x
  rw [← k1Map_comp, h, k1Map_id]
  rfl

theorem k1Map_rightInverse (e : A ≃⋆ₐ[ℂ] B) :
    Function.RightInverse (k1Map e.symm.toStarAlgHom) (k1Map e.toStarAlgHom) := by
  intro x
  have h : e.toStarAlgHom.comp e.symm.toStarAlgHom = StarAlgHom.id ℂ B := by
    ext a
    exact e.apply_symm_apply a
  change ((k1Map e.toStarAlgHom).comp (k1Map e.symm.toStarAlgHom)) x = x
  rw [← k1Map_comp, h, k1Map_id]
  rfl

/-- The canonical additive equivalence on unital K₁ induced by a star-algebra equivalence. -/
def k1Equiv (e : A ≃⋆ₐ[ℂ] B) : K1 A ≃+ K1 B where
  toFun := k1Map e.toStarAlgHom
  invFun := k1Map e.symm.toStarAlgHom
  left_inv := k1Map_leftInverse e
  right_inv := k1Map_rightInverse e
  map_add' := (k1Map e.toStarAlgHom).map_add

@[simp] theorem k1Equiv_toAddMonoidHom (e : A ≃⋆ₐ[ℂ] B) :
    (k1Equiv e).toAddMonoidHom = k1Map e.toStarAlgHom := rfl

@[simp] theorem k1Equiv_refl : k1Equiv (StarAlgEquiv.refl ℂ A) = AddEquiv.refl (K1 A) := by
  ext x
  change k1Map (StarAlgHom.id ℂ A) x = x
  rw [k1Map_id]
  rfl

@[simp] theorem k1Equiv_symm (e : A ≃⋆ₐ[ℂ] B) : k1Equiv e.symm = (k1Equiv e).symm := by
  ext x
  rfl

@[simp] theorem k1Equiv_trans (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) :
    k1Equiv (e.trans f) = (k1Equiv e).trans (k1Equiv f) := by
  ext x
  exact DFunLike.congr_fun (k1Map_comp f.toStarAlgHom e.toStarAlgHom) x

end BC4lean.OperatorKTheory
