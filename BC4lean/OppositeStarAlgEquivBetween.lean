import BC4lean.GradedHilbertModule

/-! # Opposite star equivalences between different coefficient algebras

The existing grading helper treats automorphisms of one coefficient
algebra. Actual coefficient change also needs equivalences between
different algebras. This separate helper constructs them directly and
agrees with the checked automorphism helper when both algebras coincide.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C D : Type*} [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def opStarAlgEquivBetween (e : B ≃⋆ₐ[ℂ] C) : Bᵐᵒᵖ ≃⋆ₐ[ℂ] Cᵐᵒᵖ where
  toFun a := MulOpposite.op (e (MulOpposite.unop a))
  invFun a := MulOpposite.op (e.symm (MulOpposite.unop a))
  left_inv a := by simp
  right_inv a := by simp
  map_mul' a b := by simp only [MulOpposite.unop_mul, map_mul, MulOpposite.op_mul]
  map_add' a b := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
  map_star' a := by simp only [MulOpposite.unop_star, map_star, MulOpposite.op_star]
  map_smul' c a := by simp only [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]

@[simp] theorem opStarAlgEquivBetween_apply (e : B ≃⋆ₐ[ℂ] C) (a : Bᵐᵒᵖ) :
    opStarAlgEquivBetween e a = MulOpposite.op (e (MulOpposite.unop a)) := rfl

@[simp] theorem opStarAlgEquivBetween_symm (e : B ≃⋆ₐ[ℂ] C) :
    (opStarAlgEquivBetween e).symm = opStarAlgEquivBetween e.symm := by
  ext a
  rfl

@[simp] theorem opStarAlgEquivBetween_refl :
    opStarAlgEquivBetween (StarAlgEquiv.refl ℂ B) = StarAlgEquiv.refl ℂ Bᵐᵒᵖ := by
  ext a
  rfl

theorem opStarAlgEquivBetween_trans (e : B ≃⋆ₐ[ℂ] C) (f : C ≃⋆ₐ[ℂ] D) :
    opStarAlgEquivBetween (e.trans f) = (opStarAlgEquivBetween e).trans (opStarAlgEquivBetween f) := by
  ext a
  rfl

theorem opStarAlgEquivBetween_endomorphism (e : B ≃⋆ₐ[ℂ] B) :
    opStarAlgEquivBetween e = opStarAlgEquiv e := rfl

end BC4lean.KKTheory
