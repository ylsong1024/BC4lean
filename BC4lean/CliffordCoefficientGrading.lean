import BC4lean.GradedKasparovCycle

/-! # The actual coordinate coefficient grading and action of Cl₁

The coordinate swap grading and diagonal coefficient action are elementary
star automorphisms. Keeping them separate from the approximate-unit range
construction permits the genuine tensor grading to depend only on these
actual algebra maps.
-/

noncomputable section
namespace BC4lean.KKTheory
variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The coefficient grading for the actual product model of B ⊗ Cl₁. -/
def cliffordCoefficientGrading : CStarGrading (B × B) where
  automorphism :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := Prod.swap_swap
      right_inv := Prod.swap_swap
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      map_star' _ := rfl
      map_smul' _ _ := rfl }
  involutive := Prod.swap_swap

@[simp] theorem cliffordCoefficientGrading_apply (b : B × B) :
    cliffordCoefficientGrading.automorphism b = (b.2, b.1) := rfl

/-- The group acts on B and trivially on the Clifford factor. -/
def cliffordCoefficientAction {Γ : Type*} [Group Γ] (β : CStarAlgebraAction Γ B) :
    CStarAlgebraAction Γ (B × B) where
  automorphism :=
    { toFun g :=
        { toFun b := (β.automorphism g b.1, β.automorphism g b.2)
          invFun b := (β.automorphism g⁻¹ b.1, β.automorphism g⁻¹ b.2)
          left_inv b := by ext <;> exact β.inv_apply_apply g _
          right_inv b := by ext <;> exact β.apply_inv_apply g _
          map_add' a b := by ext <;> exact map_add _ _ _
          map_mul' a b := by ext <;> exact map_mul _ _ _
          map_star' a := by ext <;> exact map_star _ _
          map_smul' c a := by ext <;> exact map_smul _ _ _ }
      map_one' := by ext b <;> exact β.one_apply _
      map_mul' g h := by ext b <;> exact β.mul_apply g h _ }

@[simp] theorem cliffordCoefficientAction_apply {Γ : Type*} [Group Γ]
    (β : CStarAlgebraAction Γ B) (g : Γ) (b : B × B) :
    (cliffordCoefficientAction β).automorphism g b =
      (β.automorphism g b.1, β.automorphism g b.2) := rfl

theorem cliffordCoefficientAction_preservesGrading {Γ : Type*} [Group Γ]
    (β : CStarAlgebraAction Γ B) :
    (cliffordCoefficientAction β).PreservesGrading cliffordCoefficientGrading :=
  fun _ _ => rfl

end BC4lean.KKTheory
