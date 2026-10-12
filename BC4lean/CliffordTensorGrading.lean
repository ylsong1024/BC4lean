import BC4lean.CliffordAlgebraTensor
import BC4lean.CliffordCoefficientGrading

/-! # The actual Clifford tensor equivalence is graded and equivariant

The grading and group action on the constructed C⋆ tensor are transported
through its proved coordinate star equivalence. Their pure tensor formulas
identify the swap grading with the actual odd Clifford generator and the
diagonal group action with the original coefficient action on B.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped TensorProduct
variable {Γ B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The actual elementary tensor in the constructed complete C⋆ tensor. -/
def cliffordTensorPure (b : B) (z : CliffordOne) : CliffordTensor B := b ⊗ₜ[ℂ] z

/-- The grading on B ⊗ Cl₁, for trivially graded B. -/
def cliffordTensorGrading : CStarGrading (CliffordTensor B) where
  automorphism := cliffordTensorCoordinateStarAlgEquiv.trans
    (cliffordCoefficientGrading.automorphism.trans cliffordTensorCoordinateStarAlgEquiv.symm)
  involutive x := by
    apply cliffordTensorCoordinateStarAlgEquiv.injective
    simp [StarAlgEquiv.trans_apply, cliffordCoefficientGrading_apply]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem cliffordTensorCoordinate_grading (x : CliffordTensor B) :
    cliffordTensorCoordinateStarAlgEquiv (cliffordTensorGrading.automorphism x) =
      cliffordCoefficientGrading.automorphism (cliffordTensorCoordinateStarAlgEquiv x) := by
  simp [cliffordTensorGrading, StarAlgEquiv.trans_apply]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The grading applies the actual Clifford grading to the elementary factor. -/
theorem cliffordTensorGrading_pure (b : B) (z : CliffordOne) :
    cliffordTensorGrading.automorphism (cliffordTensorPure b z) =
      cliffordTensorPure b (CliffordOne.grading.automorphism z) := by
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorGrading.automorphism (cliffordTensorPure b z)) =
    cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorPure b (CliffordOne.grading.automorphism z))
  rw [cliffordTensorCoordinate_grading]
  change cliffordCoefficientGrading.automorphism
    (cliffordTensorCoordinates (b ⊗ₜ[ℂ] z)) =
      cliffordTensorCoordinates (b ⊗ₜ[ℂ] CliffordOne.grading.automorphism z)
  rw [cliffordTensorCoordinates_tmul, cliffordTensorCoordinates_tmul]
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- The odd generator stays odd in the actual coefficient tensor. -/
theorem cliffordTensor_epsilon_odd (b : B) :
    cliffordTensorGrading.automorphism (cliffordTensorPure b CliffordOne.epsilon) =
      -cliffordTensorPure b CliffordOne.epsilon := by
  rw [cliffordTensorGrading_pure, CliffordOne.epsilon_odd]
  exact TensorProduct.tmul_neg _ _

/-- The group acts through B and acts trivially on the Clifford factor. -/
def cliffordTensorAction (β : CStarAlgebraAction Γ B) : CStarAlgebraAction Γ (CliffordTensor B) where
  automorphism :=
    { toFun g := cliffordTensorCoordinateStarAlgEquiv.trans
        (((cliffordCoefficientAction β).automorphism g).trans cliffordTensorCoordinateStarAlgEquiv.symm)
      map_one' := by
        ext x
        apply cliffordTensorCoordinateStarAlgEquiv.injective
        simp [StarAlgEquiv.trans_apply]
      map_mul' g h := by
        ext x
        apply cliffordTensorCoordinateStarAlgEquiv.injective
        simp [StarAlgEquiv.trans_apply] }

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem cliffordTensorCoordinate_action (β : CStarAlgebraAction Γ B)
    (g : Γ) (x : CliffordTensor B) :
    cliffordTensorCoordinateStarAlgEquiv ((cliffordTensorAction β).automorphism g x) =
      (cliffordCoefficientAction β).automorphism g (cliffordTensorCoordinateStarAlgEquiv x) := by
  simp [cliffordTensorAction, StarAlgEquiv.trans_apply]

omit [PartialOrder B] [StarOrderedRing B] in
theorem cliffordTensorAction_pure (β : CStarAlgebraAction Γ B)
    (g : Γ) (b : B) (z : CliffordOne) :
    (cliffordTensorAction β).automorphism g (cliffordTensorPure b z) =
      cliffordTensorPure (β.automorphism g b) z := by
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv
      ((cliffordTensorAction β).automorphism g (cliffordTensorPure b z)) =
    cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorPure (β.automorphism g b) z)
  rw [cliffordTensorCoordinate_action]
  change (cliffordCoefficientAction β).automorphism g
    (cliffordTensorCoordinates (b ⊗ₜ[ℂ] z)) =
      cliffordTensorCoordinates ((β.automorphism g b) ⊗ₜ[ℂ] z)
  rw [cliffordTensorCoordinates_tmul, cliffordTensorCoordinates_tmul,
    cliffordCoefficientAction_apply]
  apply Prod.ext <;> exact map_smul _ _ _

omit [PartialOrder B] [StarOrderedRing B] in
theorem cliffordTensorAction_preservesGrading (β : CStarAlgebraAction Γ B) :
    (cliffordTensorAction β).PreservesGrading cliffordTensorGrading := by
  intro g x
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv
      ((cliffordTensorAction β).automorphism g (cliffordTensorGrading.automorphism x)) =
    cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorGrading.automorphism ((cliffordTensorAction β).automorphism g x))
  rw [cliffordTensorCoordinate_action, cliffordTensorCoordinate_grading,
    cliffordTensorCoordinate_grading, cliffordTensorCoordinate_action]
  exact cliffordCoefficientAction_preservesGrading β g _

end BC4lean.KKTheory
