import BC4lean.CliffordTensorGrading

/-! # The actual Clifford tensor map of a nonunital coefficient homomorphism

The proved tensor-coordinate equivalences conjugate the genuine product map
(b₊,b₋) ↦ (f(b₊),f(b₋)). The elementary tensor formula identifies this with
f ⊗ I. The map respects the actual swap grading and coefficient group action,
and its identity and composition laws hold on the whole complete tensor.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped TensorProduct

variable {B C D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [NonUnitalCStarAlgebra D]

def cliffordCoordinateHom (f : B →⋆ₙₐ[ℂ] C) : (B × B) →⋆ₙₐ[ℂ] (C × C) where
  toFun b := (f b.1, f b.2)
  map_zero' := Prod.ext (map_zero f) (map_zero f)
  map_add' b c := Prod.ext (map_add f b.1 c.1) (map_add f b.2 c.2)
  map_mul' b c := Prod.ext (map_mul f b.1 c.1) (map_mul f b.2 c.2)
  map_smul' z b := Prod.ext (map_smul f z b.1) (map_smul f z b.2)
  map_star' b := Prod.ext (map_star f b.1) (map_star f b.2)

@[simp] theorem cliffordCoordinateHom_apply (f : B →⋆ₙₐ[ℂ] C) (b : B × B) :
    cliffordCoordinateHom f b = (f b.1, f b.2) := rfl

def cliffordTensorHom (f : B →⋆ₙₐ[ℂ] C) : CliffordTensor B →⋆ₙₐ[ℂ] CliffordTensor C :=
  cliffordTensorCoordinateStarAlgEquiv.symm.toNonUnitalStarAlgHom.comp
    ((cliffordCoordinateHom f).comp cliffordTensorCoordinateStarAlgEquiv.toNonUnitalStarAlgHom)

@[simp] theorem cliffordTensorHom_coordinate (f : B →⋆ₙₐ[ℂ] C) (x : CliffordTensor B) :
    cliffordTensorCoordinateStarAlgEquiv (cliffordTensorHom f x) =
      cliffordCoordinateHom f (cliffordTensorCoordinateStarAlgEquiv x) := by
  exact cliffordTensorCoordinateStarAlgEquiv.apply_symm_apply _

@[simp] theorem cliffordTensorHom_id :
    cliffordTensorHom (NonUnitalStarAlgHom.id ℂ B) = NonUnitalStarAlgHom.id ℂ (CliffordTensor B) := by
  ext x
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorHom (NonUnitalStarAlgHom.id ℂ B) x) =
    cliffordTensorCoordinateStarAlgEquiv x
  rw [cliffordTensorHom_coordinate]; rfl

theorem cliffordTensorHom_comp (f : B →⋆ₙₐ[ℂ] C) (g : C →⋆ₙₐ[ℂ] D) :
    cliffordTensorHom (g.comp f) = (cliffordTensorHom g).comp (cliffordTensorHom f) := by
  ext x
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv (cliffordTensorHom (g.comp f) x) =
    cliffordTensorCoordinateStarAlgEquiv (cliffordTensorHom g (cliffordTensorHom f x))
  rw [cliffordTensorHom_coordinate, cliffordTensorHom_coordinate, cliffordTensorHom_coordinate]; rfl

variable [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
/-- The coefficient map is genuinely f ⊗ I on elementary tensors. -/
theorem cliffordTensorHom_pure (f : B →⋆ₙₐ[ℂ] C) (b : B) (z : CliffordOne) :
    cliffordTensorHom f (cliffordTensorPure b z) = cliffordTensorPure (f b) z := by
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv (cliffordTensorHom f (cliffordTensorPure b z)) =
    cliffordTensorCoordinateStarAlgEquiv (cliffordTensorPure (f b) z)
  rw [cliffordTensorHom_coordinate]
  change (f (z.1 • b), f (z.2 • b)) = cliffordTensorCoordinates (f b ⊗ₜ[ℂ] z)
  rw [cliffordTensorCoordinates_tmul]
  exact Prod.ext (map_smul f z.1 b) (map_smul f z.2 b)

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem cliffordTensorHom_graded (f : B →⋆ₙₐ[ℂ] C) (x : CliffordTensor B) :
    cliffordTensorHom f (cliffordTensorGrading.automorphism x) =
      cliffordTensorGrading.automorphism (cliffordTensorHom f x) := by
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorHom f (cliffordTensorGrading.automorphism x)) =
    cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorGrading.automorphism (cliffordTensorHom f x))
  rw [cliffordTensorHom_coordinate, cliffordTensorCoordinate_grading,
    cliffordTensorCoordinate_grading, cliffordTensorHom_coordinate]; rfl

variable {Γ : Type*} [Group Γ]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem cliffordTensorHom_equivariant (f : B →⋆ₙₐ[ℂ] C)
    (hf : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (g : Γ) (x : CliffordTensor B) :
    cliffordTensorHom f ((cliffordTensorAction β).automorphism g x) =
      (cliffordTensorAction γ).automorphism g (cliffordTensorHom f x) := by
  apply cliffordTensorCoordinateStarAlgEquiv.injective
  change cliffordTensorCoordinateStarAlgEquiv
      (cliffordTensorHom f ((cliffordTensorAction β).automorphism g x)) =
    cliffordTensorCoordinateStarAlgEquiv
      ((cliffordTensorAction γ).automorphism g (cliffordTensorHom f x))
  rw [cliffordTensorHom_coordinate, cliffordTensorCoordinate_action,
    cliffordTensorCoordinate_action, cliffordTensorHom_coordinate]
  apply Prod.ext
  · exact hf g (cliffordTensorCoordinateStarAlgEquiv x).1
  · exact hf g (cliffordTensorCoordinateStarAlgEquiv x).2

end BC4lean.KKTheory
