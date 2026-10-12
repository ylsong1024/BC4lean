import BC4lean.ClosedStarHomKernelModule

/-! # Actual grading and group actions on closed coefficient kernels -/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ D C : Type*} [CStarAlgebra D] [CStarAlgebra C]
  [PartialOrder D] [StarOrderedRing D]

def starHomKernelGrading (χ : D →⋆ₐ[ℂ] C) (δ : CStarGrading D)
    (hχ : ∀ a, χ (δ.automorphism a) = χ a) :
    GradedHilbertModule δ (StarHomKernelModule χ) where
  grading := starHomKernelIsometryEquiv χ δ.automorphism hχ
  involutive x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact δ.involutive _
  inner_grading x y := by
    change opStarAlgEquiv δ.automorphism (y : Dᵐᵒᵖ) *
        star (opStarAlgEquiv δ.automorphism (x : Dᵐᵒᵖ)) =
      opStarAlgEquiv δ.automorphism ((y : Dᵐᵒᵖ) * star (x : Dᵐᵒᵖ))
    rw [map_mul, map_star]

@[simp] theorem starHomKernelGrading_coe (χ : D →⋆ₐ[ℂ] C) (δ : CStarGrading D)
    (hχ : ∀ a, χ (δ.automorphism a) = χ a) (x : StarHomKernelModule χ) :
    ((starHomKernelGrading χ δ hχ).grading x : Dᵐᵒᵖ) =
      opStarAlgEquiv δ.automorphism (x : Dᵐᵒᵖ) := rfl

theorem starHomKernelLeftMul_graded (χ : D →⋆ₐ[ℂ] C) (δ : CStarGrading D)
    (hχ : ∀ a, χ (δ.automorphism a) = χ a) (a : D) (x : StarHomKernelModule χ) :
    (starHomKernelGrading χ δ hχ).grading (starHomKernelLeftMul χ a x) =
      starHomKernelLeftMul χ (δ.automorphism a) ((starHomKernelGrading χ δ hχ).grading x) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact map_mul δ.automorphism a _

variable [Group Γ]

def starHomKernelAction (χ : D →⋆ₐ[ℂ] C) (α : CStarAlgebraAction Γ D)
    (hχ : ∀ g a, χ (α.automorphism g a) = χ a) :
    EquivariantHilbertModule α (StarHomKernelModule χ) where
  action :=
    { toFun := fun g => starHomKernelIsometryEquiv χ (α.automorphism g) (hχ g)
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro x
        apply Subtype.ext
        apply MulOpposite.unop_injective
        exact α.one_apply _
      map_mul' := fun g h => by
        apply LinearIsometryEquiv.ext
        intro x
        apply Subtype.ext
        apply MulOpposite.unop_injective
        exact α.mul_apply g h _ }
  inner_action g x y := by
    change opStarAlgEquiv (α.automorphism g) (y : Dᵐᵒᵖ) *
        star (opStarAlgEquiv (α.automorphism g) (x : Dᵐᵒᵖ)) =
      opStarAlgEquiv (α.automorphism g) ((y : Dᵐᵒᵖ) * star (x : Dᵐᵒᵖ))
    rw [map_mul, map_star]

@[simp] theorem starHomKernelAction_coe (χ : D →⋆ₐ[ℂ] C) (α : CStarAlgebraAction Γ D)
    (hχ : ∀ g a, χ (α.automorphism g a) = χ a) (g : Γ) (x : StarHomKernelModule χ) :
    ((starHomKernelAction χ α hχ).action g x : Dᵐᵒᵖ) =
      opStarAlgEquiv (α.automorphism g) (x : Dᵐᵒᵖ) := rfl

theorem starHomKernelAction_preservesGrading (χ : D →⋆ₐ[ℂ] C)
    (α : CStarAlgebraAction Γ D) (δ : CStarGrading D)
    (hαχ : ∀ g a, χ (α.automorphism g a) = χ a)
    (hδχ : ∀ a, χ (δ.automorphism a) = χ a) (h : α.PreservesGrading δ) :
    (starHomKernelAction χ α hαχ).PreservesGrading (starHomKernelGrading χ δ hδχ) := by
  intro g x
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact h g _

theorem starHomKernelLeftMul_equivariant (χ : D →⋆ₐ[ℂ] C)
    (α : CStarAlgebraAction Γ D) (hχ : ∀ g a, χ (α.automorphism g a) = χ a)
    (g : Γ) (a : D) :
    (starHomKernelAction χ α hχ).conjugateOperator g (starHomKernelLeftMul χ a) =
      starHomKernelLeftMul χ (α.automorphism g a) := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change α.automorphism g (a * α.automorphism g⁻¹ (MulOpposite.unop (x : Dᵐᵒᵖ))) =
    α.automorphism g a * MulOpposite.unop (x : Dᵐᵒᵖ)
  rw [map_mul, α.apply_inv_apply]

end BC4lean.KKTheory
