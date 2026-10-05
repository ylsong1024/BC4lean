import BC4lean.EquivariantHilbertModule

/-! # The standard graded equivariant Hilbert module

The standard right Hilbert module B_B is represented by Bᵐᵒᵖ. A coefficient
algebra grading or group action acts on its underlying vectors by the same
coefficient automorphism. We construct these complex-linear isometric actions
and prove compatibility with the standard inner product and with gradings.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B Γ : Type*} [NonUnitalCStarAlgebra B]

/-- A complex star-automorphism of a C⋆-algebra is a linear isometry equivalence. -/
def starAlgEquivLinearIsometry (e : B ≃⋆ₐ[ℂ] B) : B ≃ₗᵢ[ℂ] B where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' := map_smul e
  norm_map' x := StarAlgEquiv.norm_map e x

@[simp] theorem starAlgEquivLinearIsometry_apply (e : B ≃⋆ₐ[ℂ] B) (b : B) :
    starAlgEquivLinearIsometry e b = e b := rfl

variable [PartialOrder B] [StarOrderedRing B]

namespace GradedHilbertModule

/-- The standard graded right Hilbert module over a graded coefficient algebra. -/
def standard (β : CStarGrading B) : GradedHilbertModule β Bᵐᵒᵖ where
  grading := starAlgEquivLinearIsometry (opStarAlgEquiv β.automorphism)
  involutive x := by
    change opStarAlgEquiv β.automorphism (opStarAlgEquiv β.automorphism x) = x
    exact β.op_automorphism_sq x
  inner_grading x y := by
    change opStarAlgEquiv β.automorphism y * star (opStarAlgEquiv β.automorphism x) =
      opStarAlgEquiv β.automorphism (y * star x)
    rw [map_mul, map_star]

@[simp] theorem standard_grading_apply (β : CStarGrading B) (x : Bᵐᵒᵖ) :
    (standard β).grading x = MulOpposite.op (β.automorphism (MulOpposite.unop x)) := rfl

end GradedHilbertModule

variable [Group Γ]
namespace EquivariantHilbertModule

/-- The coefficient action induces a genuine compatible action on the standard module. -/
def standard (α : CStarAlgebraAction Γ B) : EquivariantHilbertModule α Bᵐᵒᵖ where
  action :=
    { toFun := fun g => starAlgEquivLinearIsometry (opStarAlgEquiv (α.automorphism g))
      map_one' := by
        ext x
        change MulOpposite.op (α.automorphism 1 (MulOpposite.unop x)) = x
        simp
      map_mul' := by
        intro g h
        ext x
        change MulOpposite.op (α.automorphism (g * h) (MulOpposite.unop x)) =
          MulOpposite.op (α.automorphism g (α.automorphism h (MulOpposite.unop x)))
        rw [α.mul_apply] }
  inner_action g x y := by
    change opStarAlgEquiv (α.automorphism g) y * star (opStarAlgEquiv (α.automorphism g) x) =
      opStarAlgEquiv (α.automorphism g) (y * star x)
    rw [map_mul, map_star]

@[simp] theorem standard_action_apply (α : CStarAlgebraAction Γ B) (g : Γ) (x : Bᵐᵒᵖ) :
    (standard α).action g x = MulOpposite.op (α.automorphism g (MulOpposite.unop x)) := rfl

/-- Compatible coefficient grading and action induce compatible structures on B_B. -/
theorem standard_preservesGrading (α : CStarAlgebraAction Γ B) (β : CStarGrading B)
    (h : α.PreservesGrading β) :
    (standard α).PreservesGrading (GradedHilbertModule.standard β) := by
  intro g x
  change MulOpposite.op (α.automorphism g (β.automorphism (MulOpposite.unop x))) =
    MulOpposite.op (β.automorphism (α.automorphism g (MulOpposite.unop x)))
  exact congrArg MulOpposite.op (h g (MulOpposite.unop x))

/-- Every standard coefficient action preserves the grading concentrated in even degree. -/
theorem standard_preserves_trivialGrading (α : CStarAlgebraAction Γ B) :
    (standard α).PreservesGrading
      (GradedHilbertModule.trivial : GradedHilbertModule CStarGrading.trivial Bᵐᵒᵖ) :=
  fun _ _ => rfl

end EquivariantHilbertModule
end BC4lean.KKTheory
