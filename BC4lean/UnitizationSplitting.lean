import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Algebra.Star.StarAlgHom

/-! # The forced unitization of an already unital algebra -/
noncomputable section
namespace BC4lean.OperatorKTheory
variable (A : Type*) [CStarAlgebra A]

/-- Evaluation of the new scalar unit using the original unit. -/
def unitizationEval : Unitization ℂ A →⋆ₐ[ℂ] A :=
  Unitization.starLift (NonUnitalStarAlgHom.id ℂ A)

@[simp] theorem unitizationEval_apply (x : Unitization ℂ A) :
    unitizationEval A x = algebraMap ℂ A x.fst + x.snd := rfl

/-- The scalar coordinate and original-unit evaluation split the forced unitization. -/
def unitizationProductHom : Unitization ℂ A →⋆ₐ[ℂ] ℂ × A :=
  ({ Unitization.fstHom ℂ A with map_star' := Unitization.fst_star } :
    Unitization ℂ A →⋆ₐ[ℂ] ℂ).prod (unitizationEval A)

/-- The splitting is an actual star-algebra isomorphism, with no K-theory premise. -/
def unitizationProductEquiv : Unitization ℂ A ≃⋆ₐ[ℂ] ℂ × A :=
  StarAlgEquiv.ofBijective (unitizationProductHom A) (by
    constructor
    · intro x y h
      have hfst := congrArg (fun z : ℂ × A => z.1) h
      change x.fst = y.fst at hfst
      have hsnd := congrArg (fun z : ℂ × A => z.2) h
      change algebraMap ℂ A x.fst + x.snd = algebraMap ℂ A y.fst + y.snd at hsnd
      apply Unitization.ext hfst
      rw [hfst] at hsnd
      exact add_left_cancel hsnd
    · intro x
      refine ⟨⟨x.1, x.2 - algebraMap ℂ A x.1⟩, ?_⟩
      apply Prod.ext
      · rfl
      · change algebraMap ℂ A x.1 + (x.2 - algebraMap ℂ A x.1) = x.2
        abel)

@[simp] theorem unitizationProductEquiv_fst (x : Unitization ℂ A) :
    (unitizationProductEquiv A x).1 = x.fst := rfl

@[simp] theorem unitizationProductEquiv_snd (x : Unitization ℂ A) :
    (unitizationProductEquiv A x).2 = algebraMap ℂ A x.fst + x.snd := rfl

end BC4lean.OperatorKTheory
