import BC4lean.EquivariantHilbertModule
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # The equivariant algebra of functions vanishing at infinity

Pullback along cocompact continuous maps is a nonunital complex star-algebra
homomorphism. A continuous action by homeomorphisms acts on functions by
`(g • f) x = f (g⁻¹ • x)`. These constructions need no compactness,
countability, or separation hypotheses on the space.
-/

noncomputable section

open scoped ZeroAtInfty

namespace BC4lean.KKTheory.CZero

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- The canonical spectral order on the function C⋆-algebra. -/
instance instPartialOrder : PartialOrder C₀(X, ℂ) :=
  CStarAlgebra.spectralOrder C₀(X, ℂ)

/-- The canonical order is compatible with the C⋆-algebra's star operation. -/
instance instStarOrderedRing : StarOrderedRing C₀(X, ℂ) :=
  CStarAlgebra.spectralOrderedRing C₀(X, ℂ)

/-- Pullback of complex functions vanishing at infinity. -/
def pullback (f : CocompactMap X Y) : C₀(Y, ℂ) →⋆ₙₐ[ℂ] C₀(X, ℂ) where
  toNonUnitalAlgHom := ZeroAtInftyContinuousMap.compNonUnitalAlgHom f
  map_star' _ := rfl

@[simp] theorem pullback_apply (f : CocompactMap X Y) (a : C₀(Y, ℂ)) (x : X) :
    pullback f a x = a (f x) := rfl

@[simp] theorem pullback_id :
    pullback (CocompactMap.id X) = NonUnitalStarAlgHom.id ℂ C₀(X, ℂ) := by
  ext a x
  rfl

@[simp] theorem pullback_comp (g : CocompactMap Y Z) (f : CocompactMap X Y) :
    pullback (g.comp f) = (pullback f).comp (pullback g) := by
  ext a x
  rfl

/-- Pullback along a homeomorphism is a complex star-algebra equivalence. -/
def homeomorphPullback (f : X ≃ₜ Y) : C₀(Y, ℂ) ≃⋆ₐ[ℂ] C₀(X, ℂ) where
  toFun := pullback f.toCocompactMap
  invFun := pullback f.symm.toCocompactMap
  left_inv a := by ext x; exact congrArg a (f.apply_symm_apply x)
  right_inv a := by ext x; exact congrArg a (f.symm_apply_apply x)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem homeomorphPullback_apply (f : X ≃ₜ Y) (a : C₀(Y, ℂ)) (x : X) :
    homeomorphPullback f a x = a (f x) := rfl

variable (Γ : Type*) [Group Γ] [MulAction Γ X] [ContinuousConstSMul Γ X]

/-- The genuine action on `C₀(X, ℂ)` induced by a continuous action on `X`. -/
def action : CStarAlgebraAction Γ C₀(X, ℂ) where
  automorphism :=
    { toFun := fun g => homeomorphPullback (Homeomorph.smul (α := X) g⁻¹)
      map_one' := by
        ext a x
        change a ((1 : Γ)⁻¹ • x) = a x
        simp
      map_mul' := by
        intro g h
        ext a x
        change a ((g * h)⁻¹ • x) = a (h⁻¹ • (g⁻¹ • x))
        rw [mul_inv_rev, mul_smul] }

@[simp] theorem action_apply (g : Γ) (a : C₀(X, ℂ)) (x : X) :
    (action Γ).automorphism g a x = a (g⁻¹ • x) := rfl

end BC4lean.KKTheory.CZero
