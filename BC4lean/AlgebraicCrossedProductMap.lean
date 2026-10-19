import BC4lean.AlgebraicCrossedProduct
import Mathlib.LinearAlgebra.Finsupp.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Coefficientwise maps on actual finite crossed products

An arbitrary equivariant nonunital complex star homomorphism acts on the
finite coefficient function. Multiplication and star are proved from the
original equivariance identity and twisted singleton formulas. The map need
not be injective or nondegenerate.


-/

noncomputable section
namespace BC4lean.KKTheory.AlgebraicCrossedProduct

variable {Γ A B D : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

private def coefficientHomLinear (φ : A →⋆ₙₐ[ℂ] B) : A →ₗ[ℂ] B where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ

/-- Apply the actual coefficient homomorphism at each finite coordinate. -/
def mapLinear (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B) : AlgebraicCrossedProduct α →ₗ[ℂ] AlgebraicCrossedProduct β :=
  (coeffLinearEquiv β).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (coefficientHomLinear φ)).comp
      (coeffLinearEquiv α).toLinearMap)

@[simp] theorem coeff_mapLinear (α : CStarAlgebraAction Γ A)
    (β : CStarAlgebraAction Γ B) (φ : A →⋆ₙₐ[ℂ] B)
    (f : AlgebraicCrossedProduct α) (g : Γ) :
    coeff β (mapLinear α β φ f) g = φ (coeff α f g) := rfl

@[simp] theorem mapLinear_single (α : CStarAlgebraAction Γ A)
    (β : CStarAlgebraAction Γ B) (φ : A →⋆ₙₐ[ℂ] B) (g : Γ) (a : A) :
    mapLinear α β φ (single α g a) = single β g (φ a) := by
  classical
  apply AlgebraicCrossedProduct.ext β
  intro k
  simp only [coeff_mapLinear, coeff_single, Finsupp.single_apply]
  by_cases h : g = k
  · simp only [if_pos h]
  · simp only [if_neg h, map_zero]

theorem mapLinear_mul (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (f h : AlgebraicCrossedProduct α) :
    mapLinear α β φ (f * h) = mapLinear α β φ f * mapLinear α β φ h := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp
  | single g a =>
    induction h using AlgebraicCrossedProduct.induction_on α with
    | zero => simp
    | single k b =>
      simp only [single_mul_single, mapLinear_single, map_mul, hφ]
    | add h₁ h₂ ih₁ ih₂ => simp [mul_add, ih₁, ih₂]
  | add f₁ f₂ ih₁ ih₂ => simp [add_mul, ih₁, ih₂]

theorem mapLinear_star (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (f : AlgebraicCrossedProduct α) :
    mapLinear α β φ (star f) = star (mapLinear α β φ f) := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp
  | single g a => simp only [star_single, mapLinear_single, hφ, map_star]
  | add f h ihf ihh => simp [ihf, ihh]

/-- The actual finite crossed-product star homomorphism associated to an
equivariant nonunital coefficient homomorphism. -/
def map (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a)) :
    AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] AlgebraicCrossedProduct β where
  toFun := mapLinear α β φ
  map_zero' := map_zero (mapLinear α β φ)
  map_add' := map_add (mapLinear α β φ)
  map_smul' := map_smul (mapLinear α β φ)
  map_mul' := mapLinear_mul α β φ hφ
  map_star' := mapLinear_star α β φ hφ

@[simp] theorem coeff_map (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (f : AlgebraicCrossedProduct α) (g : Γ) :
    coeff β (map α β φ hφ f) g = φ (coeff α f g) := rfl

@[simp] theorem map_single (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a)) (g : Γ) (a : A) :
    map α β φ hφ (single α g a) = single β g (φ a) :=
  mapLinear_single α β φ g a

@[simp] theorem map_id_apply (α : CStarAlgebraAction Γ A) (f : AlgebraicCrossedProduct α) :
    map α α (NonUnitalStarAlgHom.id ℂ A) (fun _ _ => rfl) f = f := by
  apply AlgebraicCrossedProduct.ext α
  intro g
  rfl

/-- Original equivariance is preserved under composition of coefficient maps. -/
theorem equivariant_comp (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (δ : CStarAlgebraAction Γ D) (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] D)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (hψ : ∀ g b, ψ (β.automorphism g b) = δ.automorphism g (ψ b)) :
    ∀ g a, (ψ.comp φ) (α.automorphism g a) = δ.automorphism g ((ψ.comp φ) a) := by
  intro g a
  change ψ (φ (α.automorphism g a)) = δ.automorphism g (ψ (φ a))
  rw [hφ, hψ]

@[simp] theorem map_comp_apply (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (δ : CStarAlgebraAction Γ D) (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] D)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (hψ : ∀ g b, ψ (β.automorphism g b) = δ.automorphism g (ψ b))
    (f : AlgebraicCrossedProduct α) :
    map α δ (ψ.comp φ) (equivariant_comp α β δ φ ψ hφ hψ) f =
      map β δ ψ hψ (map α β φ hφ f) := by
  apply AlgebraicCrossedProduct.ext δ
  intro g
  simp only [coeff_map, NonUnitalStarAlgHom.comp_apply]

end BC4lean.KKTheory.AlgebraicCrossedProduct
