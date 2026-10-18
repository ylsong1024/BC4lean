import BC4lean.AlgebraicCrossedProduct
import BC4lean.ReducedCrossedProduct
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Integrating finite-support crossed-product elements

Finite twisted convolution integrates to the concrete regular representation.
Its codomain restriction to the reduced crossed product has dense range.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

private def algebraicCrossedGeneratorLinear (α : CStarAlgebraAction Γ B) (g : Γ) :
    B →ₗ[ℂ]
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) where
  toFun b := reducedCrossedGenerator α b g
  map_add' b c := by
    change reducedCrossedCoefficientHom α (b + c) * reducedCrossedRegular g =
      reducedCrossedCoefficientHom α b * reducedCrossedRegular g +
        reducedCrossedCoefficientHom α c * reducedCrossedRegular g
    rw [map_add, add_mul]
  map_smul' c b := by
    change reducedCrossedCoefficientHom α (c • b) * reducedCrossedRegular g =
      c • (reducedCrossedCoefficientHom α b * reducedCrossedRegular g)
    rw [map_smul, smul_mul_assoc]

/-- The finite sum of the actual regular generators. -/
def algebraicCrossedOperatorLinear (α : CStarAlgebraAction Γ B) :
    AlgebraicCrossedProduct α →ₗ[ℂ]
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  (Finsupp.lsum ℂ (algebraicCrossedGeneratorLinear α)).comp
    (AlgebraicCrossedProduct.coeffLinearEquiv α).toLinearMap

@[simp] theorem algebraicCrossedOperatorLinear_single (α : CStarAlgebraAction Γ B)
    (g : Γ) (b : B) :
    algebraicCrossedOperatorLinear α (AlgebraicCrossedProduct.single α g b) =
      reducedCrossedGenerator α b g := by
  change Finsupp.lsum ℂ (algebraicCrossedGeneratorLinear α) (Finsupp.single g b) = _
  exact Finsupp.lsum_single ℂ (algebraicCrossedGeneratorLinear α) g b

theorem algebraicCrossedOperatorLinear_mul (α : CStarAlgebraAction Γ B)
    (f h : AlgebraicCrossedProduct α) :
    algebraicCrossedOperatorLinear α (f * h) =
      algebraicCrossedOperatorLinear α f * algebraicCrossedOperatorLinear α h := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp
  | single g a =>
    induction h using AlgebraicCrossedProduct.induction_on α with
    | zero => simp
    | single k b =>
      simp only [AlgebraicCrossedProduct.single_mul_single,
        algebraicCrossedOperatorLinear_single, reducedCrossedGenerator_mul]
    | add h₁ h₂ ih₁ ih₂ => simp [mul_add, ih₁, ih₂]
  | add f₁ f₂ ih₁ ih₂ => simp [add_mul, ih₁, ih₂]

theorem algebraicCrossedOperatorLinear_star (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) :
    algebraicCrossedOperatorLinear α (star f) = star (algebraicCrossedOperatorLinear α f) := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp
  | single g b =>
    simp only [AlgebraicCrossedProduct.star_single, algebraicCrossedOperatorLinear_single,
      reducedCrossedGenerator_star]
  | add f h ihf ihh => simp [ihf, ihh]

/-- The actual integrated regular nonunital star-algebra homomorphism. -/
def algebraicCrossedOperatorHom (α : CStarAlgebraAction Γ B) :
    AlgebraicCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) where
  toFun := algebraicCrossedOperatorLinear α
  map_zero' := map_zero (algebraicCrossedOperatorLinear α)
  map_add' := map_add (algebraicCrossedOperatorLinear α)
  map_smul' := map_smul (algebraicCrossedOperatorLinear α)
  map_mul' := algebraicCrossedOperatorLinear_mul α
  map_star' := algebraicCrossedOperatorLinear_star α

/-- Integration is the finite sum of regular generators with the given coefficients. -/
theorem algebraicCrossedOperatorHom_eq_sum (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) :
    algebraicCrossedOperatorHom α f =
      ∑ g ∈ (AlgebraicCrossedProduct.coeff α f).support,
        reducedCrossedGenerator α (AlgebraicCrossedProduct.coeff α f g) g := rfl

@[simp] theorem algebraicCrossedOperatorHom_single (α : CStarAlgebraAction Γ B)
    (g : Γ) (b : B) :
    algebraicCrossedOperatorHom α (AlgebraicCrossedProduct.single α g b) =
      reducedCrossedGenerator α b g := algebraicCrossedOperatorLinear_single α g b

theorem algebraicCrossedOperator_mem (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) :
    algebraicCrossedOperatorHom α f ∈ reducedCrossedAlgebra α := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero =>
    rw [map_zero]
    exact zero_mem (reducedCrossedAlgebra α)
  | single g b =>
    simpa only [algebraicCrossedOperatorHom_single] using reducedCrossedGenerator_mem α b g
  | add f h ihf ihh =>
    rw [map_add]
    exact add_mem ihf ihh

/-- Integration with codomain in the actual reduced crossed-product C⋆-algebra. -/
def algebraicToReducedCrossed (α : CStarAlgebraAction Γ B) :
    AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] ReducedCrossedProduct α :=
  NonUnitalStarAlgHom.codRestrict (algebraicCrossedOperatorHom α) (reducedCrossedAlgebra α)
    (algebraicCrossedOperator_mem α)

@[simp] theorem algebraicToReducedCrossed_coe (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) :
    (algebraicToReducedCrossed α f :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) =
      algebraicCrossedOperatorHom α f := rfl

@[simp] theorem algebraicToReducedCrossed_single (α : CStarAlgebraAction Γ B)
    (g : Γ) (b : B) :
    (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g b) :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) =
      reducedCrossedGenerator α b g := algebraicCrossedOperatorHom_single α g b

/-- The regular-operator closure is exactly the closure of finite twisted convolution. -/
theorem algebraicCrossedOperator_range_closure (α : CStarAlgebraAction Γ B) :
    (NonUnitalStarAlgHom.range (algebraicCrossedOperatorHom α)).topologicalClosure =
      reducedCrossedAlgebra α := by
  apply le_antisymm
  · apply NonUnitalStarSubalgebra.topologicalClosure_minimal
    · rintro _ ⟨f, rfl⟩
      exact algebraicCrossedOperator_mem α f
    · exact reducedCrossedAlgebra_isClosed α
  · apply reducedCrossedAlgebra_minimal α _
      (NonUnitalStarSubalgebra.isClosed_topologicalClosure _)
    intro b g
    apply NonUnitalStarSubalgebra.le_topologicalClosure
    exact ⟨AlgebraicCrossedProduct.single α g b, algebraicCrossedOperatorHom_single α g b⟩

/-- Finite-support elements are dense in the constructed reduced crossed product. -/
theorem algebraicToReducedCrossed_denseRange (α : CStarAlgebraAction Γ B) :
    DenseRange (algebraicToReducedCrossed α) := by
  intro T
  rw [closure_subtype, ← Set.range_comp]
  change (T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
    (ReducedCrossedHilbertModule B Γ)) ∈ ((NonUnitalStarAlgHom.range
    (algebraicCrossedOperatorHom α)).topologicalClosure : Set _)
  rw [algebraicCrossedOperator_range_closure]
  exact T.property

end BC4lean.KKTheory
