import BC4lean.AlgebraicCrossedProduct
import BC4lean.TrivialActionUnitary
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Finite integration of an actual covariant module representation

The input consists of an actual Hilbert-module group action, actual source
coefficient representation and their pointwise equivariance equation. This
constructs only the genuine finite-support star homomorphism. No reduced
continuity or completed crossed-product representation is assumed.

-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A C H : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C] [PartialOrder C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]

variable (W : EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ C) H)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap C H H)

def covariantGenerator (a : A) (g : Γ) : AdjointableMap C H H :=
  π a * W.trivialActionOperator g

theorem covariantGenerator_covariance (α : CStarAlgebraAction Γ A)
    (hπ : ∀ g a, W.conjugateOperator g (π a) = π (α.automorphism g a)) (g : Γ) (a : A) :
    π (α.automorphism g a) * W.trivialActionOperator g = W.trivialActionOperator g * π a := by
  rw [W.trivialActionOperator_intertwine, hπ, α.inv_apply_apply]

theorem covariantGenerator_mul (α : CStarAlgebraAction Γ A)
    (hπ : ∀ g a, W.conjugateOperator g (π a) = π (α.automorphism g a))
    (a b : A) (g h : Γ) :
    covariantGenerator W π a g * covariantGenerator W π b h =
      covariantGenerator W π (a * α.automorphism g b) (g * h) := by
  unfold covariantGenerator
  calc
    _ = π a * (W.trivialActionOperator g * π b) * W.trivialActionOperator h := by noncomm_ring
    _ = π a * (π (α.automorphism g b) * W.trivialActionOperator g) *
        W.trivialActionOperator h := by rw [← covariantGenerator_covariance W π α hπ g b]
    _ = (π a * π (α.automorphism g b)) *
        (W.trivialActionOperator g * W.trivialActionOperator h) := by noncomm_ring
    _ = _ := by rw [map_mul, W.trivialActionOperator_mul]

theorem covariantGenerator_star (α : CStarAlgebraAction Γ A)
    (hπ : ∀ g a, W.conjugateOperator g (π a) = π (α.automorphism g a)) (a : A) (g : Γ) :
    star (covariantGenerator W π a g) =
      covariantGenerator W π (α.automorphism g⁻¹ (star a)) g⁻¹ := by
  unfold covariantGenerator
  rw [star_mul, W.trivialActionOperator_star, ← map_star]
  exact (covariantGenerator_covariance W π α hπ g⁻¹ (star a)).symm

private def covariantGeneratorLinear (g : Γ) : A →ₗ[ℂ] AdjointableMap C H H where
  toFun a := covariantGenerator W π a g
  map_add' a b := by
    change π (a + b) * W.trivialActionOperator g =
      π a * W.trivialActionOperator g + π b * W.trivialActionOperator g
    rw [map_add, add_mul]
  map_smul' z a := by
    change π (z • a) * W.trivialActionOperator g = z • (π a * W.trivialActionOperator g)
    rw [map_smul, smul_mul_assoc]

def covariantAlgebraicLinear (α : CStarAlgebraAction Γ A) :
    AlgebraicCrossedProduct α →ₗ[ℂ] AdjointableMap C H H :=
  (Finsupp.lsum ℂ (covariantGeneratorLinear W π)).comp
    (AlgebraicCrossedProduct.coeffLinearEquiv α).toLinearMap

@[simp] theorem covariantAlgebraicLinear_single (α : CStarAlgebraAction Γ A) (g : Γ) (a : A) :
    covariantAlgebraicLinear W π α (AlgebraicCrossedProduct.single α g a) =
      covariantGenerator W π a g := by
  change Finsupp.lsum ℂ (covariantGeneratorLinear W π) (Finsupp.single g a) = _
  exact Finsupp.lsum_single ℂ (covariantGeneratorLinear W π) g a

theorem covariantAlgebraicLinear_mul (α : CStarAlgebraAction Γ A)
    (hπ : ∀ g a, W.conjugateOperator g (π a) = π (α.automorphism g a))
    (f h : AlgebraicCrossedProduct α) :
    covariantAlgebraicLinear W π α (f * h) =
      covariantAlgebraicLinear W π α f * covariantAlgebraicLinear W π α h := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp
  | single g a =>
    induction h using AlgebraicCrossedProduct.induction_on α with
    | zero => simp
    | single k b => simp only [AlgebraicCrossedProduct.single_mul_single,
        covariantAlgebraicLinear_single, covariantGenerator_mul W π α hπ]
    | add h₁ h₂ ih₁ ih₂ => simp [mul_add, ih₁, ih₂]
  | add f₁ f₂ ih₁ ih₂ => simp [add_mul, ih₁, ih₂]

theorem covariantAlgebraicLinear_star (α : CStarAlgebraAction Γ A)
    (hπ : ∀ g a, W.conjugateOperator g (π a) = π (α.automorphism g a))
    (f : AlgebraicCrossedProduct α) :
    covariantAlgebraicLinear W π α (star f) = star (covariantAlgebraicLinear W π α f) := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp
  | single g a => simp only [AlgebraicCrossedProduct.star_single,
      covariantAlgebraicLinear_single, covariantGenerator_star W π α hπ]
  | add f h ihf ihh => simp [ihf, ihh]

def covariantAlgebraicRepresentation (α : CStarAlgebraAction Γ A)
    (hπ : ∀ g a, W.conjugateOperator g (π a) = π (α.automorphism g a)) :
    AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] AdjointableMap C H H where
  toFun := covariantAlgebraicLinear W π α
  map_zero' := map_zero (covariantAlgebraicLinear W π α)
  map_add' := map_add (covariantAlgebraicLinear W π α)
  map_smul' := map_smul (covariantAlgebraicLinear W π α)
  map_mul' := covariantAlgebraicLinear_mul W π α hπ
  map_star' := covariantAlgebraicLinear_star W π α hπ

@[simp] theorem covariantAlgebraicRepresentation_single (α : CStarAlgebraAction Γ A)
    (hπ : ∀ g a, W.conjugateOperator g (π a) = π (α.automorphism g a)) (g : Γ) (a : A) :
    covariantAlgebraicRepresentation W π α hπ (AlgebraicCrossedProduct.single α g a) =
      covariantGenerator W π a g := covariantAlgebraicLinear_single W π α g a

end BC4lean.KKTheory
