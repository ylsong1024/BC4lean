import BC4lean.ReducedSourceRegularBound
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The actual bounded source regular operator



The finite source regular action is extended along the actual dense finite-vector
map into the coefficient-norm indexed Hilbert module. `LinearMap.extendOfNorm`
uses the reduced-norm bound already proved for finite vectors; its source need
not carry an additional norm. The representation `π` may be degenerate and no
equivariant structure on the original module is required.
-/

noncomputable section
namespace BC4lean.KKTheory.ReducedSourceRegular

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (α : CStarAlgebraAction Γ A)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)

/-- The actual finite action followed by the finite-vector map into its
coefficient-norm Hilbert-module completion. -/
def finiteActionToModule (f : AlgebraicCrossedProduct α) :
    IndexedHilbertModule.Vectors E Γ →ₗ[ℂ] IndexedHilbertModule.Module B E Γ :=
  (IndexedHilbertModule.mk (B := B)).comp (finiteAction α π f)

@[simp] theorem finiteActionToModule_apply (f : AlgebraicCrossedProduct α)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    finiteActionToModule α π f ξ =
      IndexedHilbertModule.mk (B := B) (finiteAction α π f ξ) := rfl

/-- The finite bound is expressed in precisely the form required by the
extension along the actual dense finite-vector map. -/
theorem finiteActionToModule_norm_le (f : AlgebraicCrossedProduct α)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    ‖finiteActionToModule α π f ξ‖ ≤
      ‖algebraicCrossedOperatorHom α f‖ * ‖IndexedHilbertModule.mk (B := B) ξ‖ :=
  finiteAction_norm_le α π f ξ

/-- The actual bounded regular source operator on the completed indexed
module. It is obtained from the proved finite reduced-norm estimate. -/
def operatorCLM (f : AlgebraicCrossedProduct α) :
    IndexedHilbertModule.Module B E Γ →L[ℂ] IndexedHilbertModule.Module B E Γ :=
  (finiteActionToModule α π f).extendOfNorm
    (IndexedHilbertModule.mk (B := B))

@[simp] theorem operatorCLM_mk (f : AlgebraicCrossedProduct α)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    operatorCLM α π f (IndexedHilbertModule.mk (B := B) ξ) =
      IndexedHilbertModule.mk (B := B) (finiteAction α π f ξ) := by
  exact LinearMap.extendOfNorm_eq
    (f := finiteActionToModule α π f)
    (e := IndexedHilbertModule.mk (B := B) (E := E) (I := Γ))
    (IndexedHilbertModule.mk_denseRange (B := B) (E := E) (I := Γ))
    ⟨‖algebraicCrossedOperatorHom α f‖, finiteActionToModule_norm_le α π f⟩ ξ

/-- The finite reduced-norm estimate passes to every vector in the genuine
completion, with the same constant. -/
theorem operatorCLM_norm_apply_le (f : AlgebraicCrossedProduct α)
    (x : IndexedHilbertModule.Module B E Γ) :
    ‖operatorCLM α π f x‖ ≤ ‖algebraicCrossedOperatorHom α f‖ * ‖x‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (f := finiteActionToModule α π f)
    (e := IndexedHilbertModule.mk (B := B) (E := E) (I := Γ))
    (IndexedHilbertModule.mk_denseRange (B := B) (E := E) (I := Γ))
    ‖algebraicCrossedOperatorHom α f‖ (finiteActionToModule_norm_le α π f) x

/-- The actual source regular operator is contractive for the concrete
reduced norm on the algebraic crossed product. -/
theorem operatorCLM_norm_le (f : AlgebraicCrossedProduct α) :
    ‖operatorCLM α π f‖ ≤ ‖algebraicCrossedOperatorHom α f‖ := by
  exact LinearMap.opNorm_extendOfNorm_le
    (f := finiteActionToModule α π f)
    (e := IndexedHilbertModule.mk (B := B) (E := E) (I := Γ))
    (IndexedHilbertModule.mk_denseRange (B := B) (E := E) (I := Γ))
    (norm_nonneg (algebraicCrossedOperatorHom α f))
    (finiteActionToModule_norm_le α π f)

omit [Group Γ] [CompleteSpace E] in
/-- Continuous operators on the actual indexed module agree when they agree
on the finite vectors. -/
theorem indexedCLM_ext
    (S T : IndexedHilbertModule.Module B E Γ →L[ℂ]
      IndexedHilbertModule.Module B E Γ)
    (h : ∀ ξ : IndexedHilbertModule.Vectors E Γ,
      S (IndexedHilbertModule.mk (B := B) ξ) =
        T (IndexedHilbertModule.mk (B := B) ξ)) : S = T := by
  apply ContinuousLinearMap.ext
  intro x
  have he := (IndexedHilbertModule.mk_denseRange (B := B) (E := E) (I := Γ)).equalizer
    S.continuous T.continuous (funext h)
  exact congrFun he x

/-- The bounded extension is characterized by the actual finite action. -/
theorem operatorCLM_ext (f : AlgebraicCrossedProduct α)
    (T : IndexedHilbertModule.Module B E Γ →L[ℂ] IndexedHilbertModule.Module B E Γ)
    (h : ∀ ξ : IndexedHilbertModule.Vectors E Γ,
      T (IndexedHilbertModule.mk (B := B) ξ) =
        IndexedHilbertModule.mk (B := B) (finiteAction α π f ξ)) :
    T = operatorCLM α π f := by
  apply indexedCLM_ext
  intro ξ
  rw [operatorCLM_mk, h]

/-- The completed operator retains the exact translated and twisted formula
on each original coordinate inclusion. -/
@[simp] theorem operatorCLM_single_inclusion (g t : Γ) (a : A) (x : E) :
    operatorCLM α π (AlgebraicCrossedProduct.single α g a)
        (IndexedHilbertModule.inclusion (B := B) t x) =
      IndexedHilbertModule.inclusion (B := B) (g * t)
        (π (α.automorphism (g * t)⁻¹ a) x) := by
  simp only [IndexedHilbertModule.inclusion_apply, operatorCLM_mk,
    finiteAction_single, finiteGenerator_single]

/-- Evaluation after the completed operator has the original finite
convolution formula on every finite input. -/
@[simp] theorem evaluation_operatorCLM_mk (f : AlgebraicCrossedProduct α)
    (ξ : IndexedHilbertModule.Vectors E Γ) (t : Γ) :
    IndexedHilbertModule.evaluation (B := B) t
        (operatorCLM α π f (IndexedHilbertModule.mk (B := B) ξ)) =
      ∑ g ∈ (AlgebraicCrossedProduct.coeff α f).support,
        π (α.automorphism t⁻¹ (AlgebraicCrossedProduct.coeff α f g))
          (ξ (g⁻¹ * t)) := by
  rw [operatorCLM_mk, IndexedHilbertModule.evaluation_mk, finiteAction_apply]

@[simp] theorem operatorCLM_zero : operatorCLM α π 0 = 0 := by
  apply indexedCLM_ext
  intro ξ
  simp only [operatorCLM_mk, finiteAction_zero, LinearMap.zero_apply, map_zero,
    zero_apply]

@[simp] theorem operatorCLM_add (f h : AlgebraicCrossedProduct α) :
    operatorCLM α π (f + h) = operatorCLM α π f + operatorCLM α π h := by
  apply indexedCLM_ext
  intro ξ
  simp only [operatorCLM_mk, finiteAction_add, LinearMap.add_apply, map_add,
    add_apply]

@[simp] theorem finiteAction_smul (z : ℂ) (f : AlgebraicCrossedProduct α) :
    finiteAction α π (z • f) = z • finiteAction α π f :=
  map_smul (finiteActionLinear α π) z f

@[simp] theorem operatorCLM_smul (z : ℂ) (f : AlgebraicCrossedProduct α) :
    operatorCLM α π (z • f) = z • operatorCLM α π f := by
  apply indexedCLM_ext
  intro ξ
  simp only [operatorCLM_mk, finiteAction_smul, LinearMap.smul_apply, map_smul,
    smul_apply]

/-- Complex linearity of the actual bounded regular source action. -/
def operatorLinear : AlgebraicCrossedProduct α →ₗ[ℂ]
    (IndexedHilbertModule.Module B E Γ →L[ℂ] IndexedHilbertModule.Module B E Γ) where
  toFun := operatorCLM α π
  map_add' := operatorCLM_add α π
  map_smul' := operatorCLM_smul α π

@[simp] theorem operatorLinear_apply (f : AlgebraicCrossedProduct α) :
    operatorLinear α π f = operatorCLM α π f := rfl

end BC4lean.KKTheory.ReducedSourceRegular
