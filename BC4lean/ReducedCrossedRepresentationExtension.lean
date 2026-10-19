import BC4lean.ReducedCrossedNorm
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine extension from the proved reduced bound

The input is a finite algebraic star homomorphism and a proved estimate in
the actual regular reduced norm. Dense extension constructs the continuous
linear map; multiplication and star are then proved by actual dense-range
induction. No completed representation is supplied or assumed.

-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A R : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra R]

def algebraicToReducedCrossedLinear (α : CStarAlgebraAction Γ A) :
    AlgebraicCrossedProduct α →ₗ[ℂ] ReducedCrossedProduct α where
  toFun := algebraicToReducedCrossed α
  map_add' := map_add (algebraicToReducedCrossed α)
  map_smul' := map_smul (algebraicToReducedCrossed α)

private def algebraicRepresentationLinear (α : CStarAlgebraAction Γ A)
    (φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] R) : AlgebraicCrossedProduct α →ₗ[ℂ] R where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ

def extendReducedRepresentationCLM (α : CStarAlgebraAction Γ A)
    (φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] R) : ReducedCrossedProduct α →L[ℂ] R :=
  (algebraicRepresentationLinear α φ).extendOfNorm (algebraicToReducedCrossedLinear α)

theorem extendReducedRepresentationCLM_algebraic (α : CStarAlgebraAction Γ A)
    (φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] R)
    (hφ : ∀ f, ‖φ f‖ ≤ algebraicCrossedReducedNorm α f) (f : AlgebraicCrossedProduct α) :
    extendReducedRepresentationCLM α φ (algebraicToReducedCrossed α f) = φ f := by
  apply LinearMap.extendOfNorm_eq (algebraicToReducedCrossed_denseRange α)
  refine ⟨1, ?_⟩
  intro g
  change ‖φ g‖ ≤ 1 * algebraicCrossedReducedNorm α g
  simpa only [one_mul] using hφ g

theorem extendReducedRepresentationCLM_mul (α : CStarAlgebraAction Γ A)
    (φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] R)
    (hφ : ∀ f, ‖φ f‖ ≤ algebraicCrossedReducedNorm α f) (z w : ReducedCrossedProduct α) :
    extendReducedRepresentationCLM α φ (z * w) =
      extendReducedRepresentationCLM α φ z * extendReducedRepresentationCLM α φ w := by
  refine (algebraicToReducedCrossed_denseRange α).induction_on₂
    (isClosed_eq ((extendReducedRepresentationCLM α φ).continuous.comp continuous_mul)
      (((extendReducedRepresentationCLM α φ).continuous.comp continuous_fst).mul
        ((extendReducedRepresentationCLM α φ).continuous.comp continuous_snd))) ?_ z w
  intro f g
  calc
    _ = extendReducedRepresentationCLM α φ (algebraicToReducedCrossed α (f * g)) :=
      congrArg (extendReducedRepresentationCLM α φ) (map_mul (algebraicToReducedCrossed α) f g).symm
    _ = φ (f * g) := extendReducedRepresentationCLM_algebraic α φ hφ (f * g)
    _ = φ f * φ g := map_mul φ f g
    _ = _ := by simp only [extendReducedRepresentationCLM_algebraic α φ hφ]

theorem extendReducedRepresentationCLM_star (α : CStarAlgebraAction Γ A)
    (φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] R)
    (hφ : ∀ f, ‖φ f‖ ≤ algebraicCrossedReducedNorm α f) (z : ReducedCrossedProduct α) :
    extendReducedRepresentationCLM α φ (star z) = star (extendReducedRepresentationCLM α φ z) := by
  refine (algebraicToReducedCrossed_denseRange α).induction_on z
    (isClosed_eq ((extendReducedRepresentationCLM α φ).continuous.comp continuous_star)
      (continuous_star.comp (extendReducedRepresentationCLM α φ).continuous)) ?_
  intro f
  calc
    _ = extendReducedRepresentationCLM α φ (algebraicToReducedCrossed α (star f)) :=
      congrArg (extendReducedRepresentationCLM α φ) (map_star (algebraicToReducedCrossed α) f).symm
    _ = φ (star f) := extendReducedRepresentationCLM_algebraic α φ hφ (star f)
    _ = star (φ f) := map_star φ f
    _ = _ := by rw [extendReducedRepresentationCLM_algebraic α φ hφ]

/-- The actual completed reduced star homomorphism constructed from the
finite homomorphism and its genuine reduced-norm bound. -/
def extendReducedRepresentation (α : CStarAlgebraAction Γ A)
    (φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] R)
    (hφ : ∀ f, ‖φ f‖ ≤ algebraicCrossedReducedNorm α f) :
    ReducedCrossedProduct α →⋆ₙₐ[ℂ] R where
  toFun := extendReducedRepresentationCLM α φ
  map_zero' := map_zero (extendReducedRepresentationCLM α φ)
  map_add' := map_add (extendReducedRepresentationCLM α φ)
  map_smul' := map_smul (extendReducedRepresentationCLM α φ)
  map_mul' := extendReducedRepresentationCLM_mul α φ hφ
  map_star' := extendReducedRepresentationCLM_star α φ hφ

@[simp] theorem extendReducedRepresentation_algebraic (α : CStarAlgebraAction Γ A)
    (φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ] R)
    (hφ : ∀ f, ‖φ f‖ ≤ algebraicCrossedReducedNorm α f) (f : AlgebraicCrossedProduct α) :
    extendReducedRepresentation α φ hφ (algebraicToReducedCrossed α f) = φ f :=
  extendReducedRepresentationCLM_algebraic α φ hφ f

end BC4lean.KKTheory
