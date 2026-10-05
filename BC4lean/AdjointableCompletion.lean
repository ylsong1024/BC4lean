import BC4lean.HilbertModuleCompletion
import BC4lean.AdjointableAlgebra
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Adjointable maps on Hilbert-module completions

The completion keeps the actual coefficient-valued inner product. A bounded
adjoint pair extends to the completions, preserving its norm, adjoint and
composition. Uniqueness follows from the genuine dense canonical inclusion.
-/

noncomputable section
namespace BC4lean.KKTheory

open UniformSpace
open scoped InnerProductSpace

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

/-- The actual completed continuous linear map satisfies the original norm bound. -/
theorem completionCLM_norm_apply_le (T : E →L[ℂ] F) (x : Completion E) :
    ‖T.completion x‖ ≤ ‖T‖ * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp T.completion.continuous)
      (continuous_const.mul continuous_norm)
  | ih x =>
    simpa only [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe] using
      T.le_opNorm x

/-- Completing both domain and target preserves the continuous-linear operator norm. -/
theorem completionCLM_norm (T : E →L[ℂ] F) : ‖T.completion‖ = ‖T‖ := by
  apply le_antisymm
  · exact T.completion.opNorm_le_bound (norm_nonneg _) (completionCLM_norm_apply_le T)
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    have h := T.completion.le_opNorm (x : Completion E)
    simpa only [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe] using h

namespace AdjointableMap

/-- Extend the actual bounded adjoint pair to the complete Hilbert modules. -/
def completion (T : AdjointableMap B E F) :
    AdjointableMap B (Completion E) (Completion F) where
  toCLM := T.toCLM.completion
  adjointCLM := T.adjointCLM.completion
  adjoint_identity x y := by
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp
          ((T.toCLM.completion.continuous.comp continuous_fst).prodMk continuous_snd))
        (CStarModule.continuous_inner.comp
          (continuous_fst.prodMk (T.adjointCLM.completion.continuous.comp continuous_snd)))
    · intro x y
      simpa only [ContinuousLinearMap.completion_apply_coe, completionInner_coe] using
        T.adjoint_identity x y

@[simp] theorem completion_toCLM (T : AdjointableMap B E F) :
    T.completion.toCLM = T.toCLM.completion := rfl

@[simp] theorem completion_apply_coe (T : AdjointableMap B E F) (x : E) :
    T.completion (x : Completion E) = (T x : Completion F) :=
  T.toCLM.completion_apply_coe x

@[simp] theorem completion_adjoint (T : AdjointableMap B E F) :
    T.completion.adjoint = T.adjoint.completion := rfl

/-- Completion preserves the norm on rectangular adjointable maps. -/
@[simp] theorem norm_completion (T : AdjointableMap B E F) :
    ‖T.completion‖ = ‖T‖ := completionCLM_norm T.toCLM

/-- Density determines the completed adjointable map uniquely. -/
theorem completion_unique (T : AdjointableMap B E F)
    (S : AdjointableMap B (Completion E) (Completion F))
    (hS : ∀ x : E, S (x : Completion E) = (T x : Completion F)) :
    S = T.completion := by
  ext x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq S.toCLM.continuous T.completion.toCLM.continuous
  · intro x
    rw [hS, completion_apply_coe]

@[simp] theorem completion_zero :
    (0 : AdjointableMap B E F).completion = 0 := by
  apply (completion_unique (0 : AdjointableMap B E F) 0 (by intro x; simp [Completion.coe_zero])).symm

@[simp] theorem completion_add (S T : AdjointableMap B E F) :
    (S + T).completion = S.completion + T.completion := by
  apply (completion_unique (S + T) (S.completion + T.completion) ?_).symm
  intro x
  simp only [coe_add_apply, completion_apply_coe, Completion.coe_add]

@[simp] theorem completion_smul (c : ℂ) (T : AdjointableMap B E F) :
    (c • T).completion = c • T.completion := by
  apply (completion_unique (c • T) (c • T.completion) ?_).symm
  intro x
  simp only [coe_smul_apply, completion_apply_coe, Completion.coe_smul]

@[simp] theorem completion_comp (S : AdjointableMap B F G) (T : AdjointableMap B E F) :
    (S.comp T).completion = S.completion.comp T.completion := by
  apply (completion_unique (S.comp T) (S.completion.comp T.completion) ?_).symm
  intro x
  simp only [comp_apply, completion_apply_coe]

@[simp] theorem completion_id :
    (id : AdjointableMap B E E).completion = id := by
  apply (completion_unique (id : AdjointableMap B E E) id (by intro x; rfl)).symm

/-- The extension is a genuine complex-linear isometric map on rectangular operators. -/
def completionLinearIsometry :
    AdjointableMap B E F →ₗᵢ[ℂ] AdjointableMap B (Completion E) (Completion F) where
  toFun := completion
  map_add' := completion_add
  map_smul' := completion_smul
  norm_map' := norm_completion

/-- Endomorphism completion is an actual star-algebra homomorphism. -/
def completionHom :
    AdjointableMap B E E →⋆ₐ[ℂ] AdjointableMap B (Completion E) (Completion E) where
  toFun := completion
  map_zero' := completion_zero
  map_one' := completion_id
  map_add' := completion_add
  map_mul' := completion_comp
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, completion_smul,
      Algebra.algebraMap_eq_smul_one]
    change c • (id : AdjointableMap B E E).completion =
      c • (id : AdjointableMap B (Completion E) (Completion E))
    rw [completion_id]
  map_star' T := (completion_adjoint T).symm

end AdjointableMap
end BC4lean.KKTheory
