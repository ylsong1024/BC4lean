import BC4lean.AdjointableAlgebra
import BC4lean.AdjointableNorm
import Mathlib.Analysis.Normed.Operator.Completeness

/-! # Completeness of adjointable maps

The map sending an adjointable operator to the pair consisting of the operator
and its adjoint has closed range in the product of spaces of bounded operators.
Equality of the two operator norms makes this map an isometry for the ordinary
operator norm. Thus maps between complete Hilbert C⋆-modules form a Banach space,
and adjointable endomorphisms form a unital C⋆-algebra.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

namespace AdjointableMap

/-- An adjointable map and its adjoint, regarded as a pair of bounded maps. -/
def toCLMPair (T : AdjointableMap B E F) : (E →L[ℂ] F) × (F →L[ℂ] E) :=
  (T.toCLM, T.adjointCLM)

/-- The image of the pair map is exactly the pairs satisfying the adjoint identity. -/
theorem range_toCLMPair :
    Set.range (toCLMPair (B := B) (E := E) (F := F)) =
      { p : (E →L[ℂ] F) × (F →L[ℂ] E) |
        ∀ x y, ⟪p.1 x, y⟫_(Bᵐᵒᵖ) = ⟪x, p.2 y⟫_(Bᵐᵒᵖ) } := by
  ext p
  constructor
  · rintro ⟨T, rfl⟩
    exact T.adjoint_identity
  · intro hp
    exact ⟨⟨p.1, p.2, hp⟩, rfl⟩

variable [StarOrderedRing B]

/-- The adjoint identity defines a closed set of pairs of bounded operators. -/
theorem isClosed_range_toCLMPair :
    IsClosed (Set.range (toCLMPair (B := B) (E := E) (F := F))) := by
  rw [range_toCLMPair]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_eq (by fun_prop) (by fun_prop)

/-- Pairing an operator with its adjoint preserves the ordinary operator distance. -/
theorem toCLMPair_isometry :
    Isometry (toCLMPair (B := B) (E := E) (F := F)) := by
  refine Isometry.of_dist_eq fun S T ↦ ?_
  rw [Prod.dist_eq]
  change max (dist S.toCLM T.toCLM) (dist S.adjointCLM T.adjointCLM) = dist S T
  simp only [dist_eq_norm, ← toCLM_sub, ← adjointCLM_sub,
    norm_adjointCLM, norm_def, max_self]

/-- Adjointable maps between complete Hilbert C⋆-modules form a complete normed space. -/
instance instCompleteSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (AdjointableMap B E F) :=
  toCLMPair_isometry.isUniformInducing.completeSpace isClosed_range_toCLMPair.isComplete

/-- Adjointable endomorphisms satisfy the C⋆-identity for the operator norm. -/
instance instCStarRing : CStarRing (AdjointableMap B E E) where
  norm_mul_self_le T := by
    change ‖T.toCLM‖ * ‖T.toCLM‖ ≤ ‖(T.adjoint.comp T).toCLM‖
    rw [norm_toCLM_adjoint_comp_self, pow_two]

/-- The adjointable endomorphisms of a Hilbert C⋆-module form a C⋆-algebra. -/
instance instCStarAlgebra [CompleteSpace E] : CStarAlgebra (AdjointableMap B E E) where

end AdjointableMap
end BC4lean.KKTheory
