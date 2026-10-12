import BC4lean.StandardModuleFrame
import BC4lean.CompactModuleOperatorCriterion

/-! # Compact synthesis frames over nonunital coefficients

The square of coefficient creation by ξ is standard left multiplication by
〈ξ,ξ〉. The proved rectangular compactness criterion therefore makes creation
compact. Composing with a coordinate evaluation and taking an actually
norm-convergent operator series gives compact synthesis. This proves the
compact dense-range operator needed as a stabilization prerequisite, without
asserting stabilization itself or compactness of coordinate projections.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The actual creation square is coefficient left multiplication on B_B. -/
theorem moduleVectorCreation_adjoint_comp_self (ξ : E) :
    (moduleVectorCreation (B := B) ξ).adjoint.comp (moduleVectorCreation ξ) =
      standardLeftMul (MulOpposite.unop ⟪ξ, ξ⟫_(Bᵐᵒᵖ)) := moduleVectorCreation_adjoint_comp ξ

/-- Coefficient creation is compact even for a nonunital coefficient algebra. -/
theorem moduleVectorCreation_isModuleCompact (ξ : E) : IsModuleCompact (moduleVectorCreation (B := B) ξ) :=
  moduleVectorCreation_compact ξ

theorem standardModuleSynthesisTerm_isModuleCompact (η : ℕ → E) (n : ℕ) :
    IsModuleCompact (standardModuleSynthesisTerm (B := B) η n) :=
  standardModuleSynthesisTerm_compact η n

variable [CompleteSpace E]

/-- Summable synthesis is an actual compact adjointable operator. -/
theorem standardModuleSynthesis_isModuleCompact (η : ℕ → E) (hη : Summable (fun n => ‖η n‖)) :
    IsModuleCompact (standardModuleSynthesis (B := B) η) := standardModuleSynthesis_compact η hη

/-- A countably generated complete Hilbert module has genuine compact
adjointable dense-range synthesis from H_B. -/
theorem exists_compact_standardModuleSynthesis_denseRange
    (hE : IsCountablyGeneratedModule B E) :
    ∃ T : AdjointableMap B (StandardCountableHilbertModule B) E, IsModuleCompact T ∧ DenseRange T :=
  exists_standardModuleCompactSynthesis_denseRange hE

end BC4lean.KKTheory
