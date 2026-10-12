import BC4lean.CompactModuleOperatorCriterion
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Tactic.Module

/-! # Compact absolute and positive parts of actual module operators

The absolute value has compact adjoint square, so the proved rectangular
compactness criterion makes it compact. For a selfadjoint operator, its
positive part is one half of the sum with its absolute value. This proves
compactness directly and does not assume a compact functional-calculus bridge.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance standardModuleCompactPositivePartLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardModuleCompactPositivePartLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- Compactness of the actual absolute value follows from its compact square. -/
theorem IsModuleCompact.cfcAbs {T : AdjointableMap B E E} (hT : IsModuleCompact T) :
    IsModuleCompact (CFC.abs T) := by
  apply IsModuleCompact.of_adjoint_comp_self
  change IsModuleCompact (star (CFC.abs T) * CFC.abs T)
  rw [(CFC.abs_nonneg T).isSelfAdjoint.star_eq, CFC.abs_mul_abs]
  exact hT.comp_left T.adjoint

/-- Compactness of the actual positive part is proved without an assumed
functional-calculus stability theorem for the compact ideal. -/
theorem IsModuleCompact.posPart {T : AdjointableMap B E E} (hT : IsModuleCompact T)
    (hSA : IsSelfAdjoint T) : IsModuleCompact T⁺ := by
  have he : T⁺ = (1 / 2 : ℂ) • (CFC.abs T + T) := by
    rw [CFC.abs_add_self T hSA]
    simp only [two_smul]
    module
  rw [he]
  exact (hT.cfcAbs.add hT).smul (1 / 2 : ℂ)

end BC4lean.KKTheory
