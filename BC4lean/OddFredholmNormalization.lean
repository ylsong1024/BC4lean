import BC4lean.OddFredholmLocalCompactPerturbation
import BC4lean.GlobalModuleContractiveNormalization
import BC4lean.LocalizedModuleFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! # Actual selfadjoint contractive normalization of arbitrary odd cycles

Symmetrize the actual operator to S, then replace it by S k(S²), where
k(t)=1/√max(1,t). Localized continuous functional calculus proves the
normalizing difference locally compact, without a unital representation or
a global square-defect hypothesis. All four endpoint defects and the affine
operator homotopy are derived from the original cycle.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

local instance oddContinuationOddFredholmNormalizationLocalInstance01 :
    PartialOrder (AdjointableMap B E E) :=
  CStarAlgebra.spectralOrder (AdjointableMap B E E)
local instance oddContinuationOddFredholmNormalizationLocalInstance02 :
    StarOrderedRing (AdjointableMap B E E) :=
  CStarAlgebra.spectralOrderedRing (AdjointableMap B E E)

namespace OddKasparovCycle

/-- The normalization of the symmetrized actual cycle operator. -/
def normalizedOperator (c : OddKasparovCycle α β E) : AdjointableMap B E E :=
  globalFredholmNormalization c.symmetrized.operator

theorem normalizedOperator_norm_le_one (c : OddKasparovCycle α β E) :
    ‖c.normalizedOperator‖ ≤ 1 := norm_globalFredholmNormalization_le _

theorem normalizedOperator_selfadjoint (c : OddKasparovCycle α β E) :
    IsSelfAdjoint c.normalizedOperator := by
  let S := c.symmetrized.operator
  have hS : IsSelfAdjoint S := c.symmetrized_selfadjoint
  have hSS : Commute (S.adjoint.comp S) S := by
    change Commute (star S * S) S
    rw [hS.star_eq]
    exact mul_assoc S S S
  have hcomm := hSS.cfc_real fredholmNormWeight
  have hk : star (globalFredholmNormalizer S) = globalFredholmNormalizer S :=
    globalFredholmNormalizer_adjoint S
  change star (S * globalFredholmNormalizer S) = S * globalFredholmNormalizer S
  rw [star_mul, hk, hS.star_eq]
  exact hcomm.eq

/-- The normalizing weight differs from 1 by an actual locally compact
operator, using the symmetrized square defect localized at each a. -/
theorem normalizer_sub_one_locallyCompact (c : OddKasparovCycle α β E)
    (a : A) :
    IsModuleCompact ((globalFredholmNormalizer c.symmetrized.operator - 1) *
      c.representation a) := by
  let S := c.symmetrized.operator
  have hS : IsSelfAdjoint S := c.symmetrized_selfadjoint
  have hQ : IsSelfAdjoint (S.adjoint.comp S) :=
    (rectangular_adjoint_squares_nonneg S).2.isSelfAdjoint
  have hlocal : IsModuleCompact ((S.adjoint.comp S - 1) * c.representation a) := by
    change IsModuleCompact ((star S * S - 1) * c.representation a)
    rw [hS.star_eq]
    exact c.symmetrized.square_mod_compact a
  have h := cfc_sub_value_mul_isModuleCompact (S.adjoint.comp S) (c.representation a)
    hQ 1 (by simpa only [map_one] using hlocal) fredholmNormWeight
      continuous_fredholmNormWeight
  have hf1 : fredholmNormWeight 1 = 1 := by norm_num [fredholmNormWeight]
  simpa only [hf1, map_one, globalFredholmNormalizer] using h

/-- The normalized operator is locally compactly perturbed from S. -/
theorem normalizedOperator_sub_symmetrized_locallyCompact
    (c : OddKasparovCycle α β E) (a : A) :
    IsModuleCompact ((c.normalizedOperator - c.symmetrized.operator) * c.representation a) := by
  have heq : (c.normalizedOperator - c.symmetrized.operator) * c.representation a =
      c.symmetrized.operator *
        ((globalFredholmNormalizer c.symmetrized.operator - 1) * c.representation a) := by
    change (c.symmetrized.operator * globalFredholmNormalizer c.symmetrized.operator -
      c.symmetrized.operator) * c.representation a = _
    noncomm_ring
  rw [heq]
  exact mul_mem_moduleCompact_left c.symmetrized.operator
    (c.normalizer_sub_one_locallyCompact a)

/-- The full difference from the arbitrary original operator is localized
compact; global compactness of either difference is unnecessary. -/
theorem normalizedOperator_sub_locallyCompact (c : OddKasparovCycle α β E)
    (a : A) : IsModuleCompact ((c.normalizedOperator - c.operator) * c.representation a) := by
  have heq : (c.normalizedOperator - c.operator) * c.representation a =
      (c.normalizedOperator - c.symmetrized.operator) * c.representation a +
      c.symmetrizingPerturbation * c.representation a := by
    change (c.normalizedOperator - c.operator) * c.representation a =
      (c.normalizedOperator - (c.operator + c.symmetrizingPerturbation)) * c.representation a +
      c.symmetrizingPerturbation * c.representation a
    noncomm_ring
  rw [heq]
  exact (c.normalizedOperator_sub_symmetrized_locallyCompact a).add
    (c.symmetrizingPerturbation_locallyCompact a)

/-- Adjoint local compactness follows from the original selfadjoint defect
and exact selfadjointness of the normalized operator. -/
theorem normalizedOperator_sub_adjoint_locallyCompact
    (c : OddKasparovCycle α β E) (a : A) :
    IsModuleCompact (star (c.normalizedOperator - c.operator) * c.representation a) := by
  rw [star_sub, c.normalizedOperator_selfadjoint.star_eq]
  have heq : (c.normalizedOperator - star c.operator) * c.representation a =
      (c.normalizedOperator - c.operator) * c.representation a +
      (c.operator - star c.operator) * c.representation a := by noncomm_ring
  rw [heq]
  exact (c.normalizedOperator_sub_locallyCompact a).add (c.selfadjoint_mod_compact a)

/-- All genuine cycle conditions at the normalized endpoint are proved. -/
theorem operatorConditions_normalized (c : OddKasparovCycle α β E) :
    c.OperatorConditions c.normalizedOperator := by
  have h := c.operatorConditions_add_locallyCompact (c.normalizedOperator - c.operator)
    c.normalizedOperator_sub_locallyCompact c.normalizedOperator_sub_adjoint_locallyCompact
  have heq : c.operator + (c.normalizedOperator - c.operator) = c.normalizedOperator := by abel
  rw [heq] at h
  exact h

/-- The actual normalized raw cycle on the same complete module. -/
def normalized (c : OddKasparovCycle α β E) :
    OddKasparovCycle α β E :=
  c.withOperator c.normalizedOperator c.operatorConditions_normalized

theorem normalized_selfadjoint (c : OddKasparovCycle α β E) :
    IsSelfAdjoint c.normalized.operator := c.normalizedOperator_selfadjoint

theorem normalized_norm_le_one (c : OddKasparovCycle α β E) :
    ‖c.normalized.operator‖ ≤ 1 := c.normalizedOperator_norm_le_one

/-- The genuine affine operator homotopy from an arbitrary odd cycle to
its proved selfadjoint contractive normalization. -/
def normalizationHomotopy (c : OddKasparovCycle α β E) :
    OddKasparovOperatorHomotopy c c.operator c.normalized.operator :=
  OddKasparovOperatorHomotopy.compactPerturbation c c.normalizedOperator
    c.operatorConditions_normalized c.normalizedOperator_sub_locallyCompact

end OddKasparovCycle
end BC4lean.KKTheory
