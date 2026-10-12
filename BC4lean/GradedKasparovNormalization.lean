import BC4lean.GradedKasparovLocalCompactPerturbation
import BC4lean.GlobalModuleContractiveNormalization
import BC4lean.LocalizedModuleFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! # Selfadjoint contractive normalization with localized defects

For an arbitrary genuine graded cycle, first symmetrize the operator to S.
Then use S k(S²), where k(t)=1/√max(1,t). The difference k(S²)−1 is
proved locally compact from (S²−1)φ(a), using continuous-function induction
on spectrum(S²)∪{1}. No global compact Fredholm defect is assumed.

Evenness of the normalizer is proved inside the closed star subalgebra of
operators commuting with the actual semilinear module grading. The module
grading is never promoted to a coefficient-linear adjointable operator.
-/

noncomputable section
namespace BC4lean.KKTheory

section LocalizedCFC

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

namespace GradedHilbertModule

variable {δ : CStarGrading B}

/-- The actual even operators form a complex star subalgebra also when the
module grading twists the coefficient action. -/
def evenOperatorSubalgebra (γ : GradedHilbertModule δ E) :
    StarSubalgebra ℂ (AdjointableMap B E E) where
  carrier := {T | γ.IsEven γ T}
  zero_mem' := isEven_zero
  one_mem' := γ.isEven_id
  add_mem' := fun hS hT => hS.add hT
  mul_mem' := fun hS hT => hS.comp hT
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact γ.isEven_id.smul c
  star_mem' := fun hT => hT.adjoint

omit [StarOrderedRing B] [CompleteSpace E] in
theorem evenOperatorSubalgebra_isClosed (γ : GradedHilbertModule δ E) :
    IsClosed (γ.evenOperatorSubalgebra : Set (AdjointableMap B E E)) := by
  change IsClosed {T : AdjointableMap B E E | ∀ x, γ.grading (T x) = T (γ.grading x)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  have hx : Continuous (fun T : AdjointableMap B E E => T x) :=
    AdjointableMap.toCLM_isometry.continuous.clm_apply continuous_const
  have hγx : Continuous (fun T : AdjointableMap B E E => T (γ.grading x)) :=
    AdjointableMap.toCLM_isometry.continuous.clm_apply continuous_const
  exact isClosed_eq (γ.grading.continuous.comp hx) hγx

/-- Real CFC preserves evenness for the genuine module grading. -/
theorem IsEven.cfc {γ : GradedHilbertModule δ E} {Q : AdjointableMap B E E}
    (hQ : γ.IsEven γ Q) (f : ℝ → ℝ) : γ.IsEven γ (cfc f Q) := by
  let : IsClosed (γ.evenOperatorSubalgebra : Set (AdjointableMap B E E)) :=
    γ.evenOperatorSubalgebra_isClosed
  exact cfc_mem (𝕜' := ℂ) (s := γ.evenOperatorSubalgebra) f hQ

end GradedHilbertModule
end LocalizedCFC

section NormalizeCycle

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovCycle

/-- The normalization of the symmetrized actual cycle operator. -/
def normalizedOperator (c : GradedKasparovCycle α β δA δB E) : AdjointableMap B E E :=
  globalFredholmNormalization c.symmetrized.operator

theorem normalizedOperator_norm_le_one (c : GradedKasparovCycle α β δA δB E) :
    ‖c.normalizedOperator‖ ≤ 1 := norm_globalFredholmNormalization_le _

theorem normalizer_even (c : GradedKasparovCycle α β δA δB E) :
    c.grading.IsEven c.grading (globalFredholmNormalizer c.symmetrized.operator) := by
  have hS : c.grading.IsOdd c.grading c.symmetrized.operator :=
    c.symmetrized.operator_odd
  have hQ : c.grading.IsEven c.grading
      (c.symmetrized.operator.adjoint.comp c.symmetrized.operator) :=
    hS.adjoint.comp_odd hS
  exact hQ.cfc fredholmNormWeight

theorem normalizedOperator_isOdd (c : GradedKasparovCycle α β δA δB E) :
    c.grading.IsOdd c.grading c.normalizedOperator :=
  c.symmetrized.operator_odd.comp_even c.normalizer_even

theorem normalizedOperator_selfadjoint (c : GradedKasparovCycle α β δA δB E) :
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
theorem normalizer_sub_one_locallyCompact (c : GradedKasparovCycle α β δA δB E)
    (a : A) :
    IsModuleCompact ((globalFredholmNormalizer c.symmetrized.operator - 1) *
      c.representation a) := by
  let S := c.symmetrized.operator
  have hS : IsSelfAdjoint S := c.symmetrized_selfadjoint
  have hQ : IsSelfAdjoint (S.adjoint.comp S) := by
    change star (star S * S) = star S * S
    rw [star_mul, star_star]
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
    (c : GradedKasparovCycle α β δA δB E) (a : A) :
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
theorem normalizedOperator_sub_locallyCompact (c : GradedKasparovCycle α β δA δB E)
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
    (c : GradedKasparovCycle α β δA δB E) (a : A) :
    IsModuleCompact (star (c.normalizedOperator - c.operator) * c.representation a) := by
  rw [star_sub, c.normalizedOperator_selfadjoint.star_eq]
  have heq : (c.normalizedOperator - star c.operator) * c.representation a =
      (c.normalizedOperator - c.operator) * c.representation a +
      (c.operator - star c.operator) * c.representation a := by noncomm_ring
  rw [heq]
  exact (c.normalizedOperator_sub_locallyCompact a).add (c.selfadjoint_mod_compact a)

/-- All genuine cycle conditions at the normalized endpoint are proved. -/
theorem operatorConditions_normalized (c : GradedKasparovCycle α β δA δB E) :
    c.OperatorConditions c.normalizedOperator := by
  have hodd : c.grading.IsOdd c.grading (c.normalizedOperator - c.operator) := by
    have h := c.normalizedOperator_isOdd.add (c.operator_odd.smul (-1))
    change c.grading.IsOdd c.grading
      (c.normalizedOperator + (-1 : ℂ) • c.operator) at h
    simpa only [neg_one_smul, sub_eq_add_neg] using h
  have h := c.operatorConditions_add_locallyCompact (c.normalizedOperator - c.operator)
    hodd c.normalizedOperator_sub_locallyCompact c.normalizedOperator_sub_adjoint_locallyCompact
  have heq : c.operator + (c.normalizedOperator - c.operator) = c.normalizedOperator := by abel
  rw [heq] at h
  exact h

/-- The actual normalized raw cycle on the same complete graded module. -/
def normalized (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle α β δA δB E :=
  c.withOperator c.normalizedOperator c.operatorConditions_normalized

theorem normalized_selfadjoint (c : GradedKasparovCycle α β δA δB E) :
    IsSelfAdjoint c.normalized.operator := c.normalizedOperator_selfadjoint

theorem normalized_norm_le_one (c : GradedKasparovCycle α β δA δB E) :
    ‖c.normalized.operator‖ ≤ 1 := c.normalizedOperator_norm_le_one

/-- The genuine affine operator homotopy from an arbitrary graded cycle to
its proved selfadjoint contractive normalization. -/
def normalizationHomotopy (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovOperatorHomotopy c c.operator c.normalized.operator :=
  GradedKasparovOperatorHomotopy.compactPerturbation c c.normalizedOperator
    c.operatorConditions_normalized c.normalizedOperator_sub_locallyCompact

end GradedKasparovCycle
end NormalizeCycle
end BC4lean.KKTheory
