import BC4lean.CliffordQuarterPhaseConnection
import BC4lean.GradedKasparovFirstSumProduct

/-! # Genuine localized positive lifts in the signed source comparison

The phase-conjugated first operator is σ_y(AK), with A commuting with K.
Its anticommutator with σ_y(G) is the actual Hilbert-sum diagonal of
{AK,G}. The two source-coordinate localized positive lifts therefore
sum and transport through the same genuine quarter-phase unitary.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordQuarterPhase
open CliffordExternalEvenBalancedTensor CliffordExternalEvenRepresentation

variable {C M : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]
  [CompleteSpace M]
  (K : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) M)

local instance cliffordQuarterPhasePositivityLocalInstance1 : CompleteSpace (HilbertModuleSum C M M) := hilbertModuleSum_complete

theorem upper_mul_even (A : AdjointableMap C M M)
    (hA : K.toAdjointable * A = A * K.toAdjointable) : upper K * A = A * upper K := by
  simp only [upper, plus, minus, CliffordOne.plusProjection, CliffordOne.minusProjection,
    add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hA]

theorem lower_mul_even (A : AdjointableMap C M M)
    (hA : K.toAdjointable * A = A * K.toAdjointable) : lower K * A = A * lower K := by
  simp only [lower, plus, minus, CliffordOne.plusProjection, CliffordOne.minusProjection,
    add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hA]

theorem sumEquiv_transport_diagonal (P Q : AdjointableMap C M M)
    (hP : K.toAdjointable * P = P * K.toAdjointable)
    (hQ : K.toAdjointable * Q = Q * K.toAdjointable) :
    (sumEquiv K).transport (sumMap P Q) = sumMap P Q := by
  have hp : upper K * P * lower K = P := by
    rw [upper_mul_even K P hP, mul_assoc, upper_mul_lower, mul_one]
  have hq : lower K * Q * upper K = Q := by
    rw [lower_mul_even K Q hQ, mul_assoc, lower_mul_upper, mul_one]
  ext x
  simp only [HilbertModuleEquiv.transport_apply, sumEquiv_symm_apply, sumMap_apply,
    sumEquiv_apply, sumMk_fst, sumMk_snd]
  apply Prod.ext
  · exact congrArg (fun T : AdjointableMap C M M => T x.fst) hp
  · exact congrArg (fun T : AdjointableMap C M M => T x.snd) hq

theorem sumEquiv_symm_transport_signed (A : AdjointableMap C M M)
    (hA : K.toAdjointable * A = A * K.toAdjointable) :
    (sumEquiv K).symm.transport (CliffordOddSourceCycle.operator A) =
      CliffordOddSourceCycle.operator (A * K.toAdjointable) := by
  have hp : lower K * A * lower K = A * K.toAdjointable := by
    rw [lower_mul_even K A hA, mul_assoc, lower_square]
  have hq : upper K * A * upper K = A * K.toAdjointable := by
    rw [upper_mul_even K A hA, mul_assoc, upper_square]
  ext x
  simp only [HilbertModuleEquiv.transport_apply, sumEquiv_symm_apply,
    HilbertModuleEquiv.symm_symm, sumEquiv_apply, CliffordOddSourceCycle.operator_apply,
    sumMk_fst, sumMk_snd, map_smul]
  apply Prod.ext
  · exact congrArg (fun T : AdjointableMap C M M => (-Complex.I) • T x.snd) hp
  · exact congrArg (fun T : AdjointableMap C M M => Complex.I • T x.fst) hq

theorem sumEquiv_transport_signed (A : AdjointableMap C M M)
    (hA : K.toAdjointable * A = A * K.toAdjointable) :
    (sumEquiv K).transport (CliffordOddSourceCycle.operator (A * K.toAdjointable)) =
      CliffordOddSourceCycle.operator A := by
  have h := congrArg (sumEquiv K).transport (sumEquiv_symm_transport_signed K A hA)
  simpa only [HilbertModuleEquiv.transport_symm_symm] using h.symm

theorem signed_anticommutator {C M : Type*}
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M]
    [CStarModule Cᵐᵒᵖ M] [CompleteSpace M]
    (A G : AdjointableMap C M M) :
    CliffordOddSourceCycle.operator A * CliffordOddSourceCycle.operator G +
      CliffordOddSourceCycle.operator G * CliffordOddSourceCycle.operator A =
      sumMap (A * G + G * A) (A * G + G * A) := by
  ext x
  apply Prod.ext <;>
    simp only [AdjointableMap.mul_apply, AdjointableMap.coe_add_apply,
      CliffordOddSourceCycle.operator_apply, sumMk_fst, sumMk_snd, sumMk_add,
      sumMap_apply, map_smul, smul_smul, neg_mul, mul_neg,
      Complex.I_mul_I, neg_neg, one_smul]

theorem localized_positive (A G P Q : AdjointableMap C M M)
    (hA : K.toAdjointable * A = A * K.toAdjointable)
    (hP : K.toAdjointable * P = P * K.toAdjointable)
    (hQ : K.toAdjointable * Q = Q * K.toAdjointable)
    (hposP : IsPositiveModuloModuleCompact
      (P * (A * K.toAdjointable * G + G * (A * K.toAdjointable)) * star P))
    (hposQ : IsPositiveModuloModuleCompact
      (Q * (A * K.toAdjointable * G + G * (A * K.toAdjointable)) * star Q)) :
    IsPositiveModuloModuleCompact (sumMap P Q *
      (CliffordOddSourceCycle.operator A * phasedOperator K G +
        phasedOperator K G * CliffordOddSourceCycle.operator A) * star (sumMap P Q)) := by
  have h := (hposP.sumMap hposQ).transport (sumEquiv K)
  have heq : sumMap
      (P * (A * K.toAdjointable * G + G * (A * K.toAdjointable)) * star P)
      (Q * (A * K.toAdjointable * G + G * (A * K.toAdjointable)) * star Q) =
      sumMap P Q *
        (CliffordOddSourceCycle.operator (A * K.toAdjointable) * CliffordOddSourceCycle.operator G +
          CliffordOddSourceCycle.operator G * CliffordOddSourceCycle.operator (A * K.toAdjointable)) *
        star (sumMap P Q) := by
    rw [signed_anticommutator, ← sumMap_star, ← sumMap_mul, ← sumMap_mul]
  rw [heq, HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_star,
    sumEquiv_transport_diagonal K P Q hP hQ,
    sumEquiv_transport_signed K A hA] at h
  exact h

end BC4lean.KKTheory.CliffordQuarterPhase
