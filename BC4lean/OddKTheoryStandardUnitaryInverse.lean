import BC4lean.OddKTheoryStandardFiniteSplit
import BC4lean.OddFredholmCutoffIndependence

/-! # The actual finite inverse equals the completed compact-unitary inverse

A concrete affine path stays inside the radius-one invertible neighbourhood
of the original unitary and is polar-normalized. The exact finite corner
splitting then removes an exactly degenerate infinite tail. Thus the chosen
finite OperatorK1 index has the actual completed-row odd inverse class.
-/

noncomputable section
universe uB
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local instance oddContinuationOddKTheoryStandardUnitaryInverseLocalInstance01 : PartialOrder (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryStandardUnitaryInverseLocalInstance02 : StarOrderedRing (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryStandardUnitaryInverseLocalInstance03 (n : ℕ) : CompleteSpace (FiniteStandardModule B (Fin n)) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryStandardUnitaryInverseLocalInstance04 (n : ℕ) : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B (Fin n))
    (ProjectionModule (1 - standardCountableCutoff (B := B) n))) := hilbertModuleSum_complete

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

def oddKTheoryStandardUnitaryCutoffAffine
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ) (t : I) : OddFredholmStandardOperator B :=
  (1 - (t : ℝ)) • (U : OddFredholmStandardOperator B) + (t : ℝ) • oddFredholmUnitaryCutoff U n

theorem oddKTheoryStandardUnitaryCutoffAffine_near
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) (t : I) :
    ‖oddKTheoryStandardUnitaryCutoffAffine U n t - (U : _)‖ < 1 := by
  have he : oddKTheoryStandardUnitaryCutoffAffine U n t - (U : _) =
      (t : ℝ) • (oddFredholmUnitaryCutoff U n - (U : _)) := by
    unfold oddKTheoryStandardUnitaryCutoffAffine
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  exact (mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _)).trans_lt (by simpa only [one_mul] using hn)

def oddKTheoryStandardUnitaryCutoffPolarPath
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    Path U (oddFredholmStandardCutoffPolarUnitary U n hn) where
  toFun t := oddFredholmPolarUnitary (oddKTheoryStandardUnitaryCutoffAffine U n t)
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
      (oddKTheoryStandardUnitaryCutoffAffine_near U n hn t))
  continuous_toFun := (continuousOn_oddFredholmPolarElement.comp_continuous
    (by unfold oddKTheoryStandardUnitaryCutoffAffine; fun_prop)
    (fun t => oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
      (oddKTheoryStandardUnitaryCutoffAffine_near U n hn t))).subtype_mk _
  source' := by
    apply Subtype.ext
    simp only [oddKTheoryStandardUnitaryCutoffAffine, unitInterval.coe_zero, sub_zero,
      one_smul, zero_smul, add_zero, oddFredholmPolarUnitary, oddFredholmPolarElement_unitary]
  target' := by
    apply Subtype.ext
    simp only [oddKTheoryStandardUnitaryCutoffAffine, unitInterval.coe_one, sub_self,
      zero_smul, one_smul, zero_add, oddFredholmPolarUnitary, oddFredholmStandardCutoffPolarUnitary]

theorem oddKTheoryStandardUnitaryCutoffPolarPath_compact
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) (t : I) :
    IsModuleCompact ((oddKTheoryStandardUnitaryCutoffPolarPath U n hn t : _) - 1) := by
  apply oddFredholmPolarElement_sub_one_isModuleCompact _
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
      (oddKTheoryStandardUnitaryCutoffAffine_near U n hn t))
  have he : oddKTheoryStandardUnitaryCutoffAffine U n t - 1 =
      (1 - (t : ℝ)) • ((U : OddFredholmStandardOperator B) - 1) +
        (t : ℝ) • (oddFredholmUnitaryCutoff U n - 1) := by
    unfold oddKTheoryStandardUnitaryCutoffAffine
    module
  rw [he, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (hU.smul _).add ((oddFredholmUnitaryCutoff_sub_one_isModuleCompact U hU n).smul _)

theorem oddKTheorySupportedStandardPullback_finite_class
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hTail : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    OddKK.mk (BundledOddKasparovCycle.of
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
        standardCountableHilbertModule_isCountablyGenerated U hU)) =
      oddKTheoryMatrixUnitaryClass (oddFredholmSupportedFiniteUnitary U hU n hTail)
        (oddFredholmSupportedFiniteUnitary_scalar U hU n hTail) := by
  let hN : IsCountablyGeneratedModule B (ProjectionModule (1 - standardCountableCutoff (B := B) n)) :=
    projectionModule_isCountablyGenerated _ (standardCountableCutoff_isStarProjection n).one_sub
      standardCountableHilbertModule_isCountablyGenerated
  have he : oddKTheoryTransportOperatorUnitary (oddKTheoryStandardFiniteSplitEquiv n) U =
      oddKTheorySumOperatorUnitary (oddFredholmSupportedUnitaryCompression U n hTail)
        (1 : unitary (AdjointableMap B (ProjectionModule (1 - standardCountableCutoff (B := B) n))
          (ProjectionModule (1 - standardCountableCutoff (B := B) n)))) :=
    Subtype.ext (oddKTheoryStandardFiniteSplit_transport_supported U n hTail)
  have ht := oddKTheoryCompactUnitaryTransportIso standardCountableHilbertModule_isCountablyGenerated
    (finiteStandardModule_isCountablyGenerated_nonunital.sum hN) (oddKTheoryStandardFiniteSplitEquiv n) U hU
  rw [he] at ht
  have hs := oddKTheoryCompactUnitarySumIso finiteStandardModule_isCountablyGenerated_nonunital hN
    (oddFredholmSupportedUnitaryCompression U n hTail) 1
    (oddFredholmSupportedUnitaryCompression_sub_one_isModuleCompact U hU n hTail)
    (by simpa only [sub_self] using IsModuleCompact.zero)
  have hfinite : oddKTheoryMatrixOperatorUnitary (oddFredholmSupportedFiniteUnitary U hU n hTail) =
      oddFredholmSupportedUnitaryCompression U n hTail := by
    apply Subtype.ext
    exact oddFredholmFiniteCompactUnitaryMatrix_operator _ _
  calc
    _ = OddKK.mk (BundledOddKasparovCycle.of
        ((oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
          finiteStandardModule_isCountablyGenerated_nonunital (oddFredholmSupportedUnitaryCompression U n hTail)
          (oddFredholmSupportedUnitaryCompression_sub_one_isModuleCompact U hU n hTail)).directSum
          (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hN 1
            (by simpa only [sub_self] using IsModuleCompact.zero)))) :=
      OddKK.mk_eq_of_iso (ht.trans hs)
    _ = OddKK.mk (BundledOddKasparovCycle.of
        (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
          finiteStandardModule_isCountablyGenerated_nonunital (oddFredholmSupportedUnitaryCompression U n hTail)
          (oddFredholmSupportedUnitaryCompression_sub_one_isModuleCompact U hU n hTail))) := by
      change OddKK.mk ((BundledOddKasparovCycle.of
        (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
          finiteStandardModule_isCountablyGenerated_nonunital (oddFredholmSupportedUnitaryCompression U n hTail)
          (oddFredholmSupportedUnitaryCompression_sub_one_isModuleCompact U hU n hTail))).directSum
        (BundledOddKasparovCycle.of (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hN 1
          (by simpa only [sub_self] using IsModuleCompact.zero)))) = _
      rw [OddKK.mk_directSum, OddKK.mk_eq_zero_of_degenerate _
          (oddKTheoryCompactUnitaryPullbackCycle_one_degenerate hN), add_zero]
    _ = _ := by
      have hm := OddKK.mk_eq_of_iso
        (oddKTheoryMatrixCompactPullbackCycleIso (oddFredholmSupportedFiniteUnitary U hU n hTail)
          (oddFredholmSupportedFiniteUnitary_scalar U hU n hTail))
      simpa only [hfinite] using hm.symm

theorem oddOperatorK1KKInverse_standardUnitaryIndex
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    oddOperatorK1KKInverse (oddFredholmStandardUnitaryIndex U hU) =
      OddKK.mk (BundledOddKasparovCycle.of
        (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
          standardCountableHilbertModule_isCountablyGenerated U hU)) := by
  let n := oddFredholmStandardIndexSize U hU
  let hn := oddFredholmStandardIndexSize_near U hU
  have hp := OddKK.mk_eq_of_full (FullOddKasparovHomotopy.ofOperatorHomotopy
    (oddFredholmCompactUnitaryPullbackOperatorHomotopy (Γ := PUnit)
      standardCountableHilbertModule_isCountablyGenerated (oddKTheoryStandardUnitaryCutoffPolarPath U n hn)
      (oddKTheoryStandardUnitaryCutoffPolarPath_compact U hU n hn)))
  have hf := oddKTheorySupportedStandardPullback_finite_class (oddFredholmStandardCutoffPolarUnitary U n hn)
    (oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact U hU n hn) n
    (oddFredholmStandardCutoffPolarUnitary_right_tail U n hn)
  have hfinite : oddFredholmSupportedFiniteUnitary (oddFredholmStandardCutoffPolarUnitary U n hn)
      (oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact U hU n hn) n
      (oddFredholmStandardCutoffPolarUnitary_right_tail U n hn) =
      oddFredholmStandardFiniteIndexUnitary U hU n hn := rfl
  rw [hfinite] at hf
  change oddOperatorK1KKInverse (oddFredholmScalarIdentityUnitaryIndex
    (oddFredholmStandardFiniteIndexUnitary U hU n hn) _) = _
  rw [oddOperatorK1KKInverse_scalarIdentityUnitary]
  exact hf.symm.trans hp.symm

end BC4lean.KKTheory
