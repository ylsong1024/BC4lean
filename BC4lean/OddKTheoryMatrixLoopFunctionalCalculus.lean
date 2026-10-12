import BC4lean.OddKTheoryWeightedDefectTransfer

/-! # Full actual functional calculus of the matrix Fredholm defect

The common compact scalar domain is the actual complex spectrum together
with the crossing interval. Selfadjointness makes that entire domain real.
The proved bounded weighted entry map and its proved coordinate intertwining
therefore transfer full complex CFC. In particular the actual exponential
index difference is exactly a four-entry matrix-CFC operator.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- The genuine selfadjoint subtype of the actual matrix pullback operator. -/
def oddKTheoryMatrixLoopSelfAdjoint
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) : selfAdjoint (OddKTheoryMatrixRowOperator B ι) :=
  ⟨oddKTheoryMatrixLoopPullback u, oddKTheoryMatrixLoopPullback_isSelfAdjoint u⟩

/-- Actual common compact scalar domain; the spectrum is not replaced by a
formal interval or the spectrum of a quotient algebra. -/
def oddKTheoryMatrixLoopCFCDomain
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) : Set ℂ :=
  spectrum ℂ (oddKTheoryMatrixLoopPullback u) ∪ Set.range oddKTheoryLoopEigenvalue

theorem oddKTheoryMatrixLoopCFCDomain_isCompact
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    IsCompact (oddKTheoryMatrixLoopCFCDomain u) :=
  (spectrum.isCompact (oddKTheoryMatrixLoopPullback u)).union
    (isCompact_range continuous_oddKTheoryLoopEigenvalue)

instance oddKTheoryMatrixLoopCFCDomain_compactSpace
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    CompactSpace (oddKTheoryMatrixLoopCFCDomain u) :=
  isCompact_iff_compactSpace.mp (oddKTheoryMatrixLoopCFCDomain_isCompact u)

theorem oddKTheoryMatrixLoopCFCDomain_contains_spectrum
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    spectrum ℂ (oddKTheoryMatrixLoopPullback u) ⊆ oddKTheoryMatrixLoopCFCDomain u :=
  Set.subset_union_left

theorem oddKTheoryMatrixLoopCFCDomain_contains_segment
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    Set.range oddKTheoryLoopEigenvalue ⊆ oddKTheoryMatrixLoopCFCDomain u :=
  Set.subset_union_right

/-- Every point of the actual common CFC domain is real. -/
theorem oddKTheoryMatrixLoopCFCDomain_real
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (z : oddKTheoryMatrixLoopCFCDomain u) : star (z : ℂ) = (z : ℂ) := by
  rcases z.property with hz | hz
  · rw [(oddKTheoryMatrixLoopPullback_isSelfAdjoint u).mem_spectrum_eq_re hz]
    simp
  · rcases hz with ⟨t, ht⟩
    rw [← ht]
    simp [oddKTheoryLoopEigenvalue]

/-- Full genuine complex CFC multiplied by the actual Fredholm defect is
exactly the proved bounded four-entry coefficient map. -/
theorem oddKTheoryMatrixLoopPullback_cfc_mul_square_defect
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (f : ℂ → ℂ) (hf : Continuous f) :
    cfc (A := OddKTheoryMatrixRowOperator B ι) f (oddKTheoryMatrixLoopPullback (B := B) (ι := ι) u) *
        (oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixLoopPullback u - 1) =
      oddKTheoryMatrixWeightedDefectCLM (oddKTheoryMatrixLoopCFCDomain u)
        (oddKTheoryMatrixLoopCFCDomain_contains_segment u) u
        ⟨fun z => f z, hf.comp continuous_subtype_val⟩ :=
  oddFredholmWeightedFunctionalCalculus_cfc (A := OddKTheoryMatrixRowOperator B ι) (oddKTheoryMatrixLoopSelfAdjoint (B := B) (ι := ι) u)
    (oddKTheoryMatrixLoopCFCDomain u) (oddKTheoryMatrixLoopCFCDomain_contains_spectrum u)
    (oddKTheoryMatrixLoopCFCDomain_real u)
    (oddKTheoryMatrixWeightedDefectCLM (oddKTheoryMatrixLoopCFCDomain u)
      (oddKTheoryMatrixLoopCFCDomain_contains_segment u) u)
    (oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixLoopPullback u - 1)
    (oddKTheoryMatrixWeightedDefectCLM_one _ _ u)
    (oddKTheoryMatrixWeightedDefectCLM_coordinate_intertwine _ _ u) f hf

/-- The actual exponential index unitary difference has exactly four actual
matrix-CFC row entries, using the entire endpoint-zero factor. -/
theorem oddKTheoryMatrixLoopPullback_exponential_sub_one_weighted
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    (oddFredholmExponential (A := OddKTheoryMatrixRowOperator B ι) (oddKTheoryMatrixLoopSelfAdjoint (B := B) (ι := ι) u) : OddKTheoryMatrixRowOperator B ι) - 1 =
      oddKTheoryMatrixWeightedDefectCLM (oddKTheoryMatrixLoopCFCDomain u)
        (oddKTheoryMatrixLoopCFCDomain_contains_segment u) u
        ⟨fun z => oddFredholmExponentialFactor z,
          oddFredholmExponentialFactor_continuous.comp continuous_subtype_val⟩ := by
  let F : OddKTheoryMatrixRowOperator B ι := oddKTheoryMatrixLoopPullback (B := B) (ι := ι) u
  have hnormal : IsStarNormal F := (oddKTheoryMatrixLoopPullback_isSelfAdjoint u).isStarNormal
  let := hnormal
  have hH : cfc (fun z : ℂ => z ^ 2 - 1) F = F * F - 1 := by
    rw [cfc_sub (fun z : ℂ => z ^ 2) (fun _ : ℂ => 1) F
      (by fun_prop) continuous_const.continuousOn,
      cfc_pow_id (R := ℂ) F 2 hnormal, cfc_const_one ℂ F hnormal, pow_two]
  have hcomm := cfc_commute_cfc (fun z : ℂ => z ^ 2 - 1) oddFredholmExponentialFactor F
  rw [hH] at hcomm
  rw [oddFredholmExponential_sub_one_factor, pow_two]
  change (F * F - 1) * cfc oddFredholmExponentialFactor F = _
  rw [hcomm.eq]
  exact oddKTheoryMatrixLoopPullback_cfc_mul_square_defect u
    oddFredholmExponentialFactor oddFredholmExponentialFactor_continuous

end BC4lean.KKTheory
