import BC4lean.StandardCountableFiniteCoordinates
import BC4lean.StandardCountableProjectionRounding

/-! # Genuine finite unitization projections from the rounded Julia corner

The reference matrix is the complete scalar matrix diag(0,I). The actual
finite coordinate map compresses a projection to a projection because the
proved reference-tail identities make that projection commute with the
coordinate range. Its compact reference difference has genuine B-matrix
coefficients. Adding those coefficients to the fixed scalar matrix gives a
genuine unitization projection, reflected jointly by its operator action and
its full scalar matrix part. This does not assume faithful unitization action.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped Matrix Topology

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The fixed finite Julia reference matrix, including its entire scalar part. -/
def pairedStandardFiniteReferenceMatrix (n : ℕ) :
    CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B) :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun i =>
    match i with
    | Sum.inl _ => 0
    | Sum.inr _ => 1)

omit [PartialOrder B] [StarOrderedRing B] in
/-- The reference is an actual unitization matrix projection. -/
theorem pairedStandardFiniteReferenceMatrix_isStarProjection (n : ℕ) :
    IsStarProjection (pairedStandardFiniteReferenceMatrix (B := B) n) := by
  apply isStarProjection_iff'.mpr
  constructor
  · let d : PairedStandardFiniteIndex n → Unitization ℂ B :=
      fun i => match i with | Sum.inl _ => 0 | Sum.inr _ => 1
    change (Matrix.diagonal d :
        Matrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B)) *
        Matrix.diagonal d = Matrix.diagonal d
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    cases i with
    | inl i => exact zero_mul (0 : Unitization ℂ B)
    | inr i => exact one_mul (1 : Unitization ℂ B)
  · apply CStarMatrix.ext
    intro i j
    let d : PairedStandardFiniteIndex n → Unitization ℂ B :=
      fun i => match i with | Sum.inl _ => 0 | Sum.inr _ => 1
    change star ((Matrix.diagonal d) j i) = (Matrix.diagonal d) i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      cases i with
      | inl i => exact star_zero _
      | inr i => exact star_one _
    · simpa only [Matrix.diagonal_apply_ne d (Ne.symm hij), Matrix.diagonal_apply_ne d hij] using
        (star_zero (Unitization ℂ B))

omit [PartialOrder B] [StarOrderedRing B] in
/-- The complete scalar reference matrix is also a genuine projection. -/
theorem pairedStandardFiniteReferenceScalarMatrix_isStarProjection (n : ℕ) :
    IsStarProjection (unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n)) := by
  have hq := pairedStandardFiniteReferenceMatrix_isStarProjection (B := B) n
  apply isStarProjection_iff'.mpr
  constructor
  · rw [← unitizationScalarMatrix_mul, hq.isIdempotentElem.eq]
  · rw [← unitizationScalarMatrix_star, hq.isSelfAdjoint.star_eq]

@[simp] theorem pairedStandardFiniteReferenceMatrix_apply (n : ℕ)
    (x : FiniteStandardModule B (PairedStandardFiniteIndex n))
    (i : PairedStandardFiniteIndex n) :
    unitizedModuleMatrixRepresentation (pairedStandardFiniteReferenceMatrix n) x i =
      match i with | Sum.inl _ => 0 | Sum.inr _ => x i := by
  rw [unitizedModuleMatrixRepresentation_apply]
  let d : PairedStandardFiniteIndex n → Unitization ℂ B :=
    fun i => match i with | Sum.inl _ => 0 | Sum.inr _ => 1
  change (∑ j : PairedStandardFiniteIndex n,
      unitizedStandardLeftMul ((Matrix.diagonal d) i j) (x j)) =
    match i with | Sum.inl _ => 0 | Sum.inr _ => x i
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
    cases i with
    | inl i =>
      change unitizedStandardLeftMul (0 : Unitization ℂ B) (x (Sum.inl i)) = 0
      simpa only [map_zero] using
        (AdjointableMap.coe_zero_apply (B := B) (x (Sum.inl i)))
    | inr i =>
      change unitizedStandardLeftMul (1 : Unitization ℂ B) (x (Sum.inr i)) = x (Sum.inr i)
      simpa only [map_one] using
        (AdjointableMap.one_apply (B := B) (x (Sum.inr i)))
  · intro j _ hji
    simpa only [Matrix.diagonal_apply_ne d (Ne.symm hji), map_zero] using
      (AdjointableMap.coe_zero_apply (B := B) (x j))
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Actual finite coordinate compression of an operator on the paired module. -/
def pairedStandardFiniteCompression (n : ℕ)
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))) :=
  (((pairedStandardFiniteInclusion (B := B) n).adjoint.comp P).comp
      (pairedStandardFiniteInclusion (B := B) n) :
    AdjointableMap B (FiniteStandardModule B (PairedStandardFiniteIndex n))
      (FiniteStandardModule B (PairedStandardFiniteIndex n)))

/-- Inclusion of the actual compressed finite operator is exactly its cutoff
corner on the paired standard module. -/
theorem pairedStandardFiniteCompression_reinclude (n : ℕ)
    (K : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))) :
    ((pairedStandardFiniteInclusion n).comp (pairedStandardFiniteCompression (B := B) n K)).comp
        (pairedStandardFiniteInclusion n).adjoint =
      standardCountablePairedCutoff n * K * standardCountablePairedCutoff n := by
  simp only [← pairedStandardFiniteInclusion_comp_adjoint]
  ext x
  rfl

/-- The compressed infinite reference is exactly the represented scalar matrix. -/
theorem pairedStandardFiniteCompression_reference (n : ℕ) :
    pairedStandardFiniteCompression (B := B) n (standardCountablePairedReferenceProjection (B := B)) =
      unitizedModuleMatrixRepresentation (pairedStandardFiniteReferenceMatrix n) := by
  ext x i
  have hJ := congrArg
    (fun T : AdjointableMap B (FiniteStandardModule B (PairedStandardFiniteIndex n))
      (FiniteStandardModule B (PairedStandardFiniteIndex n)) => T x i)
    (pairedStandardFiniteInclusion_adjoint_comp_self (B := B) n)
  simp only [AdjointableMap.comp_apply, pairedStandardFiniteInclusion_adjoint_apply,
    AdjointableMap.id_apply] at hJ
  simp only [pairedStandardFiniteCompression, AdjointableMap.comp_apply,
    pairedStandardFiniteInclusion_adjoint_apply, standardCountablePairedReferenceProjection,
    sumMap_apply, pairedStandardFiniteReferenceMatrix_apply]
  cases i with
  | inl i => simp only [pairedStandardCoordinateInclusion_adjoint_apply,
      AdjointableMap.coe_zero_apply, sumMk_fst, map_zero]
  | inr i => simpa only [pairedStandardCoordinateInclusion_adjoint_apply,
      AdjointableMap.one_apply, sumMk_snd] using hJ

/-- A projection commuting with the actual coordinate range compresses to a
genuine projection on the finite standard B-module. -/
theorem pairedStandardFiniteCompression_isStarProjection (n : ℕ)
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsStarProjection P)
    (hCommute : standardCountablePairedCutoff n * P = P * standardCountablePairedCutoff n) :
    IsStarProjection (pairedStandardFiniteCompression (B := B) n P) := by
  have hCJ (x : FiniteStandardModule B (PairedStandardFiniteIndex n)) :
      standardCountablePairedCutoff n (pairedStandardFiniteInclusion n x) =
        pairedStandardFiniteInclusion n x := by
    rw [← pairedStandardFiniteInclusion_comp_adjoint, AdjointableMap.comp_apply]
    have hJ := congrArg (fun T : AdjointableMap B
      (FiniteStandardModule B (PairedStandardFiniteIndex n))
      (FiniteStandardModule B (PairedStandardFiniteIndex n)) => T x)
      (pairedStandardFiniteInclusion_adjoint_comp_self (B := B) n)
    change (pairedStandardFiniteInclusion n).adjoint (pairedStandardFiniteInclusion n x) = x at hJ
    exact congrArg (pairedStandardFiniteInclusion n) hJ
  have hCP (y : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
      standardCountablePairedCutoff n (P y) = P (standardCountablePairedCutoff n y) :=
    congrArg (fun T => T y) hCommute
  apply isStarProjection_iff'.mpr
  constructor
  · apply AdjointableMap.ext
    intro x
    change (pairedStandardFiniteInclusion n).adjoint
      (P (pairedStandardFiniteInclusion n ((pairedStandardFiniteInclusion n).adjoint
        (P (pairedStandardFiniteInclusion n x))))) =
      (pairedStandardFiniteInclusion n).adjoint (P (pairedStandardFiniteInclusion n x))
    have hRange (y : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
        pairedStandardFiniteInclusion n ((pairedStandardFiniteInclusion n).adjoint y) =
          standardCountablePairedCutoff n y :=
      congrArg (fun T => T y) (pairedStandardFiniteInclusion_comp_adjoint (B := B) n)
    rw [hRange, hCP, hCJ]
    have hPP := congrArg (fun T => T (pairedStandardFiniteInclusion n x)) hP.isIdempotentElem.eq
    exact congrArg (pairedStandardFiniteInclusion (B := B) n).adjoint hPP
  · change (pairedStandardFiniteCompression (B := B) n P).adjoint = pairedStandardFiniteCompression (B := B) n P
    have hPAdjoint : P.adjoint = P := hP.isSelfAdjoint.star_eq
    simp only [pairedStandardFiniteCompression, AdjointableMap.adjoint_comp,
      AdjointableMap.adjoint_adjoint, hPAdjoint, AdjointableMap.comp_assoc]

/-- The proved rounded reference-tail identities imply actual cutoff commutation. -/
theorem spectralGapRoundedReferenceCompression_commutes_cutoff
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsSelfAdjoint P) (n : ℕ) :
    standardCountablePairedCutoff n * spectralGapRoundedProjection (standardCountableReferenceCompression P n) =
      spectralGapRoundedProjection (standardCountableReferenceCompression P n) * standardCountablePairedCutoff n := by
  have hl := spectralGapRoundedReferenceCompression_left_tail P hP n
  have hr := spectralGapRoundedReferenceCompression_right_tail P hP n
  simp only [sub_mul, one_mul] at hl
  simp only [mul_sub, mul_one] at hr
  have hc := standardCountablePairedCutoff_commutes_reference (B := B) n
  rw [hc] at hl
  exact sub_right_inj.mp (hl.trans hr.symm)

/-- The compact finite corner has genuine B-coefficients, and the scalar
matrix plus those coefficients is a genuine unitization projection. -/
theorem pairedStandardFiniteCompression_exists_unitization_projection (n : ℕ)
    (R : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hR : IsStarProjection R)
    (hCompact : IsModuleCompact (R - standardCountablePairedReferenceProjection))
    (hCommute : standardCountablePairedCutoff n * R = R * standardCountablePairedCutoff n) :
    ∃ M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B),
      IsStarProjection M ∧
      unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) ∧
      unitizedModuleMatrixRepresentation (B := B) M = pairedStandardFiniteCompression (B := B) n R := by
  have hK : IsModuleCompact (pairedStandardFiniteCompression (B := B) n
      (R - standardCountablePairedReferenceProjection)) :=
    (hCompact.comp_left (pairedStandardFiniteInclusion n).adjoint).comp_right (pairedStandardFiniteInclusion n)
  obtain ⟨K, hK⟩ := finiteModuleCompact_exists_matrix hK
  let M := pairedStandardFiniteReferenceMatrix (B := B) n + unitizationCoefficientMatrix K
  have hScalar : unitizationScalarMatrix M =
      unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) := by
    simp only [M, unitizationScalarMatrix_add, unitizationScalarMatrix_coefficient, add_zero]
  have hOperator : unitizedModuleMatrixRepresentation M = pairedStandardFiniteCompression (B := B) n R := by
    dsimp only [M]
    rw [map_add, unitizedModuleMatrixRepresentation_coefficient, hK,
      ← pairedStandardFiniteCompression_reference]
    apply AdjointableMap.ext
    intro x
    simp only [pairedStandardFiniteCompression, AdjointableMap.comp_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, map_sub]
    abel
  refine ⟨M, ?_, hScalar, hOperator⟩
  apply unitizationMatrix_isStarProjection_of_scalar_and_operator
  · rw [hScalar]
    exact pairedStandardFiniteReferenceScalarMatrix_isStarProjection n
  · rw [hOperator]
    exact pairedStandardFiniteCompression_isStarProjection n R hR hCommute

/-- Once the difference has its proved zero tails, the finite matrix realizes
the entire infinite relative projection, with the reference tail retained. -/
theorem pairedStandardFiniteProjection_realization (n : ℕ)
    (R : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B))
    (hOperator : unitizedModuleMatrixRepresentation (B := B) M = pairedStandardFiniteCompression (B := B) n R)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    R = standardCountablePairedReferenceProjection +
      ((pairedStandardFiniteInclusion (B := B) n).comp
        (unitizedModuleMatrixRepresentation (B := B) M -
          unitizedModuleMatrixRepresentation (B := B) (pairedStandardFiniteReferenceMatrix (B := B) n))).comp
        (pairedStandardFiniteInclusion (B := B) n).adjoint := by
  have hDifference : unitizedModuleMatrixRepresentation M -
      unitizedModuleMatrixRepresentation (pairedStandardFiniteReferenceMatrix n) =
        pairedStandardFiniteCompression (B := B) n (R - standardCountablePairedReferenceProjection) := by
    rw [hOperator, ← pairedStandardFiniteCompression_reference]
    apply AdjointableMap.ext
    intro x
    simp only [pairedStandardFiniteCompression, AdjointableMap.comp_apply,
      AdjointableMap.coe_sub_apply, map_sub]
  rw [hDifference, pairedStandardFiniteCompression_reinclude, ← hCorner]
  abel

/-- Every actual projection compactly differing from the Julia reference has
an actual continuous relative-projection path to an endpoint whose finite
coordinate compression is a genuine unitization projection with scalar
matrix diag(0,I). The finite coordinate number and spectral gap are derived. -/
theorem exists_standardCountableFiniteUnitizationProjectionPath
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsStarProjection P)
    (hCompact : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ,
    ∃ M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B),
    ∃ γ : Path P (spectralGapRoundedProjection (standardCountableReferenceCompression P n)),
      IsStarProjection M ∧
      unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) ∧
      unitizedModuleMatrixRepresentation (B := B) M = pairedStandardFiniteCompression (B := B) n
        (spectralGapRoundedProjection (standardCountableReferenceCompression P n)) ∧
      (∀ t : I, IsStarProjection (γ t) ∧
        IsModuleCompact (γ t - standardCountablePairedReferenceProjection)) ∧
      spectralGapRoundedProjection (standardCountableReferenceCompression P n) -
          standardCountablePairedReferenceProjection =
        standardCountablePairedCutoff n *
          (spectralGapRoundedProjection (standardCountableReferenceCompression P n) -
            standardCountablePairedReferenceProjection) * standardCountablePairedCutoff n := by
  obtain ⟨n, γ, hγ⟩ := exists_standardCountableRelativeProjectionPath P hP hCompact
  have hR := hγ 1
  rw [γ.target] at hR
  obtain ⟨M, hM, hScalar, hOperator⟩ := pairedStandardFiniteCompression_exists_unitization_projection n
    (spectralGapRoundedProjection (standardCountableReferenceCompression P n)) hR.1 hR.2
    (spectralGapRoundedReferenceCompression_commutes_cutoff P hP.isSelfAdjoint n)
  exact ⟨n, M, γ, hM, hScalar, hOperator, hγ,
    spectralGapRoundedReferenceCompression_sub_eq_cutoff P hP.isSelfAdjoint n⟩

/-- The finite matrix difference is included into the actual paired standard
module while the reference action is kept on every other coordinate. -/
def pairedStandardFiniteRelativeRealization (n : ℕ)
    (M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B)) :=
  standardCountablePairedReferenceProjection (B := B) +
    ((pairedStandardFiniteInclusion (B := B) n).comp
      (unitizedModuleMatrixRepresentation M -
        unitizedModuleMatrixRepresentation (pairedStandardFiniteReferenceMatrix n))).comp
      (pairedStandardFiniteInclusion (B := B) n).adjoint

/-- Genuine finite normalization: the endpoint itself is the finite relative
matrix realization, and the whole constructed path has compact reference
difference. No finite normal form or spectral gap is given as a hypothesis. -/
theorem exists_standardCountableFiniteRelativeProjectionHomotopy
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsStarProjection P)
    (hCompact : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ,
    ∃ M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B),
      IsStarProjection M ∧
      unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) ∧
      ∃ γ : Path P (pairedStandardFiniteRelativeRealization n M),
        ∀ t : I, IsStarProjection (γ t) ∧
          IsModuleCompact (γ t - standardCountablePairedReferenceProjection) := by
  obtain ⟨n, M, γ, hM, hScalar, hOperator, hγ, hCorner⟩ :=
    exists_standardCountableFiniteUnitizationProjectionPath P hP hCompact
  have hRealization : spectralGapRoundedProjection (standardCountableReferenceCompression P n) =
      pairedStandardFiniteRelativeRealization n M :=
    pairedStandardFiniteProjection_realization n _ M hOperator hCorner
  refine ⟨n, M, hM, hScalar, γ.cast rfl hRealization.symm, ?_⟩
  intro t
  exact hγ t

end BC4lean.KKTheory
