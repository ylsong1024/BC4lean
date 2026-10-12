import BC4lean.StandardCountableFiniteCornerHomotopy
import BC4lean.UnitizationFiniteMatrixNorm
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Genuine finite reference padding of a supported relative projection

The finite matrix is constructed from the actual compact coefficient matrix.
Enlarging its actual coordinate corner retains the entire reference matrix on
the new coordinates. The resulting finite projection class is therefore
unchanged after subtracting the reference class. Scalar and operator data are
used together throughout; the unitization action alone is not assumed faithful.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open scoped Matrix

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

/-- Compression preserves the original compact reference difference. -/
private theorem standardRelativeFiniteCompression_isModuleCompact (R : StdEnd)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ) :
    IsModuleCompact (pairedStandardFiniteCompression (B := B) n
      (R - standardCountablePairedReferenceProjection)) :=
  (hc.comp_left (pairedStandardFiniteInclusion n).adjoint).comp_right
    (pairedStandardFiniteInclusion n)

/-- The actual compact reference difference has a canonical finite matrix. -/
def standardCountableRelativeFiniteMatrix (R : StdEnd)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ) :
    CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B) :=
  pairedStandardFiniteReferenceMatrix n + unitizationCoefficientMatrix
    (finiteModuleCompactMatrix
      (pairedStandardFiniteCompression n (R - standardCountablePairedReferenceProjection))
      (standardRelativeFiniteCompression_isModuleCompact R hc n))

@[simp] theorem standardCountableRelativeFiniteMatrix_scalar (R : StdEnd)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ) :
    unitizationScalarMatrix (standardCountableRelativeFiniteMatrix R hc n) =
      unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) := by
  simp only [standardCountableRelativeFiniteMatrix, unitizationScalarMatrix_add,
    unitizationScalarMatrix_coefficient, add_zero]

@[simp] theorem standardCountableRelativeFiniteMatrix_operator (R : StdEnd)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ) :
    unitizedModuleMatrixRepresentation (standardCountableRelativeFiniteMatrix R hc n) =
      pairedStandardFiniteCompression n R := by
  rw [standardCountableRelativeFiniteMatrix,
    map_add (unitizedModuleMatrixRepresentation (B := B) (ι := PairedStandardFiniteIndex n)),
    unitizedModuleMatrixRepresentation_coefficient (B := B) (ι := PairedStandardFiniteIndex n),
    moduleMatrixRepresentation_finiteModuleCompactMatrix (B := B) (ι := PairedStandardFiniteIndex n),
    ← pairedStandardFiniteCompression_reference (B := B) n]
  apply AdjointableMap.ext
  intro x
  simp only [pairedStandardFiniteCompression, AdjointableMap.comp_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, map_sub]
  abel

theorem standardCountableRelativeFiniteMatrix_isStarProjection (R : StdEnd)
    (hR : IsStarProjection R)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hCommute : standardCountablePairedCutoff n * R = R * standardCountablePairedCutoff n) :
    IsStarProjection (standardCountableRelativeFiniteMatrix R hc n) := by
  apply unitizationMatrix_isStarProjection_of_scalar_and_operator
  · rw [standardCountableRelativeFiniteMatrix_scalar]
    exact pairedStandardFiniteReferenceScalarMatrix_isStarProjection n
  · rw [standardCountableRelativeFiniteMatrix_operator]
    exact pairedStandardFiniteCompression_isStarProjection n R hR hCommute

/-- The constructed matrix is independent of a matrix witness: full scalar
equality and its actual finite operator determine it uniquely. -/
theorem standardCountableRelativeFiniteMatrix_unique (R : StdEnd)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ)
    (M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B))
    (hs : unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n))
    (ho : unitizedModuleMatrixRepresentation M = pairedStandardFiniteCompression n R) :
    M = standardCountableRelativeFiniteMatrix R hc n :=
  unitizationMatrix_eq_of_scalar_and_operator_eq M _
    (hs.trans (standardCountableRelativeFiniteMatrix_scalar R hc n).symm)
    (ho.trans (standardCountableRelativeFiniteMatrix_operator R hc n).symm)

/-- The concrete index permutation keeps the two grading summands while
placing the old coordinates before the newly added coordinates. -/
def pairedStandardFinitePaddingEquiv (n m : ℕ) :
    PairedStandardFiniteIndex n ⊕ PairedStandardFiniteIndex m ≃ PairedStandardFiniteIndex (n + m) :=
  (Equiv.sumSumSumComm (Fin n) (Fin n) (Fin m) (Fin m)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

@[simp] theorem pairedStandardFinitePaddingEquiv_small_left (n m : ℕ) (i : Fin n) :
    pairedStandardFinitePaddingEquiv n m (Sum.inl (Sum.inl i)) =
      Sum.inl (Fin.castAdd m i) := rfl

@[simp] theorem pairedStandardFinitePaddingEquiv_small_right (n m : ℕ) (i : Fin n) :
    pairedStandardFinitePaddingEquiv n m (Sum.inl (Sum.inr i)) =
      Sum.inr (Fin.castAdd m i) := rfl

@[simp] theorem pairedStandardFinitePaddingEquiv_tail_left (n m : ℕ) (i : Fin m) :
    pairedStandardFinitePaddingEquiv n m (Sum.inr (Sum.inl i)) =
      Sum.inl (Fin.natAdd n i) := rfl

@[simp] theorem pairedStandardFinitePaddingEquiv_tail_right (n m : ℕ) (i : Fin m) :
    pairedStandardFinitePaddingEquiv n m (Sum.inr (Sum.inr i)) =
      Sum.inr (Fin.natAdd n i) := rfl

@[simp] theorem pairedStandardFiniteInclusion_single (n : ℕ)
    (i : PairedStandardFiniteIndex n) (b : Bᵐᵒᵖ) :
    pairedStandardFiniteInclusion n (finiteStandardInclusion i b) =
      pairedStandardCoordinateInclusion n i b := by
  simp [pairedStandardFiniteInclusion_apply, finiteStandardInclusion_apply,
    finiteStandardSingle_apply, Pi.single_apply, apply_ite]

theorem standardCountableRelativeFiniteMatrix_entry_action (R : StdEnd)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ)
    (i j : PairedStandardFiniteIndex n) (b : Bᵐᵒᵖ) :
    unitizedStandardLeftMul (standardCountableRelativeFiniteMatrix R hc n i j) b =
      (pairedStandardCoordinateInclusion n i).adjoint
        (R (pairedStandardCoordinateInclusion n j b)) := by
  have h := congrArg (fun T => T (finiteStandardInclusion j b) i)
    (standardCountableRelativeFiniteMatrix_operator R hc n)
  simp only [pairedStandardFiniteCompression, AdjointableMap.comp_apply,
    pairedStandardFiniteInclusion_single, pairedStandardFiniteInclusion_adjoint_apply] at h
  simpa only [unitizedModuleMatrixRepresentation_apply, finiteStandardInclusion_apply,
    finiteStandardSingle_apply, Pi.single_apply, apply_ite, map_zero,
    AdjointableMap.coe_zero_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

/-- The actual cutoff kills every later genuine coefficient coordinate. -/
theorem standardCountablePaddingCutoff_inclusion (n i : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableCutoff n (standardCountableInclusion i b) =
      if i < n then standardCountableInclusion i b else 0 := by
  rw [standardCountableInclusion_apply, standardCountableCutoff_mk]
  by_cases h : i < n
  · rw [Finsupp.filter_single_of_pos (fun k : ℕ => k < n) h, if_pos h]
  · rw [Finsupp.filter_single_of_neg (fun k : ℕ => k < n) h, if_neg h, map_zero]

/-- Evaluation at a later coordinate annihilates the entire old cutoff range. -/
theorem standardCountablePaddingEvaluation_cutoff_zero {n i : ℕ} (hi : n ≤ i)
    (x : StandardCountableHilbertModule B) :
    standardCountableEvaluation i (standardCountableCutoff n x) = 0 := by
  rw [standardCountableCutoff_apply, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [standardCountableEvaluation_inclusion]
  apply if_neg
  intro he
  subst j
  have hlt := Finset.mem_range.mp hj
  omega

/-- A supported compact reference difference has the exact original reference
operator on the entire right tail. -/
theorem standardCountableSupportedProjection_right_tail (R : StdEnd) (n : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    R * (1 - standardCountablePairedCutoff n) =
      standardCountablePairedReferenceProjection * (1 - standardCountablePairedCutoff n) := by
  have hz : (R - standardCountablePairedReferenceProjection) *
      (1 - standardCountablePairedCutoff n) = 0 := by
    rw [hCorner]
    simp only [mul_assoc, mul_sub, mul_one, standardCountablePairedCutoff_mul_self,
      sub_self]
  rwa [sub_mul, sub_eq_zero] at hz

/-- The exact left reference tail follows from the same actual corner equation. -/
theorem standardCountableSupportedProjection_left_tail (R : StdEnd) (n : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    (1 - standardCountablePairedCutoff n) * R =
      (1 - standardCountablePairedCutoff n) * standardCountablePairedReferenceProjection := by
  have hz : (1 - standardCountablePairedCutoff n) *
      (R - standardCountablePairedReferenceProjection) = 0 := by
    rw [hCorner]
    simp only [← mul_assoc, sub_mul, one_mul, standardCountablePairedCutoff_mul_self,
      sub_self, zero_mul]
  rwa [mul_sub, sub_eq_zero] at hz

omit [PartialOrder B] [StarOrderedRing B] in
/-- Reindexing a true finite projection has the same existing K₀ class. -/
theorem unitizationFiniteProjection_k0_reindex [PartialOrder B] [StarOrderedRing B] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (p : MatrixProjection (Unitization ℂ B) ι) (e : ι ≃ κ) :
    k0Projection (FiniteProjection.ofProjection
      (Projection.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e).toStarAlgHom p)) =
      k0Projection (FiniteProjection.ofProjection p) := by
  apply k0Projection_eq_of_equivalent
  apply rectEquivalent_symm
  apply rectEquivalent_of_reindex p _ e.symm
  apply Matrix.ext
  intro i j
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- Equal reference padding cancels in the actual Grothendieck group. -/
theorem unitizationRelativeProjectionK0_block_reference_padding
    [PartialOrder B] [StarOrderedRing B] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (r : MatrixProjection (Unitization ℂ B) κ) :
    k0Projection (FiniteProjection.ofProjection (projectionBlockSum p r)) -
        k0Projection (FiniteProjection.ofProjection (projectionBlockSum q r)) =
      k0Projection (FiniteProjection.ofProjection p) -
        k0Projection (FiniteProjection.ofProjection q) := by
  change k0Projection (FiniteProjection.blockSum (FiniteProjection.ofProjection p)
      (FiniteProjection.ofProjection r)) -
    k0Projection (FiniteProjection.blockSum (FiniteProjection.ofProjection q)
      (FiniteProjection.ofProjection r)) = _
  rw [k0Projection_blockSum, k0Projection_blockSum]
  abel

omit [PartialOrder B] [StarOrderedRing B] in
/-- The native matrix reindexing has the original entry at its image coordinates. -/
private theorem standardPadding_reindex_image_apply {ι κ : Type*}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (M : CStarMatrix ι ι (Unitization ℂ B)) (i j : ι) :
    CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e M (e i) (e j) = M i j := by
  change M (e.symm (e i)) (e.symm (e j)) = M i j
  simp only [Equiv.symm_apply_apply]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The genuine full scalar reference itself has exactly the same padding. -/
theorem pairedStandardFiniteReferenceMatrix_padding [PartialOrder B] [StarOrderedRing B]
    (n m : ℕ) :
    pairedStandardFiniteReferenceMatrix (B := B) (n + m) =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (pairedStandardFinitePaddingEquiv n m)
        (matrixBlockSum (pairedStandardFiniteReferenceMatrix n)
          (pairedStandardFiniteReferenceMatrix m)) := by
  apply CStarMatrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (pairedStandardFinitePaddingEquiv n m).surjective i
  obtain ⟨j, rfl⟩ := (pairedStandardFinitePaddingEquiv n m).surjective j
  rw [standardPadding_reindex_image_apply]
  rcases i with ((i | i) | (i | i)) <;> rcases j with ((j | j) | (j | j))
  all_goals
    simp only [pairedStandardFinitePaddingEquiv_small_left,
      pairedStandardFinitePaddingEquiv_small_right,
      pairedStandardFinitePaddingEquiv_tail_left,
      pairedStandardFinitePaddingEquiv_tail_right]
  all_goals
    simp [pairedStandardFiniteReferenceMatrix, matrixBlockSum, Matrix.fromBlocks,
      Matrix.diagonal_apply]
  all_goals
    intro he
    have hval := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    have hi := i.isLt
    have hj := j.isLt
    omega

private theorem pairedStandardPaddingMatrix_scalar (n m : ℕ)
    (M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B))
    (hs : unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n)) :
    unitizationScalarMatrix
      (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (pairedStandardFinitePaddingEquiv n m)
        (matrixBlockSum M (pairedStandardFiniteReferenceMatrix m))) =
      unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) (n + m)) := by
  rw [pairedStandardFiniteReferenceMatrix_padding]
  have hsEntry (i j : PairedStandardFiniteIndex n) :
      (M i j).fst = (pairedStandardFiniteReferenceMatrix (B := B) n i j).fst :=
    congrArg (fun K : CStarMatrix (PairedStandardFiniteIndex n)
      (PairedStandardFiniteIndex n) ℂ => K i j) hs
  apply CStarMatrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (pairedStandardFinitePaddingEquiv n m).surjective i
  obtain ⟨j, rfl⟩ := (pairedStandardFinitePaddingEquiv n m).surjective j
  change (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (pairedStandardFinitePaddingEquiv n m)
      (matrixBlockSum M (pairedStandardFiniteReferenceMatrix m))
      (pairedStandardFinitePaddingEquiv n m i) (pairedStandardFinitePaddingEquiv n m j)).fst =
    (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (pairedStandardFinitePaddingEquiv n m)
      (matrixBlockSum (pairedStandardFiniteReferenceMatrix n) (pairedStandardFiniteReferenceMatrix m))
      (pairedStandardFinitePaddingEquiv n m i) (pairedStandardFinitePaddingEquiv n m j)).fst
  rw [standardPadding_reindex_image_apply, standardPadding_reindex_image_apply]
  cases i <;> cases j <;>
    simp only [matrixBlockSum, CStarMatrix.ofMatrix_apply, CStarMatrix.ofMatrix_symm_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hsEntry]

private theorem pairedStandardPadding_tail_action (R : StdEnd) (n m : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n)
    (j : PairedStandardFiniteIndex m) (b : Bᵐᵒᵖ) :
    R (pairedStandardCoordinateInclusion (n + m)
      (pairedStandardFinitePaddingEquiv n m (Sum.inr j)) b) =
      standardCountablePairedReferenceProjection (pairedStandardCoordinateInclusion (n + m)
        (pairedStandardFinitePaddingEquiv n m (Sum.inr j)) b) := by
  have hz : standardCountablePairedCutoff n
      (pairedStandardCoordinateInclusion (n + m)
        (pairedStandardFinitePaddingEquiv n m (Sum.inr j)) b) = 0 := by
    have hzero : standardCountableCutoff (B := B) n (0 : StandardCountableHilbertModule B) = 0 :=
      (standardCountableCutoff (B := B) n).toCLM.map_zero
    cases j with
    | inl j =>
      rw [pairedStandardFinitePaddingEquiv_tail_left]
      simp only [standardCountablePairedCutoff, pairedStandardCoordinateInclusion,
        AdjointableMap.comp_apply, sumInl_apply, sumMap_apply,
        sumMk_fst, sumMk_snd, Fin.val_natAdd]
      rw [standardCountablePaddingCutoff_inclusion, if_neg (by omega), hzero]
      exact sumMk_zero
    | inr j =>
      rw [pairedStandardFinitePaddingEquiv_tail_right]
      simp only [standardCountablePairedCutoff, pairedStandardCoordinateInclusion,
        AdjointableMap.comp_apply, sumInr_apply, sumMap_apply,
        sumMk_fst, sumMk_snd, Fin.val_natAdd]
      rw [standardCountablePaddingCutoff_inclusion, if_neg (by omega), hzero]
      exact sumMk_zero
  have h := congrArg (fun T : StdEnd => T (pairedStandardCoordinateInclusion (n + m)
    (pairedStandardFinitePaddingEquiv n m (Sum.inr j)) b))
      (standardCountableSupportedProjection_right_tail R n hCorner)
  simpa only [AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.one_apply, hz, sub_zero] using h

private theorem pairedStandardPadding_tail_evaluation (R : StdEnd) (n m : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n)
    (i : PairedStandardFiniteIndex m) (x : StdPair) :
    (pairedStandardCoordinateInclusion (n + m)
      (pairedStandardFinitePaddingEquiv n m (Sum.inr i))).adjoint (R x) =
      (pairedStandardCoordinateInclusion (n + m)
        (pairedStandardFinitePaddingEquiv n m (Sum.inr i))).adjoint
          (standardCountablePairedReferenceProjection x) := by
  have hz (y : StdPair) :
      (pairedStandardCoordinateInclusion (n + m)
        (pairedStandardFinitePaddingEquiv n m (Sum.inr i))).adjoint
          (standardCountablePairedCutoff n y) = 0 := by
    cases i <;>
      simp only [pairedStandardFinitePaddingEquiv_tail_left,
        pairedStandardFinitePaddingEquiv_tail_right,
        pairedStandardCoordinateInclusion_adjoint_apply, standardCountablePairedCutoff,
        sumMap_apply, sumMk_fst, sumMk_snd, Fin.val_natAdd,
        standardCountablePaddingEvaluation_cutoff_zero (Nat.le_add_right n _)]
  have h := congrArg (fun T : StdEnd =>
    (pairedStandardCoordinateInclusion (n + m)
      (pairedStandardFinitePaddingEquiv n m (Sum.inr i))).adjoint (T x))
      (standardCountableSupportedProjection_left_tail R n hCorner)
  simpa only [AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.one_apply, map_sub, hz, sub_zero] using h

private theorem standardPaddingUnitization_eq_of_scalar_and_left_action
    (a b : Unitization ℂ B) (hScalar : a.fst = b.fst)
    (hAction : unitizedStandardLeftMul a = unitizedStandardLeftMul b) : a = b := by
  apply Unitization.ext hScalar
  apply sub_eq_zero.mp
  apply standardLeftMul_injective
  rw [map_zero]
  have h := unitizedStandardLeftMul_sub_of_fst_eq a b hScalar
  rw [hAction, sub_self] at h
  exact h.symm

/-- Full scalar value and the actual standard coefficient action jointly
determine a unitization element, including over a unital or zero algebra. -/
theorem standardRelativeUnitization_eq_of_scalar_and_left_action
    (a b : Unitization ℂ B) (hScalar : a.fst = b.fst)
    (hAction : unitizedStandardLeftMul a = unitizedStandardLeftMul b) : a = b :=
  standardPaddingUnitization_eq_of_scalar_and_left_action a b hScalar hAction

/-- Enlarging the actual support corner adds the original reference projection
exactly, after the concrete grading-preserving coordinate permutation. -/
theorem standardCountableRelativeFiniteMatrix_padding (R : StdEnd)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n m : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    standardCountableRelativeFiniteMatrix R hc (n + m) =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (pairedStandardFinitePaddingEquiv n m)
        (matrixBlockSum (standardCountableRelativeFiniteMatrix R hc n)
          (pairedStandardFiniteReferenceMatrix m)) := by
  have hs := (standardCountableRelativeFiniteMatrix_scalar R hc (n + m)).trans
    (pairedStandardPaddingMatrix_scalar n m _
      (standardCountableRelativeFiniteMatrix_scalar R hc n)).symm
  apply CStarMatrix.ext
  intro i j
  apply standardPaddingUnitization_eq_of_scalar_and_left_action
  · exact congrArg (fun K : CStarMatrix (PairedStandardFiniteIndex (n + m))
      (PairedStandardFiniteIndex (n + m)) ℂ => K i j) hs
  · apply AdjointableMap.ext
    intro b
    obtain ⟨i, rfl⟩ := (pairedStandardFinitePaddingEquiv n m).surjective i
    obtain ⟨j, rfl⟩ := (pairedStandardFinitePaddingEquiv n m).surjective j
    rw [standardCountableRelativeFiniteMatrix_entry_action]
    rw [standardPadding_reindex_image_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change _ = unitizedStandardLeftMul (standardCountableRelativeFiniteMatrix R hc n i j) b
        rw [standardCountableRelativeFiniteMatrix_entry_action]
        cases i <;> cases j <;> rfl
      | inr j =>
        rw [pairedStandardPadding_tail_action R n m hCorner]
        change _ = unitizedStandardLeftMul (0 : Unitization ℂ B) b
        simp only [map_zero, AdjointableMap.coe_zero_apply]
        cases i <;> cases j <;>
          simp only [pairedStandardFinitePaddingEquiv_small_left,
            pairedStandardFinitePaddingEquiv_small_right,
            pairedStandardFinitePaddingEquiv_tail_left,
            pairedStandardFinitePaddingEquiv_tail_right,
            pairedStandardCoordinateInclusion_adjoint_apply]
        all_goals
          simp only [pairedStandardCoordinateInclusion, AdjointableMap.comp_apply,
            sumInl_apply, sumInr_apply, standardCountablePairedReferenceProjection,
            sumMap_apply, sumMk_fst, sumMk_snd,
            AdjointableMap.coe_zero_apply, AdjointableMap.one_apply, map_zero]
        rename_i i j
        change standardCountableEvaluation i.val
          (standardCountableInclusion (n + j.val) b) = 0
        rw [standardCountableEvaluation_inclusion, if_neg (by
          have hi := i.isLt
          have hj := j.isLt
          omega)]
    | inr i =>
      cases j with
      | inl j =>
        rw [pairedStandardPadding_tail_evaluation R n m hCorner]
        change _ = unitizedStandardLeftMul (0 : Unitization ℂ B) b
        simp only [map_zero, AdjointableMap.coe_zero_apply]
        cases i <;> cases j <;>
          simp only [pairedStandardFinitePaddingEquiv_small_left,
            pairedStandardFinitePaddingEquiv_small_right,
            pairedStandardFinitePaddingEquiv_tail_left,
            pairedStandardFinitePaddingEquiv_tail_right,
            pairedStandardCoordinateInclusion_adjoint_apply]
        all_goals
          simp only [pairedStandardCoordinateInclusion, AdjointableMap.comp_apply,
            sumInl_apply, sumInr_apply, standardCountablePairedReferenceProjection,
            sumMap_apply, sumMk_fst, sumMk_snd,
            AdjointableMap.coe_zero_apply, AdjointableMap.one_apply, map_zero]
        rename_i i j
        change standardCountableEvaluation (n + i.val)
          (standardCountableInclusion j.val b) = 0
        rw [standardCountableEvaluation_inclusion, if_neg (by
          have hi := i.isLt
          have hj := j.isLt
          omega)]
      | inr j =>
        rw [pairedStandardPadding_tail_action R n m hCorner]
        change _ = unitizedStandardLeftMul (pairedStandardFiniteReferenceMatrix (B := B) m i j) b
        cases i <;> cases j <;>
          simp only [pairedStandardFinitePaddingEquiv_tail_left,
            pairedStandardFinitePaddingEquiv_tail_right,
            pairedStandardCoordinateInclusion_adjoint_apply]
        all_goals
          simp only [pairedStandardCoordinateInclusion, AdjointableMap.comp_apply,
            sumInl_apply, sumInr_apply, standardCountablePairedReferenceProjection,
            sumMap_apply, sumMk_fst, sumMk_snd,
            AdjointableMap.coe_zero_apply, AdjointableMap.one_apply,
            pairedStandardFiniteReferenceMatrix, CStarMatrix.ofMatrix_apply,
            Matrix.diagonal_apply, Sum.inl.injEq, Sum.inr.injEq,
            Sum.inl_ne_inr, Sum.inr_ne_inl, ite_self, ↓reduceIte,
            map_zero]
        rename_i i j
        change standardCountableEvaluation (n + i.val)
          (standardCountableInclusion (n + j.val) b) =
          unitizedStandardLeftMul (if i = j then (1 : Unitization ℂ B) else 0) b
        rw [standardCountableEvaluation_inclusion]
        by_cases hij : i = j
        · subst j
          simp only [if_true, map_one, AdjointableMap.one_apply]
        · have hne : n + j.val ≠ n + i.val := by
            intro he
            exact hij (Fin.ext (Nat.add_left_cancel he).symm)
          simp only [if_neg hne, if_neg hij, map_zero, AdjointableMap.coe_zero_apply]

/-- A genuine smaller support equation remains true in every larger corner. -/
theorem standardCountableRelativeCorner_enlarge (R : StdEnd) (n m : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff (n + m) * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff (n + m) := by
  have hRight := standardCountablePairedCutoff_mul_of_le (B := B) (Nat.le_add_right n m)
  have hLeft : standardCountablePairedCutoff (B := B) (n + m) *
      standardCountablePairedCutoff n = standardCountablePairedCutoff n := by
    have h := congrArg star hRight
    simpa only [star_mul, AdjointableMap.star_eq_adjoint,
      standardCountablePairedCutoff_adjoint] using h
  calc
    R - standardCountablePairedReferenceProjection =
        standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
          standardCountablePairedCutoff n := hCorner
    _ = standardCountablePairedCutoff (n + m) *
        (standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
          standardCountablePairedCutoff n) * standardCountablePairedCutoff (n + m) := by
      simp only [mul_assoc, ← mul_assoc (standardCountablePairedCutoff (n + m))
        (standardCountablePairedCutoff n), hLeft, hRight]
    _ = _ := by rw [← hCorner]

/-- The actual scalar-kernel class extracted from a supported corner. -/
def standardCountableSupportedProjectionIndex (R : StdEnd) (hR : IsStarProjection R)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) : OperatorK0 B :=
  unitizationRelativeProjectionK0 (standardCountableRelativeFiniteMatrix R hc n)
    (pairedStandardFiniteReferenceMatrix n)
    (standardCountableRelativeFiniteMatrix_isStarProjection R hR hc n
      (standardCountableRelativeCorner_commutes_cutoff n R hCorner))
    (pairedStandardFiniteReferenceMatrix_isStarProjection n)
    (standardCountableRelativeFiniteMatrix_scalar R hc n)

/-- Actual enlargement contributes an identical reference block on both sides
and hence preserves the existing scalar-kernel K₀ class. -/
theorem standardCountableSupportedProjectionIndex_padding (R : StdEnd) (hR : IsStarProjection R)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n m : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    standardCountableSupportedProjectionIndex R hR hc (n + m)
      (standardCountableRelativeCorner_enlarge R n m hCorner) =
        standardCountableSupportedProjectionIndex R hR hc n hCorner := by
  apply operatorK0Inclusion_injective
  let p : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) :=
    ⟨standardCountableRelativeFiniteMatrix R hc n,
      standardCountableRelativeFiniteMatrix_isStarProjection R hR hc n
        (standardCountableRelativeCorner_commutes_cutoff n R hCorner)⟩
  let q : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) :=
    ⟨pairedStandardFiniteReferenceMatrix n, pairedStandardFiniteReferenceMatrix_isStarProjection n⟩
  let r : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex m) :=
    ⟨pairedStandardFiniteReferenceMatrix m, pairedStandardFiniteReferenceMatrix_isStarProjection m⟩
  have hp : (⟨standardCountableRelativeFiniteMatrix R hc (n + m),
      standardCountableRelativeFiniteMatrix_isStarProjection R hR hc (n + m)
        (standardCountableRelativeCorner_commutes_cutoff (n + m) R
          (standardCountableRelativeCorner_enlarge R n m hCorner))⟩ :
      MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex (n + m))) =
      Projection.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B)
        (pairedStandardFinitePaddingEquiv n m)).toStarAlgHom (projectionBlockSum p r) := by
    apply Subtype.ext
    exact standardCountableRelativeFiniteMatrix_padding R hc n m hCorner
  have hq : (⟨pairedStandardFiniteReferenceMatrix (n + m),
      pairedStandardFiniteReferenceMatrix_isStarProjection (B := B) (n + m)⟩ :
      MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex (n + m))) =
      Projection.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B)
        (pairedStandardFinitePaddingEquiv n m)).toStarAlgHom (projectionBlockSum q r) := by
    apply Subtype.ext
    exact pairedStandardFiniteReferenceMatrix_padding n m
  change k0Projection (FiniteProjection.ofProjection _) -
    k0Projection (FiniteProjection.ofProjection _) =
      k0Projection (FiniteProjection.ofProjection p) - k0Projection (FiniteProjection.ofProjection q)
  rw [hp, hq, unitizationFiniteProjection_k0_reindex, unitizationFiniteProjection_k0_reindex]
  exact unitizationRelativeProjectionK0_block_reference_padding p q r

end BC4lean.KKTheory
