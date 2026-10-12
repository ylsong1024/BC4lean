import BC4lean.StandardCountableRelativeProjectionPathIndex
import BC4lean.RelativeProjectionSum
import BC4lean.OddKTheorySignedCoordinates
import BC4lean.DoubledAdjointableUnitaryPath
import BC4lean.KasparovHomotopyDirectSum

/-! # Genuine reference augmentation of standard relative projections

The actual coefficient interleave sends the original relative projection to
even coordinates and a second copy of the reference to odd coordinates. On
an actual supported finite corner the whole matrix is the concrete reindexing
of the original projection plus its reference. The equal reference summand
cancels in the existing Grothendieck group. A genuine rounded projection path
then removes the finite-support restriction.
-/

noncomputable section
open scoped CStarAlgebra
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open unitInterval
open scoped Matrix

variable {B : Type*} [NonUnitalCStarAlgebra B]
  [hPartialB : PartialOrder B] [hStarB : StarOrderedRing B]
local notation "Std" => StandardCountableHilbertModule B
local notation "StdPair" => HilbertModuleSum B Std Std
local notation "StdEnd" => AdjointableMap B StdPair StdPair

-- Anchor the original native coefficient-inner-product norm on the four-copy sum.
local instance standardRelativeAugmentationNestedNorm :
    NormedAddCommGroup (HilbertModuleSum B StdPair StdPair) :=
  WithCStarModule.instNormedAddCommGroupProd (A := Bᵐᵒᵖ) (E := StdPair) (F := StdPair)

/-- Interleave the two actual homogeneous coordinate families separately. -/
def standardRelativePairSelfAbsorption :
    HilbertModuleEquiv B (HilbertModuleSum B StdPair StdPair) StdPair :=
  (relativeProjectionMiddleShuffle (B := B) (E := Std) (F := Std) (G := Std) (H := Std)).trans
    ((standardCountableSelfAbsorption (B := B)).sum (standardCountableSelfAbsorption (B := B)))

@[simp] theorem standardRelativePairSelfAbsorption_apply
    (x : HilbertModuleSum B StdPair StdPair) :
    standardRelativePairSelfAbsorption x =
      sumMk (B := B) (standardCountableSelfAbsorption (B := B) (sumMk (B := B) x.fst.fst x.snd.fst))
        (standardCountableSelfAbsorption (B := B) (sumMk (B := B) x.fst.snd x.snd.snd)) := rfl

theorem standardRelativePairSelfAbsorption_reference :
    (standardRelativePairSelfAbsorption (B := B)).transport
      (sumMap (standardCountablePairedReferenceProjection (B := B))
        standardCountablePairedReferenceProjection) = standardCountablePairedReferenceProjection := by
  have h (x : HilbertModuleSum B StdPair StdPair) :
      standardRelativePairSelfAbsorption
        (sumMap standardCountablePairedReferenceProjection standardCountablePairedReferenceProjection x) =
      standardCountablePairedReferenceProjection (standardRelativePairSelfAbsorption x) := by
    simp only [standardRelativePairSelfAbsorption_apply, standardCountablePairedReferenceProjection,
      sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_zero_apply,
      AdjointableMap.one_apply, sumMk_zero, map_zero]
  apply AdjointableMap.ext
  intro x
  change standardRelativePairSelfAbsorption
    (sumMap standardCountablePairedReferenceProjection standardCountablePairedReferenceProjection
      (standardRelativePairSelfAbsorption.symm x)) = _
  rw [h, HilbertModuleEquiv.apply_symm_apply]

/-- Add the genuine reference on the second copy and use the actual interleave. -/
def standardRelativeProjectionAugmentation (P : StdEnd) : StdEnd :=
  (standardRelativePairSelfAbsorption (B := B)).transport (sumMap P standardCountablePairedReferenceProjection)

theorem standardRelativeProjectionAugmentation_isStarProjection (P : StdEnd) (hP : IsStarProjection P) :
    IsStarProjection (standardRelativeProjectionAugmentation P) :=
  (sumMap_isStarProjection hP standardCountablePairedReferenceProjection_isStarProjection).map
    (standardRelativePairSelfAbsorption (B := B)).transportStarAlgEquiv.toStarAlgHom

theorem standardRelativeProjectionAugmentation_compact (P : StdEnd)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    IsModuleCompact (standardRelativeProjectionAugmentation P - standardCountablePairedReferenceProjection) := by
  have h : IsModuleCompact ((standardRelativePairSelfAbsorption (B := B)).transport
      (sumMap (P - standardCountablePairedReferenceProjection) (0 : StdEnd))) :=
    (standardRelativePairSelfAbsorption (B := B)).transportMap_isModuleCompact
      standardRelativePairSelfAbsorption
      (hc.sumMap (IsModuleCompact.zero (B := B) (E := StdPair) (F := StdPair)))
  have he : sumMap (P - standardCountablePairedReferenceProjection) (0 : StdEnd) =
      sumMap (B := B) P standardCountablePairedReferenceProjection -
        sumMap (B := B) standardCountablePairedReferenceProjection standardCountablePairedReferenceProjection := by
    rw [← sumMap_sub, sub_self]
  rw [he, HilbertModuleEquiv.transport_sub, standardRelativePairSelfAbsorption_reference] at h
  exact h

set_option maxHeartbeats 800000 in
theorem continuous_standardRelativeProjectionAugmentation :
    Continuous (standardRelativeProjectionAugmentation (B := B)) := by
  let U : HilbertModuleEquiv B (HilbertModuleSum B StdPair StdPair) StdPair :=
    standardRelativePairSelfAbsorption (B := B)
  have hTransport : Continuous (fun T :
      AdjointableMap B (HilbertModuleSum B StdPair StdPair)
        (HilbertModuleSum B StdPair StdPair) => U.transport T) := by
    let L : AdjointableMap B StdPair (HilbertModuleSum B StdPair StdPair) →L[ℂ] StdEnd :=
      AdjointableMap.compLeftContinuousLinearMap U.toAdjointable
    let R : AdjointableMap B (HilbertModuleSum B StdPair StdPair)
        (HilbertModuleSum B StdPair StdPair) →L[ℂ]
        AdjointableMap B StdPair (HilbertModuleSum B StdPair StdPair) :=
      AdjointableMap.compRightContinuousLinearMap U.symm.toAdjointable
    exact L.continuous.comp R.continuous
  let L : StdEnd →L[ℂ]
      AdjointableMap B StdPair (HilbertModuleSum B StdPair StdPair) :=
    AdjointableMap.compLeftContinuousLinearMap (sumInl (B := B) (E := StdPair) (F := StdPair))
  let R : AdjointableMap B StdPair (HilbertModuleSum B StdPair StdPair) →L[ℂ]
      AdjointableMap B (HilbertModuleSum B StdPair StdPair) (HilbertModuleSum B StdPair StdPair) :=
    AdjointableMap.compRightContinuousLinearMap (sumFst (B := B) (E := StdPair) (F := StdPair))
  have hFirst : Continuous (fun P : StdEnd =>
      ((sumInl (B := B) (E := StdPair) (F := StdPair)).comp P).comp
        (sumFst (B := B) (E := StdPair) (F := StdPair))) :=
    R.continuous.comp L.continuous
  have hSum : Continuous (fun P : StdEnd =>
      sumMap (B := B) P (standardCountablePairedReferenceProjection (B := B))) := by
    change Continuous (fun P : StdEnd =>
      ((sumInl (B := B) (E := StdPair) (F := StdPair)).comp P).comp
          (sumFst (B := B) (E := StdPair) (F := StdPair)) +
        ((sumInr (B := B) (E := StdPair) (F := StdPair)).comp
          (standardCountablePairedReferenceProjection (B := B))).comp
            (sumSnd (B := B) (E := StdPair) (F := StdPair)))
    exact hFirst.add continuous_const
  exact hTransport.comp hSum

theorem standardRelativeSelfAbsorption_inl (i : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableSelfAbsorption (B := B) (sumMk (standardCountableInclusion i b) 0) =
      standardCountableInclusion (2 * i) b := by
  change standardCountableInterleave Equiv.natSumNatEquivNat _ = _
  simp only [standardCountableInterleave_apply, sumMk_fst, sumMk_snd, map_zero,
    add_zero, standardCountableEmbedding_inclusion]
  rfl

theorem standardRelativeSelfAbsorption_inr (i : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableSelfAbsorption (B := B) (sumMk 0 (standardCountableInclusion i b)) =
      standardCountableInclusion (2 * i + 1) b := by
  change standardCountableInterleave Equiv.natSumNatEquivNat _ = _
  simp only [standardCountableInterleave_apply, sumMk_fst, sumMk_snd, map_zero,
    zero_add, standardCountableEmbedding_inclusion]
  rfl

theorem standardRelativeSelfAbsorption_symm_even (i : ℕ) (b : Bᵐᵒᵖ) :
    (standardCountableSelfAbsorption (B := B)).symm (standardCountableInclusion (2 * i) b) =
      sumMk (standardCountableInclusion i b) 0 := by
  rw [← standardRelativeSelfAbsorption_inl, HilbertModuleEquiv.symm_apply_apply]

theorem standardRelativeSelfAbsorption_symm_odd (i : ℕ) (b : Bᵐᵒᵖ) :
    (standardCountableSelfAbsorption (B := B)).symm (standardCountableInclusion (2 * i + 1) b) =
      sumMk 0 (standardCountableInclusion i b) := by
  rw [← standardRelativeSelfAbsorption_inr, HilbertModuleEquiv.symm_apply_apply]

theorem standardRelativeSelfAbsorption_evaluation_even (i : ℕ)
    (x : HilbertModuleSum B Std Std) :
    standardCountableEvaluation (2 * i) (standardCountableSelfAbsorption x) =
      standardCountableEvaluation i x.fst := by
  have h : (standardCountableSelfAbsorption (B := B)).symm.toAdjointable.comp
      (standardCountableInclusion (B := B) (2 * i)) =
        (sumInl (B := B) (E := Std) (F := Std)).comp (standardCountableInclusion (B := B) i) := by
    ext b
    exact standardRelativeSelfAbsorption_symm_even i b
  have hs := congrArg AdjointableMap.adjoint h
  have he : (standardCountableEvaluation (B := B) (2 * i)).comp
      (standardCountableSelfAbsorption (B := B)).toAdjointable =
        (standardCountableEvaluation (B := B) i).comp (sumFst (B := B) (E := Std) (F := Std)) := by
    simpa only [AdjointableMap.adjoint_comp, HilbertModuleEquiv.toAdjointable_adjoint,
      HilbertModuleEquiv.symm_symm, standardCountableEvaluation, sumInl_adjoint] using hs
  exact congrArg (fun T => T x) he

theorem standardRelativeSelfAbsorption_evaluation_odd (i : ℕ)
    (x : HilbertModuleSum B Std Std) :
    standardCountableEvaluation (2 * i + 1) (standardCountableSelfAbsorption x) =
      standardCountableEvaluation i x.snd := by
  have h : (standardCountableSelfAbsorption (B := B)).symm.toAdjointable.comp
      (standardCountableInclusion (B := B) (2 * i + 1)) =
        (sumInr (B := B) (E := Std) (F := Std)).comp (standardCountableInclusion (B := B) i) := by
    ext b
    exact standardRelativeSelfAbsorption_symm_odd i b
  have hs := congrArg AdjointableMap.adjoint h
  have he : (standardCountableEvaluation (B := B) (2 * i + 1)).comp
      (standardCountableSelfAbsorption (B := B)).toAdjointable =
        (standardCountableEvaluation (B := B) i).comp (sumSnd (B := B) (E := Std) (F := Std)) := by
    simpa only [AdjointableMap.adjoint_comp, HilbertModuleEquiv.toAdjointable_adjoint,
      HilbertModuleEquiv.symm_symm, standardCountableEvaluation, sumInr_adjoint] using hs
  exact congrArg (fun T => T x) he

/-- Finite even/odd coordinates are a genuine finite index permutation. -/
def standardRelativeEvenOddFinEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) where
  toFun := Sum.elim (fun i => ⟨2 * i.val, by omega⟩) (fun i => ⟨2 * i.val + 1, by omega⟩)
  invFun k := if h : k.val % 2 = 0 then Sum.inl ⟨k.val / 2, by omega⟩
    else Sum.inr ⟨k.val / 2, by omega⟩
  left_inv i := by
    cases i with
    | inl i => simp
    | inr i =>
      simp
      apply Fin.ext
      change (2 * i.val + 1) / 2 = i.val
      omega
  right_inv k := by
    dsimp only
    split_ifs with h <;> apply Fin.ext <;> dsimp <;> omega

def standardRelativePairedEvenOddFinEquiv (n : ℕ) :
    PairedStandardFiniteIndex n ⊕ PairedStandardFiniteIndex n ≃ PairedStandardFiniteIndex (2 * n) :=
  (Equiv.sumSumSumComm (Fin n) (Fin n) (Fin n) (Fin n)).trans
    (Equiv.sumCongr (standardRelativeEvenOddFinEquiv n) (standardRelativeEvenOddFinEquiv n))

theorem standardRelativePairSelfAbsorption_cutoff (n : ℕ) :
    (standardRelativePairSelfAbsorption (B := B)).transport
      (sumMap (standardCountablePairedCutoff (B := B) n) (standardCountablePairedCutoff n)) =
        standardCountablePairedCutoff (2 * n) := by
  have hA : standardCountableSelfAbsorption.transport
      (sumMap (standardCountableCutoff (B := B) n) (standardCountableCutoff n)) =
        standardCountableCutoff (2 * n) := by
    apply oddKTheoryOperator_ext_coordinates
    intro k b
    obtain ⟨i | i, rfl⟩ := Equiv.natSumNatEquivNat.surjective k
    · change standardCountableSelfAbsorption
        (sumMap (standardCountableCutoff n) (standardCountableCutoff n)
          (standardCountableSelfAbsorption.symm (standardCountableInclusion (2 * i) b))) =
            standardCountableCutoff (2 * n) (standardCountableInclusion (2 * i) b)
      rw [standardRelativeSelfAbsorption_symm_even]
      simp only [sumMap_apply, sumMk_fst, sumMk_snd, map_zero]
      rw [standardCountablePaddingCutoff_inclusion, standardCountablePaddingCutoff_inclusion]
      by_cases hi : i < n
      · rw [if_pos hi, if_pos (show 2 * i < 2 * n by omega)]
        exact standardRelativeSelfAbsorption_inl i b
      · rw [if_neg hi, if_neg (show ¬ 2 * i < 2 * n by omega), sumMk_zero,
          HilbertModuleEquiv.map_zero]
    · change standardCountableSelfAbsorption
        (sumMap (standardCountableCutoff n) (standardCountableCutoff n)
          (standardCountableSelfAbsorption.symm (standardCountableInclusion (2 * i + 1) b))) =
            standardCountableCutoff (2 * n) (standardCountableInclusion (2 * i + 1) b)
      rw [standardRelativeSelfAbsorption_symm_odd]
      simp only [sumMap_apply, sumMk_fst, sumMk_snd, map_zero]
      rw [standardCountablePaddingCutoff_inclusion, standardCountablePaddingCutoff_inclusion]
      by_cases hi : i < n
      · rw [if_pos hi, if_pos (show 2 * i + 1 < 2 * n by omega)]
        exact standardRelativeSelfAbsorption_inr i b
      · rw [if_neg hi, if_neg (show ¬ 2 * i + 1 < 2 * n by omega), sumMk_zero,
          HilbertModuleEquiv.map_zero]
  apply AdjointableMap.ext
  intro x
  have hIntertwine (y : HilbertModuleSum B StdPair StdPair) :
      standardRelativePairSelfAbsorption
        (sumMap (standardCountablePairedCutoff n) (standardCountablePairedCutoff n) y) =
          standardCountablePairedCutoff (2 * n) (standardRelativePairSelfAbsorption y) := by
    have hh (z : HilbertModuleSum B Std Std) :
        standardCountableSelfAbsorption (sumMap (standardCountableCutoff n) (standardCountableCutoff n) z) =
          standardCountableCutoff (2 * n) (standardCountableSelfAbsorption z) := by
      have h := congrArg (fun T => T (standardCountableSelfAbsorption z)) hA
      simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h
    simp only [standardRelativePairSelfAbsorption_apply, standardCountablePairedCutoff,
      sumMap_apply, sumMk_fst, sumMk_snd]
    apply congrArg₂ (sumMk (B := B))
    · simpa only [sumMap_apply, sumMk_fst, sumMk_snd] using
        hh (sumMk (B := B) y.fst.fst y.snd.fst)
    · simpa only [sumMap_apply, sumMk_fst, sumMk_snd] using
        hh (sumMk (B := B) y.fst.snd y.snd.snd)
  change standardRelativePairSelfAbsorption
    (sumMap (standardCountablePairedCutoff n) (standardCountablePairedCutoff n)
      (standardRelativePairSelfAbsorption.symm x)) = _
  rw [hIntertwine, HilbertModuleEquiv.apply_symm_apply]

/-- Actual finite support is carried to the genuine first 2n coordinates. -/
theorem standardRelativeProjectionAugmentation_corner (P : StdEnd) (n : ℕ)
    (hCorner : P - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (P - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    standardRelativeProjectionAugmentation P - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff (2 * n) *
        (standardRelativeProjectionAugmentation P - standardCountablePairedReferenceProjection) *
          standardCountablePairedCutoff (2 * n) := by
  have hSum : sumMap (B := B) (P - standardCountablePairedReferenceProjection) (0 : StdEnd) =
      sumMap (B := B) (standardCountablePairedCutoff n) (standardCountablePairedCutoff n) *
        sumMap (B := B) (P - standardCountablePairedReferenceProjection) (0 : StdEnd) *
          sumMap (B := B) (standardCountablePairedCutoff n) (standardCountablePairedCutoff n) := by
    rw [← sumMap_mul, ← sumMap_mul, ← hCorner, mul_zero, zero_mul]
  have h := congrArg (standardRelativePairSelfAbsorption (B := B)).transport hSum
  have he : sumMap (B := B) (P - standardCountablePairedReferenceProjection) (0 : StdEnd) =
      sumMap (B := B) P standardCountablePairedReferenceProjection -
        sumMap (B := B) standardCountablePairedReferenceProjection standardCountablePairedReferenceProjection := by
    rw [← sumMap_sub, sub_self]
  simpa only [he, HilbertModuleEquiv.transport_mul, standardRelativePairSelfAbsorption_cutoff,
    HilbertModuleEquiv.transport_sub, standardRelativePairSelfAbsorption_reference,
    standardRelativeProjectionAugmentation] using h

theorem standardRelativePairSelfAbsorption_coordinate_even (n : ℕ)
    (i : PairedStandardFiniteIndex n) (b : Bᵐᵒᵖ) :
    standardRelativePairSelfAbsorption (sumMk (B := B) (pairedStandardCoordinateInclusion (B := B) n i b) (0 : StdPair)) =
      pairedStandardCoordinateInclusion (2 * n) (standardRelativePairedEvenOddFinEquiv n (Sum.inl i)) b := by
  cases i with
  | inl i =>
    change standardRelativePairSelfAbsorption
      (sumMk (B := B) (pairedStandardCoordinateInclusion (B := B) n (Sum.inl i) b) (0 : StdPair)) =
        sumMk (B := B) (standardCountableInclusion (B := B) (2 * i.val) b) (0 : Std)
    simp only [standardRelativePairSelfAbsorption_apply, pairedStandardCoordinateInclusion,
      AdjointableMap.comp_apply, sumInl_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.zero_fst, WithCStarModule.zero_snd, sumMk_zero,
      HilbertModuleEquiv.map_zero, standardRelativeSelfAbsorption_inl]
  | inr i =>
    change standardRelativePairSelfAbsorption
      (sumMk (B := B) (pairedStandardCoordinateInclusion (B := B) n (Sum.inr i) b) (0 : StdPair)) =
        sumMk (B := B) (0 : Std) (standardCountableInclusion (B := B) (2 * i.val) b)
    simp only [standardRelativePairSelfAbsorption_apply, pairedStandardCoordinateInclusion,
      AdjointableMap.comp_apply, sumInr_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.zero_fst, WithCStarModule.zero_snd, sumMk_zero,
      HilbertModuleEquiv.map_zero, standardRelativeSelfAbsorption_inl]

theorem standardRelativePairSelfAbsorption_coordinate_odd (n : ℕ)
    (i : PairedStandardFiniteIndex n) (b : Bᵐᵒᵖ) :
    standardRelativePairSelfAbsorption (sumMk (B := B) (0 : StdPair) (pairedStandardCoordinateInclusion (B := B) n i b)) =
      pairedStandardCoordinateInclusion (2 * n) (standardRelativePairedEvenOddFinEquiv n (Sum.inr i)) b := by
  cases i with
  | inl i =>
    change standardRelativePairSelfAbsorption
      (sumMk (B := B) (0 : StdPair) (pairedStandardCoordinateInclusion (B := B) n (Sum.inl i) b)) =
        sumMk (B := B) (standardCountableInclusion (B := B) (2 * i.val + 1) b) (0 : Std)
    simp only [standardRelativePairSelfAbsorption_apply, pairedStandardCoordinateInclusion,
      AdjointableMap.comp_apply, sumInl_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.zero_fst, WithCStarModule.zero_snd, sumMk_zero,
      HilbertModuleEquiv.map_zero, standardRelativeSelfAbsorption_inr]
  | inr i =>
    change standardRelativePairSelfAbsorption
      (sumMk (B := B) (0 : StdPair) (pairedStandardCoordinateInclusion (B := B) n (Sum.inr i) b)) =
        sumMk (B := B) (0 : Std) (standardCountableInclusion (B := B) (2 * i.val + 1) b)
    simp only [standardRelativePairSelfAbsorption_apply, pairedStandardCoordinateInclusion,
      AdjointableMap.comp_apply, sumInr_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.zero_fst, WithCStarModule.zero_snd, sumMk_zero,
      HilbertModuleEquiv.map_zero, standardRelativeSelfAbsorption_inr]

theorem standardRelativePairSelfAbsorption_symm_coordinate_even (n : ℕ)
    (i : PairedStandardFiniteIndex n) (b : Bᵐᵒᵖ) :
    standardRelativePairSelfAbsorption.symm
      (pairedStandardCoordinateInclusion (2 * n) (standardRelativePairedEvenOddFinEquiv n (Sum.inl i)) b) =
        sumMk (B := B) (pairedStandardCoordinateInclusion (B := B) n i b) (0 : StdPair) := by
  rw [← standardRelativePairSelfAbsorption_coordinate_even, HilbertModuleEquiv.symm_apply_apply]

theorem standardRelativePairSelfAbsorption_symm_coordinate_odd (n : ℕ)
    (i : PairedStandardFiniteIndex n) (b : Bᵐᵒᵖ) :
    standardRelativePairSelfAbsorption.symm
      (pairedStandardCoordinateInclusion (2 * n) (standardRelativePairedEvenOddFinEquiv n (Sum.inr i)) b) =
        sumMk (B := B) (0 : StdPair) (pairedStandardCoordinateInclusion (B := B) n i b) := by
  rw [← standardRelativePairSelfAbsorption_coordinate_odd, HilbertModuleEquiv.symm_apply_apply]

theorem standardRelativePairSelfAbsorption_evaluation_coordinate_even (n : ℕ)
    (i : PairedStandardFiniteIndex n) (x : HilbertModuleSum B StdPair StdPair) :
    (pairedStandardCoordinateInclusion (2 * n)
      (standardRelativePairedEvenOddFinEquiv n (Sum.inl i))).adjoint
        (standardRelativePairSelfAbsorption x) = (pairedStandardCoordinateInclusion n i).adjoint x.fst := by
  cases i with
  | inl i =>
    change standardCountableEvaluation (2 * i.val)
      (standardCountableSelfAbsorption (sumMk x.fst.fst x.snd.fst)) = standardCountableEvaluation i.val x.fst.fst
    exact standardRelativeSelfAbsorption_evaluation_even i.val _
  | inr i =>
    change standardCountableEvaluation (2 * i.val)
      (standardCountableSelfAbsorption (sumMk x.fst.snd x.snd.snd)) = standardCountableEvaluation i.val x.fst.snd
    exact standardRelativeSelfAbsorption_evaluation_even i.val _

theorem standardRelativePairSelfAbsorption_evaluation_coordinate_odd (n : ℕ)
    (i : PairedStandardFiniteIndex n) (x : HilbertModuleSum B StdPair StdPair) :
    (pairedStandardCoordinateInclusion (2 * n)
      (standardRelativePairedEvenOddFinEquiv n (Sum.inr i))).adjoint
        (standardRelativePairSelfAbsorption x) = (pairedStandardCoordinateInclusion n i).adjoint x.snd := by
  cases i with
  | inl i =>
    change standardCountableEvaluation (2 * i.val + 1)
      (standardCountableSelfAbsorption (sumMk x.fst.fst x.snd.fst)) = standardCountableEvaluation i.val x.snd.fst
    exact standardRelativeSelfAbsorption_evaluation_odd i.val _
  | inr i =>
    change standardCountableEvaluation (2 * i.val + 1)
      (standardCountableSelfAbsorption (sumMk x.fst.snd x.snd.snd)) = standardCountableEvaluation i.val x.snd.snd
    exact standardRelativeSelfAbsorption_evaluation_odd i.val _

theorem pairedStandardFiniteReferenceMatrix_evenOdd
    {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (n : ℕ) :
    pairedStandardFiniteReferenceMatrix (B := B) (2 * n) =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (standardRelativePairedEvenOddFinEquiv n)
        (matrixBlockSum (pairedStandardFiniteReferenceMatrix n) (pairedStandardFiniteReferenceMatrix n)) := by
  apply CStarMatrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (standardRelativePairedEvenOddFinEquiv n).surjective i
  obtain ⟨j, rfl⟩ := (standardRelativePairedEvenOddFinEquiv n).surjective j
  change pairedStandardFiniteReferenceMatrix (B := B) (2 * n)
      (standardRelativePairedEvenOddFinEquiv n i) (standardRelativePairedEvenOddFinEquiv n j) =
    matrixBlockSum (pairedStandardFiniteReferenceMatrix (B := B) n)
      (pairedStandardFiniteReferenceMatrix (B := B) n)
      ((standardRelativePairedEvenOddFinEquiv n).symm (standardRelativePairedEvenOddFinEquiv n i))
      ((standardRelativePairedEvenOddFinEquiv n).symm (standardRelativePairedEvenOddFinEquiv n j))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with ((i | i) | (i | i)) <;> rcases j with ((j | j) | (j | j)) <;>
    simp [pairedStandardFiniteReferenceMatrix, matrixBlockSum, Matrix.fromBlocks,
      Matrix.diagonal_apply, Fin.ext_iff, standardRelativePairedEvenOddFinEquiv,
      standardRelativeEvenOddFinEquiv, Equiv.sumSumSumComm]
  all_goals omega

/-- The actual finite matrix of reference augmentation is its true block sum,
with the concrete finite even/odd index permutation. -/
theorem standardRelativeProjectionAugmentation_finiteMatrix (P : StdEnd)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ) :
    standardCountableRelativeFiniteMatrix (standardRelativeProjectionAugmentation P)
      (standardRelativeProjectionAugmentation_compact P hc) (2 * n) =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (standardRelativePairedEvenOddFinEquiv n)
        (matrixBlockSum (standardCountableRelativeFiniteMatrix P hc n)
          (pairedStandardFiniteReferenceMatrix n)) := by
  have hScalarSmall (i j : PairedStandardFiniteIndex n) :
      (standardCountableRelativeFiniteMatrix P hc n i j).fst =
        (pairedStandardFiniteReferenceMatrix (B := B) n i j).fst :=
    congrArg (fun M : CStarMatrix (PairedStandardFiniteIndex n)
      (PairedStandardFiniteIndex n) ℂ => M i j) (standardCountableRelativeFiniteMatrix_scalar P hc n)
  apply CStarMatrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (standardRelativePairedEvenOddFinEquiv n).surjective i
  obtain ⟨j, rfl⟩ := (standardRelativePairedEvenOddFinEquiv n).surjective j
  have hReindex (M : CStarMatrix (PairedStandardFiniteIndex n ⊕ PairedStandardFiniteIndex n)
      (PairedStandardFiniteIndex n ⊕ PairedStandardFiniteIndex n) (Unitization ℂ B)) :
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (standardRelativePairedEvenOddFinEquiv n) M
        (standardRelativePairedEvenOddFinEquiv n i) (standardRelativePairedEvenOddFinEquiv n j) = M i j := by
    change M ((standardRelativePairedEvenOddFinEquiv n).symm (standardRelativePairedEvenOddFinEquiv n i))
      ((standardRelativePairedEvenOddFinEquiv n).symm (standardRelativePairedEvenOddFinEquiv n j)) = M i j
    simp only [Equiv.symm_apply_apply]
  apply standardRelativeUnitization_eq_of_scalar_and_left_action
  · have hs := congrArg (fun M : CStarMatrix (PairedStandardFiniteIndex (2 * n))
      (PairedStandardFiniteIndex (2 * n)) ℂ =>
      M (standardRelativePairedEvenOddFinEquiv n i) (standardRelativePairedEvenOddFinEquiv n j))
        (standardCountableRelativeFiniteMatrix_scalar (standardRelativeProjectionAugmentation P)
          (standardRelativeProjectionAugmentation_compact P hc) (2 * n))
    simp only [unitizationScalarMatrix_apply] at hs
    rw [pairedStandardFiniteReferenceMatrix_evenOdd, hReindex] at hs
    rw [hReindex]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa only [matrixBlockSum, CStarMatrix.ofMatrix_apply, CStarMatrix.ofMatrix_symm_apply,
          Matrix.fromBlocks_apply₁₁, hScalarSmall] using hs
      | inr j =>
        simpa only [matrixBlockSum, CStarMatrix.ofMatrix_apply,
          Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using hs
    | inr i =>
      cases j with
      | inl j =>
        simpa only [matrixBlockSum, CStarMatrix.ofMatrix_apply,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using hs
      | inr j =>
        simpa only [matrixBlockSum, CStarMatrix.ofMatrix_apply, CStarMatrix.ofMatrix_symm_apply,
          Matrix.fromBlocks_apply₂₂] using hs
  · ext b
    rw [standardCountableRelativeFiniteMatrix_entry_action]
    rw [hReindex]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [standardRelativeProjectionAugmentation, HilbertModuleEquiv.transport_apply,
          standardRelativePairSelfAbsorption_symm_coordinate_even, sumMap_apply,
          sumMk_fst, sumMk_snd, map_zero, standardRelativePairSelfAbsorption_evaluation_coordinate_even,
          matrixBlockSum, CStarMatrix.ofMatrix_apply, CStarMatrix.ofMatrix_symm_apply, Matrix.fromBlocks_apply₁₁]
        exact (standardCountableRelativeFiniteMatrix_entry_action P hc n i j b).symm
      | inr j =>
        simp only [standardRelativeProjectionAugmentation, HilbertModuleEquiv.transport_apply,
          standardRelativePairSelfAbsorption_symm_coordinate_odd, sumMap_apply,
          sumMk_fst, sumMk_snd, map_zero, standardRelativePairSelfAbsorption_evaluation_coordinate_even,
          matrixBlockSum, CStarMatrix.ofMatrix_apply, Matrix.fromBlocks_apply₁₂,
          Matrix.zero_apply, map_zero, AdjointableMap.coe_zero_apply]
    | inr i =>
      cases j with
      | inl j =>
        simp only [standardRelativeProjectionAugmentation, HilbertModuleEquiv.transport_apply,
          standardRelativePairSelfAbsorption_symm_coordinate_even, sumMap_apply,
          sumMk_fst, sumMk_snd, map_zero, standardRelativePairSelfAbsorption_evaluation_coordinate_odd,
          matrixBlockSum, CStarMatrix.ofMatrix_apply, Matrix.fromBlocks_apply₂₁,
          Matrix.zero_apply, map_zero, AdjointableMap.coe_zero_apply]
      | inr j =>
        simp only [standardRelativeProjectionAugmentation, HilbertModuleEquiv.transport_apply,
          standardRelativePairSelfAbsorption_symm_coordinate_odd, sumMap_apply,
          sumMk_fst, sumMk_snd, map_zero, standardRelativePairSelfAbsorption_evaluation_coordinate_odd,
          matrixBlockSum, CStarMatrix.ofMatrix_apply, CStarMatrix.ofMatrix_symm_apply, Matrix.fromBlocks_apply₂₂]
        have h := congrArg (fun T => T (finiteStandardInclusion j b) i)
          (pairedStandardFiniteCompression_reference (B := B) n)
        simp only [pairedStandardFiniteCompression, AdjointableMap.comp_apply,
          pairedStandardFiniteInclusion_single, pairedStandardFiniteInclusion_adjoint_apply] at h
        simpa only [unitizedModuleMatrixRepresentation_apply, finiteStandardInclusion_apply,
          finiteStandardSingle_apply, Pi.single_apply, apply_ite, map_zero,
          AdjointableMap.coe_zero_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

/-- On an actually supported projection, augmentation adds an equal genuine
reference block and preserves the scalar-kernel index. -/
theorem standardRelativeProjectionAugmentation_index_supported (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hCorner : P - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (P - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    standardCountableRelativeProjectionIndex (standardRelativeProjectionAugmentation P)
      (standardRelativeProjectionAugmentation_isStarProjection P hP)
      (standardRelativeProjectionAugmentation_compact P hc) =
        standardCountableRelativeProjectionIndex P hP hc := by
  rw [standardCountableRelativeProjectionIndex_supported _ _ _ (2 * n)
      (standardRelativeProjectionAugmentation_corner P n hCorner),
    standardCountableRelativeProjectionIndex_supported P hP hc n hCorner]
  apply operatorK0Inclusion_injective
  let p : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) :=
    ⟨standardCountableRelativeFiniteMatrix P hc n,
      standardCountableRelativeFiniteMatrix_isStarProjection P hP hc n
        (standardCountableRelativeCorner_commutes_cutoff n P hCorner)⟩
  let q : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) :=
    ⟨pairedStandardFiniteReferenceMatrix n, pairedStandardFiniteReferenceMatrix_isStarProjection n⟩
  have hp : (⟨standardCountableRelativeFiniteMatrix (standardRelativeProjectionAugmentation P)
      (standardRelativeProjectionAugmentation_compact P hc) (2 * n),
      standardCountableRelativeFiniteMatrix_isStarProjection _
        (standardRelativeProjectionAugmentation_isStarProjection P hP)
        (standardRelativeProjectionAugmentation_compact P hc) (2 * n)
        (standardCountableRelativeCorner_commutes_cutoff (2 * n) _
          (standardRelativeProjectionAugmentation_corner P n hCorner))⟩ :
      MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex (2 * n))) =
      Projection.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B)
        (standardRelativePairedEvenOddFinEquiv n)).toStarAlgHom (projectionBlockSum p q) := by
    apply Subtype.ext
    exact standardRelativeProjectionAugmentation_finiteMatrix P hc n
  have hq : (⟨pairedStandardFiniteReferenceMatrix (2 * n),
      pairedStandardFiniteReferenceMatrix_isStarProjection (B := B) (2 * n)⟩ :
      MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex (2 * n))) =
      Projection.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B)
        (standardRelativePairedEvenOddFinEquiv n)).toStarAlgHom (projectionBlockSum q q) := by
    apply Subtype.ext
    exact pairedStandardFiniteReferenceMatrix_evenOdd n
  change k0Projection (FiniteProjection.ofProjection _) -
    k0Projection (FiniteProjection.ofProjection _) =
      k0Projection (FiniteProjection.ofProjection p) - k0Projection (FiniteProjection.ofProjection q)
  rw [hp, hq, unitizationFiniteProjection_k0_reindex, unitizationFiniteProjection_k0_reindex]
  exact unitizationRelativeProjectionK0_block_reference_padding p q q

/-- Actual augmentation preserves the index for every genuine compact-relative
projection, by the constructed rounded projection path. -/
theorem standardRelativeProjectionAugmentation_index (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    standardCountableRelativeProjectionIndex (standardRelativeProjectionAugmentation P)
      (standardRelativeProjectionAugmentation_isStarProjection P hP)
      (standardRelativeProjectionAugmentation_compact P hc) =
        standardCountableRelativeProjectionIndex P hP hc := by
  obtain ⟨n, γ, hγ⟩ := exists_standardCountableRelativeProjectionPath P hP hc
  let R := spectralGapRoundedProjection (standardCountableReferenceCompression P n)
  have hR : IsStarProjection R := by
    have h := (hγ 1).1
    rwa [γ.target] at h
  have hRc : IsModuleCompact (R - standardCountablePairedReferenceProjection) := by
    have h := (hγ 1).2
    rwa [γ.target] at h
  let Γ : C(unitInterval, StdEnd) := ⟨γ, γ.continuous⟩
  let Γa : C(unitInterval, StdEnd) :=
    ⟨fun t => standardRelativeProjectionAugmentation (γ t),
      continuous_standardRelativeProjectionAugmentation.comp γ.continuous⟩
  have hOriginal := standardCountableRelativeProjectionIndex_path Γ
    (fun t => (hγ t).1) (fun t => (hγ t).2)
  have hAugmented := standardCountableRelativeProjectionIndex_path Γa
    (fun t => standardRelativeProjectionAugmentation_isStarProjection (γ t) (hγ t).1)
    (fun t => standardRelativeProjectionAugmentation_compact (γ t) (hγ t).2)
  have hEndpoint := standardRelativeProjectionAugmentation_index_supported R hR hRc n
    (spectralGapRoundedReferenceCompression_sub_eq_cutoff P hP.isSelfAdjoint n)
  simp only [Γ, Γa, ContinuousMap.coe_mk, γ.source, γ.target] at hOriginal hAugmented
  exact hAugmented.trans (hEndpoint.trans hOriginal.symm)

end BC4lean.KKTheory
