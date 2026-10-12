import BC4lean.StandardCountableRelativeProjectionAugmentation
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! # Actual reference-preserving unitary invariance of the K₀ index

The genuine doubled unitary rotation, transported by the coefficient interleave,
joins the reference augmentations of a projection and its unitary conjugate.
Actual compact difference is preserved throughout by the proved reference
commutation factorization. Norm-path invariance and genuine reference
augmentation remove the doubled copy. The conjugating unitary need not be
compact or connected to the identity.
-/

noncomputable section
open scoped CStarAlgebra
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open unitInterval

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
local notation "Std" => StandardCountableHilbertModule B
local notation "StdPair" => HilbertModuleSum B Std Std
local notation "StdEnd" => AdjointableMap B StdPair StdPair

-- Use the original coefficient-inner-product norm on the four-copy module sum.
local instance standardRelativeConjugationNestedNorm :
    NormedAddCommGroup (HilbertModuleSum B StdPair StdPair) :=
  WithCStarModule.instNormedAddCommGroupProd (A := Bᵐᵒᵖ) (E := StdPair) (F := StdPair)

def standardRelativeProjectionConjugate (W : unitary StdEnd) (P : StdEnd) : StdEnd :=
  (W : StdEnd) * P * star (W : StdEnd)

theorem standardRelativeProjectionConjugate_isStarProjection (W : unitary StdEnd)
    (P : StdEnd) (hP : IsStarProjection P) :
    IsStarProjection (standardRelativeProjectionConjugate W P) := by
  simpa only [Unitary.conjStarAlgAut_apply, standardRelativeProjectionConjugate] using
    hP.map (Unitary.conjStarAlgAut ℂ StdEnd W)

theorem standardRelativeProjectionConjugate_compact (W : unitary StdEnd) (P : StdEnd)
    (hW : Commute (W : StdEnd) standardCountablePairedReferenceProjection)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    IsModuleCompact (standardRelativeProjectionConjugate W P - standardCountablePairedReferenceProjection) := by
  have hReference : (W : StdEnd) * standardCountablePairedReferenceProjection * star (W : StdEnd) =
      standardCountablePairedReferenceProjection := by
    rw [hW.eq, mul_assoc, W.property.2, mul_one]
  have hEq : standardRelativeProjectionConjugate W P - standardCountablePairedReferenceProjection =
      (W : StdEnd) * (P - standardCountablePairedReferenceProjection) * star (W : StdEnd) := by
    rw [standardRelativeProjectionConjugate, mul_sub, sub_mul, hReference]
  rw [hEq]
  exact (hc.comp_left (W : StdEnd)).comp_right (star (W : StdEnd))

def standardRelativeDoubledConjugationProjection (W : unitary StdEnd) (P : StdEnd) (t : I) : StdEnd :=
  (standardRelativePairSelfAbsorption (B := B)).transport
    (doubledUnitaryRelativeProjectionPath W P standardCountablePairedReferenceProjection t)

theorem continuous_standardRelativeDoubledConjugationProjection (W : unitary StdEnd) (P : StdEnd) :
    Continuous (standardRelativeDoubledConjugationProjection W P) := by
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
  exact hTransport.comp
    ((continuous_doubledUnitaryRelativeProjectionPath W P
      (standardCountablePairedReferenceProjection (B := B))).comp continuous_subtype_val)

theorem standardRelativeDoubledConjugationProjection_isStarProjection (W : unitary StdEnd)
    (P : StdEnd) (hP : IsStarProjection P) (t : I) :
    IsStarProjection (standardRelativeDoubledConjugationProjection W P t) :=
  (doubledUnitaryRelativeProjectionPath_isStarProjection W hP
    standardCountablePairedReferenceProjection_isStarProjection t).map
      (standardRelativePairSelfAbsorption (B := B)).transportStarAlgEquiv.toStarAlgHom

theorem standardRelativeDoubledConjugationProjection_compact (W : unitary StdEnd) (P : StdEnd)
    (hW : Commute (W : StdEnd) standardCountablePairedReferenceProjection)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (t : I) :
    IsModuleCompact (standardRelativeDoubledConjugationProjection W P t - standardCountablePairedReferenceProjection) := by
  have h : IsModuleCompact ((standardRelativePairSelfAbsorption (B := B)).transport
      (doubledUnitaryRelativeProjectionPath W P (standardCountablePairedReferenceProjection (B := B))
        (t : ℝ) - sumMap (B := B) standardCountablePairedReferenceProjection
          standardCountablePairedReferenceProjection)) :=
    (standardRelativePairSelfAbsorption (B := B)).transportMap_isModuleCompact
      (standardRelativePairSelfAbsorption (B := B))
      (doubledUnitaryRelativeProjectionPath_difference_isModuleCompact W hW hc (t : ℝ))
  simpa only [standardRelativeDoubledConjugationProjection, HilbertModuleEquiv.transport_sub,
    standardRelativePairSelfAbsorption_reference] using h

@[simp] theorem standardRelativeDoubledConjugationProjection_zero (W : unitary StdEnd) (P : StdEnd)
    (hW : Commute (W : StdEnd) standardCountablePairedReferenceProjection) :
    standardRelativeDoubledConjugationProjection W P 0 =
      standardRelativeProjectionAugmentation (standardRelativeProjectionConjugate W P) := by
  unfold standardRelativeDoubledConjugationProjection
  rw [Set.Icc.coe_zero, doubledUnitaryRelativeProjectionPath_zero W _ _ hW]
  rfl

@[simp] theorem standardRelativeDoubledConjugationProjection_one (W : unitary StdEnd) (P : StdEnd) :
    standardRelativeDoubledConjugationProjection W P 1 = standardRelativeProjectionAugmentation P := by
  unfold standardRelativeDoubledConjugationProjection
  rw [Set.Icc.coe_one, doubledUnitaryRelativeProjectionPath_one]
  rfl

/-- Every actual reference-preserving unitary preserves the actual scalar-kernel index. -/
theorem standardCountableRelativeProjectionIndex_conjugation (W : unitary StdEnd) (P : StdEnd)
    (hP : IsStarProjection P)
    (hW : Commute (W : StdEnd) standardCountablePairedReferenceProjection)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    standardCountableRelativeProjectionIndex (standardRelativeProjectionConjugate W P)
      (standardRelativeProjectionConjugate_isStarProjection W P hP)
      (standardRelativeProjectionConjugate_compact W P hW hc) =
        standardCountableRelativeProjectionIndex P hP hc := by
  let γ : C(I, StdEnd) := ⟨standardRelativeDoubledConjugationProjection W P,
    continuous_standardRelativeDoubledConjugationProjection W P⟩
  have hPath := standardCountableRelativeProjectionIndex_path γ
    (standardRelativeDoubledConjugationProjection_isStarProjection W P hP)
    (standardRelativeDoubledConjugationProjection_compact W P hW hc)
  simp only [γ, ContinuousMap.coe_mk, standardRelativeDoubledConjugationProjection_zero W P hW,
    standardRelativeDoubledConjugationProjection_one] at hPath
  exact (standardRelativeProjectionAugmentation_index (standardRelativeProjectionConjugate W P)
    (standardRelativeProjectionConjugate_isStarProjection W P hP)
    (standardRelativeProjectionConjugate_compact W P hW hc)).symm.trans
      (hPath.trans (standardRelativeProjectionAugmentation_index P hP hc))

end BC4lean.KKTheory
