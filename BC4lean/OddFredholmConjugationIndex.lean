import BC4lean.OddFredholmIdentityAugmentation

/-! # Genuine unitary conjugation invariance of the odd index

The actual doubled rotation joins W ⊕ W* to the identity. Conjugating
U ⊕ 1 along this rotation produces a norm path of genuine compact unitaries.
The proved coordinate identity augmentation identifies its endpoint indices.
No connectivity assertion for the full infinite unitary group is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Actual unitary conjugation in End(H_B). -/
def oddFredholmConjugateUnitary (W U : unitary (OddFredholmStandardOperator B)) :
    unitary (OddFredholmStandardOperator B) := W * U * star W

theorem oddFredholmConjugateUnitary_sub_one_isModuleCompact
    (W U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    IsModuleCompact ((oddFredholmConjugateUnitary W U : OddFredholmStandardOperator B) - 1) := by
  have he : (oddFredholmConjugateUnitary W U : OddFredholmStandardOperator B) - 1 =
      (W : OddFredholmStandardOperator B) * ((U : OddFredholmStandardOperator B) - 1) * star W := by
    simp only [oddFredholmConjugateUnitary, Submonoid.coe_mul, Unitary.coe_star,
      mul_sub, sub_mul, mul_one, W.property.2]
  rw [he]
  have hleft : IsModuleCompact
      ((W : OddFredholmStandardOperator B) * ((U : OddFredholmStandardOperator B) - 1)) :=
    mul_mem_moduleCompact_left (B := B) (E := StandardCountableHilbertModule B)
      (W : OddFredholmStandardOperator B) hU
  exact mul_mem_moduleCompact_right (B := B) (E := StandardCountableHilbertModule B)
    hleft (star (W : OddFredholmStandardOperator B))

def oddFredholmDoubledConjugationUnitary
    (W U : unitary (OddFredholmStandardOperator B)) (t : I) :
    unitary (AdjointableMap B (HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)) (HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B))) :=
  ⟨doubledUnitaryRelativeProjectionPath (B := B) (E := StandardCountableHilbertModule B)
      W (U : OddFredholmStandardOperator B) (1 : OddFredholmStandardOperator B) (t : ℝ), by
    have hrotation := doubledAdjointableUnitaryPath_mem_unitary
      (B := B) (E := StandardCountableHilbertModule B) W (t : ℝ)
    have hsum := sumMap_mem_unitary (B := B) (E := StandardCountableHilbertModule B)
      U (1 : unitary (OddFredholmStandardOperator B))
    change doubledAdjointableUnitaryPath W (t : ℝ) *
      sumMap (B := B) (U : OddFredholmStandardOperator B) (1 : OddFredholmStandardOperator B) *
      star (doubledAdjointableUnitaryPath W (t : ℝ)) ∈
      unitary (AdjointableMap B
        (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
        (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    exact (unitary _).mul_mem ((unitary _).mul_mem hrotation hsum)
      (Unitary.star_mem hrotation)⟩

theorem continuous_oddFredholmDoubledConjugationUnitary
    (W U : unitary (OddFredholmStandardOperator B)) :
    Continuous (oddFredholmDoubledConjugationUnitary W U) :=
  ((continuous_doubledUnitaryRelativeProjectionPath (B := B)
    (E := StandardCountableHilbertModule B) W (U : OddFredholmStandardOperator B)
    (1 : OddFredholmStandardOperator B)).comp continuous_subtype_val).subtype_mk _

def oddFredholmStandardDoubledConjugationUnitary
    (W U : unitary (OddFredholmStandardOperator B)) (t : I) :
    unitary (OddFredholmStandardOperator B) :=
  ⟨(standardCountableSelfAbsorption (B := B)).transport (oddFredholmDoubledConjugationUnitary W U t :
      AdjointableMap B (HilbertModuleSum B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) (HilbertModuleSum B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B))),
    Unitary.map_mem (standardCountableSelfAbsorption (B := B)).transportStarAlgEquiv.toStarAlgHom
      (oddFredholmDoubledConjugationUnitary W U t).property⟩

theorem continuous_oddFredholmStandardDoubledConjugationUnitary
    (W U : unitary (OddFredholmStandardOperator B)) :
    Continuous (oddFredholmStandardDoubledConjugationUnitary W U) :=
  by
    have hpath : Continuous (fun t : I =>
        (oddFredholmDoubledConjugationUnitary W U t :
          AdjointableMap B
            (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
            (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))) :=
      continuous_subtype_val.comp (continuous_oddFredholmDoubledConjugationUnitary W U)
    have htransport : Continuous (fun T : AdjointableMap B
        (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
        (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) =>
        (standardCountableSelfAbsorption (B := B)).transport T) :=
      (StarAlgEquiv.isometry
        (standardCountableSelfAbsorption (B := B)).transportStarAlgEquiv).continuous
    apply Continuous.subtype_mk
    exact htransport.comp hpath

theorem oddFredholmStandardDoubledConjugationUnitary_compact
    (W U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (t : I) :
    IsModuleCompact ((oddFredholmStandardDoubledConjugationUnitary W U t :
      OddFredholmStandardOperator B) - 1) := by
  have h := doubledUnitaryRelativeProjectionPath_difference_isModuleCompact
    (B := B) (E := StandardCountableHilbertModule B)
    (P := (U : OddFredholmStandardOperator B)) (Q := (1 : OddFredholmStandardOperator B))
    W (Commute.one_right _) hU (t : ℝ)
  have hcompact : IsModuleCompact
      ((oddFredholmDoubledConjugationUnitary W U t :
      AdjointableMap B (HilbertModuleSum B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) (HilbertModuleSum B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B))) - 1) := by
    simpa only [oddFredholmDoubledConjugationUnitary, sumMap_one] using h
  have ht := (standardCountableSelfAbsorption (B := B)).transportMap_isModuleCompact
    (standardCountableSelfAbsorption (B := B)) hcompact
  change IsModuleCompact ((standardCountableSelfAbsorption (B := B)).transport
    ((oddFredholmDoubledConjugationUnitary W U t :
      AdjointableMap B (HilbertModuleSum B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) (HilbertModuleSum B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B))) - 1)) at ht
  simpa only [oddFredholmStandardDoubledConjugationUnitary,
    HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one] using ht

@[simp] theorem oddFredholmStandardDoubledConjugationUnitary_zero
    (W U : unitary (OddFredholmStandardOperator B)) :
    oddFredholmStandardDoubledConjugationUnitary W U 0 =
      oddFredholmStandardIdentityAugmentation (oddFredholmConjugateUnitary W U) := by
  apply Subtype.ext
  change (standardCountableSelfAbsorption (B := B)).transport
      (doubledUnitaryRelativeProjectionPath (B := B) (E := StandardCountableHilbertModule B)
        W (U : OddFredholmStandardOperator B) (1 : OddFredholmStandardOperator B) (0 : ℝ)) =
    (standardCountableSelfAbsorption (B := B)).transport
      (sumMap (B := B) ((W : OddFredholmStandardOperator B) *
        (U : OddFredholmStandardOperator B) * star (W : OddFredholmStandardOperator B))
        (1 : OddFredholmStandardOperator B))
  rw [doubledUnitaryRelativeProjectionPath_zero W _ _ (Commute.one_right _)]

@[simp] theorem oddFredholmStandardDoubledConjugationUnitary_one
    (W U : unitary (OddFredholmStandardOperator B)) :
    oddFredholmStandardDoubledConjugationUnitary W U 1 =
      oddFredholmStandardIdentityAugmentation U := by
  apply Subtype.ext
  change (standardCountableSelfAbsorption (B := B)).transport
      (doubledUnitaryRelativeProjectionPath (B := B) (E := StandardCountableHilbertModule B)
        W (U : OddFredholmStandardOperator B) (1 : OddFredholmStandardOperator B) (1 : ℝ)) =
    (standardCountableSelfAbsorption (B := B)).transport
      (sumMap (B := B) (U : OddFredholmStandardOperator B) (1 : OddFredholmStandardOperator B))
  rw [doubledUnitaryRelativeProjectionPath_one]

def oddFredholmStandardDoubledConjugationPath
    (W U : unitary (OddFredholmStandardOperator B)) :
    Path (oddFredholmStandardIdentityAugmentation (oddFredholmConjugateUnitary W U))
      (oddFredholmStandardIdentityAugmentation U) where
  toFun := oddFredholmStandardDoubledConjugationUnitary W U
  continuous_toFun := continuous_oddFredholmStandardDoubledConjugationUnitary W U
  source' := oddFredholmStandardDoubledConjugationUnitary_zero W U
  target' := oddFredholmStandardDoubledConjugationUnitary_one W U

/-- The actual index is invariant under every actual adjointable unitary
conjugation, with no compactness hypothesis on the conjugating unitary. -/
theorem oddFredholmStandardUnitaryIndex_conjugation
    (W U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    oddFredholmStandardUnitaryIndex (oddFredholmConjugateUnitary W U)
      (oddFredholmConjugateUnitary_sub_one_isModuleCompact W U hU) =
      oddFredholmStandardUnitaryIndex U hU := by
  have h := oddFredholmStandardUnitaryIndex_path (oddFredholmStandardDoubledConjugationPath W U)
    (oddFredholmStandardDoubledConjugationUnitary_compact W U hU)
  exact (oddFredholmStandardUnitaryIndex_identityAugmentation
    (oddFredholmConjugateUnitary W U)
    (oddFredholmConjugateUnitary_sub_one_isModuleCompact W U hU)).symm.trans
      (h.trans (oddFredholmStandardUnitaryIndex_identityAugmentation U hU))

/-- A standard-module unitary isomorphism gives an actual unitary operator. -/
def oddFredholmStandardEquivUnitary
    (u : HilbertModuleEquiv B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
    unitary (OddFredholmStandardOperator B) :=
  ⟨u.toAdjointable, by
    apply Unitary.mem_iff.mpr
    constructor <;> ext x <;>
      simp only [AdjointableMap.mul_apply, AdjointableMap.star_eq_adjoint,
        HilbertModuleEquiv.toAdjointable_adjoint, HilbertModuleEquiv.toAdjointable_apply,
        HilbertModuleEquiv.symm_apply_apply, HilbertModuleEquiv.apply_symm_apply,
        AdjointableMap.one_apply]⟩

theorem oddFredholmStandardEquiv_transport_unitary
    (u : HilbertModuleEquiv B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
    (U : unitary (OddFredholmStandardOperator B)) :
    u.transport (U : OddFredholmStandardOperator B) =
      (oddFredholmConjugateUnitary (oddFredholmStandardEquivUnitary u) U :
        OddFredholmStandardOperator B) := by
  ext x
  simp only [HilbertModuleEquiv.transport_apply, oddFredholmConjugateUnitary,
    Submonoid.coe_mul, Unitary.coe_star, oddFredholmStandardEquivUnitary,
    AdjointableMap.mul_apply, AdjointableMap.star_eq_adjoint,
    HilbertModuleEquiv.toAdjointable_adjoint, HilbertModuleEquiv.toAdjointable_apply]

end BC4lean.KKTheory
