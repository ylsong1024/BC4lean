import BC4lean.OddFredholmStandardFibreIndex
import BC4lean.OddKTheoryContinuousUnitaryEvaluation
import BC4lean.OddFredholmCutoffIndependence

/-! # Actual common-cutoff index equality for completed interval standard modules

The compact defect over C(I,B) itself supplies an actual finite cutoff size.
Contractive fibre evaluation preserves that radius-one polar criterion at
every parameter. The exact finite coefficient naturality and actual finite
unitary evaluation path prove endpoint equality in OperatorK1(B).
The proved cutoff independence then gives equality of the actual chosen
endpoint indices. Arbitrary module stabilization and its choice independence
remain separate obligations for full odd-homotopy descent.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- One actual cutoff works for every fibre, because it is chosen from the
compact completed interval-module operator before any evaluation. -/
def oddFredholmStandardIntervalFiniteIndex
    (U : unitary (OddFredholmStandardOperator C(I, B)))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator C(I, B)) - 1)) (t : I) :
    OperatorKTheory.OperatorK1 B :=
  oddFredholmScalarIdentityUnitaryIndex
    (oddFredholmStandardFiniteIndexUnitary (standardCountableFibreUnitary t U)
      (standardCountableFibreUnitary_sub_one_isModuleCompact t U hU)
      (oddFredholmStandardIndexSize U hU)
      (oddFredholmStandardFibre_cutoff_near t U _ (oddFredholmStandardIndexSize_near U hU)))
    (oddFredholmStandardFiniteIndexUnitary_scalar _ _ _ _)

theorem oddFredholmStandardIntervalFiniteIndex_evaluation
    (U : unitary (OddFredholmStandardOperator C(I, B)))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator C(I, B)) - 1)) (t : I) :
    oddFredholmStandardIntervalFiniteIndex U hU t =
      oddFredholmScalarIdentityUnitaryIndex
        (oddKTheoryUnitizationUnitaryEvaluation t
          (oddFredholmStandardFiniteIndexUnitary U hU (oddFredholmStandardIndexSize U hU)
            (oddFredholmStandardIndexSize_near U hU)))
        (oddKTheoryUnitizationUnitaryEvaluation_scalar t _
          (oddFredholmStandardFiniteIndexUnitary_scalar U hU _ _)) := by
  have h : oddKTheoryUnitizationUnitaryEvaluation t
      (oddFredholmStandardFiniteIndexUnitary U hU (oddFredholmStandardIndexSize U hU)
        (oddFredholmStandardIndexSize_near U hU)) =
      oddFredholmStandardFiniteIndexUnitary (standardCountableFibreUnitary t U)
        (standardCountableFibreUnitary_sub_one_isModuleCompact t U hU)
        (oddFredholmStandardIndexSize U hU)
        (oddFredholmStandardFibre_cutoff_near t U _ (oddFredholmStandardIndexSize_near U hU)) := by
    apply Subtype.ext
    exact oddFredholmStandardFiniteIndexUnitary_evaluation t U hU _ _
  apply Subtype.ext
  change OperatorKTheory.K1.of (OperatorKTheory.FiniteUnitary.ofUnitary _) =
    OperatorKTheory.K1.of (OperatorKTheory.FiniteUnitary.ofUnitary _)
  rw [h]

/-- Genuine compact interval-module unitaries have equal actual endpoint
indices at the cutoff constructed from the entire interval operator. -/
theorem oddFredholmStandardIntervalFiniteIndex_endpoints
    (U : unitary (OddFredholmStandardOperator C(I, B)))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator C(I, B)) - 1)) :
    oddFredholmStandardIntervalFiniteIndex U hU 0 =
      oddFredholmStandardIntervalFiniteIndex U hU 1 := by
  rw [oddFredholmStandardIntervalFiniteIndex_evaluation,
    oddFredholmStandardIntervalFiniteIndex_evaluation]
  exact oddKTheoryUnitizationUnitaryEvaluation_operatorK1_endpoints
    (oddFredholmStandardFiniteIndexUnitary U hU (oddFredholmStandardIndexSize U hU)
      (oddFredholmStandardIndexSize_near U hU))
    (oddFredholmStandardFiniteIndexUnitary_scalar U hU (oddFredholmStandardIndexSize U hU)
      (oddFredholmStandardIndexSize_near U hU))

set_option maxHeartbeats 600000 in
/-- Actual selfadjoint Fredholm interval operators have equal exponential
finite indices at the common cutoff supplied by their compact square defect. -/
theorem oddFredholmStandardIntervalExponentialIndex_endpoints
    (F : selfAdjoint (OddFredholmStandardOperator C(I, B)))
    (hF : IsModuleCompact ((F : OddFredholmStandardOperator C(I, B)) ^ 2 - 1)) :
    oddFredholmStandardIntervalFiniteIndex (oddFredholmExponential (A := OddFredholmStandardOperator C(I, B)) F)
        (oddFredholmExponential_sub_one_isModuleCompact (B := C(I, B))
          (E := StandardCountableHilbertModule C(I, B)) F hF) 0 =
      oddFredholmStandardIntervalFiniteIndex (oddFredholmExponential (A := OddFredholmStandardOperator C(I, B)) F)
        (oddFredholmExponential_sub_one_isModuleCompact (B := C(I, B))
          (E := StandardCountableHilbertModule C(I, B)) F hF) 1 :=
  oddFredholmStandardIntervalFiniteIndex_endpoints
    (oddFredholmExponential (A := OddFredholmStandardOperator C(I, B)) F)
    (oddFredholmExponential_sub_one_isModuleCompact (B := C(I, B))
      (E := StandardCountableHilbertModule C(I, B)) F hF)

theorem oddFredholmStandardIntervalFiniteIndex_eq_index
    (U : unitary (OddFredholmStandardOperator C(I, B)))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator C(I, B)) - 1)) (t : I) :
    oddFredholmStandardIntervalFiniteIndex U hU t =
      oddFredholmStandardUnitaryIndex (standardCountableFibreUnitary t U)
        (standardCountableFibreUnitary_sub_one_isModuleCompact t U hU) :=
  (oddFredholmStandardUnitaryIndex_eq_cutoff _ _ (oddFredholmStandardIndexSize U hU)
    (oddFredholmStandardFibre_cutoff_near t U _ (oddFredholmStandardIndexSize_near U hU))).symm

/-- Actual chosen finite indices of the two genuine completed standard
fibres agree; cutoff independence removes the auxiliary common size. -/
theorem oddFredholmStandardIntervalUnitaryIndex_endpoints
    (U : unitary (OddFredholmStandardOperator C(I, B)))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator C(I, B)) - 1)) :
    oddFredholmStandardUnitaryIndex (standardCountableFibreUnitary 0 U)
        (standardCountableFibreUnitary_sub_one_isModuleCompact 0 U hU) =
      oddFredholmStandardUnitaryIndex (standardCountableFibreUnitary 1 U)
        (standardCountableFibreUnitary_sub_one_isModuleCompact 1 U hU) := by
  rw [← oddFredholmStandardIntervalFiniteIndex_eq_index,
    ← oddFredholmStandardIntervalFiniteIndex_eq_index]
  exact oddFredholmStandardIntervalFiniteIndex_endpoints U hU

theorem oddFredholmStandardFibre_square_compact (t : I)
    (F : selfAdjoint (OddFredholmStandardOperator C(I, B)))
    (hF : IsModuleCompact ((F : OddFredholmStandardOperator C(I, B)) ^ 2 - 1)) :
    IsModuleCompact ((oddFredholmStandardFibreSelfAdjoint t F : OddFredholmStandardOperator B) ^ 2 - 1) := by
  have h := standardCountableFibreOperatorHom_isModuleCompact t hF
  simpa only [map_sub, map_pow, map_one, oddFredholmStandardFibreSelfAdjoint] using h

/-- Exponential index invariance for genuine selfadjoint Fredholm operators
over the completed interval standard module, with actual OperatorK1 values. -/
theorem oddFredholmStandardIntervalIndex_endpoints
    (F : selfAdjoint (OddFredholmStandardOperator C(I, B)))
    (hF : IsModuleCompact ((F : OddFredholmStandardOperator C(I, B)) ^ 2 - 1)) :
    oddFredholmStandardIndex (oddFredholmStandardFibreSelfAdjoint 0 F)
        (oddFredholmStandardFibre_square_compact 0 F hF) =
      oddFredholmStandardIndex (oddFredholmStandardFibreSelfAdjoint 1 F)
        (oddFredholmStandardFibre_square_compact 1 F hF) := by
  have h := oddFredholmStandardIntervalUnitaryIndex_endpoints (B := B)
    (oddFredholmExponential (A := OddFredholmStandardOperator C(I, B)) F)
    (oddFredholmExponential_sub_one_isModuleCompact (B := C(I, B))
      (E := StandardCountableHilbertModule C(I, B)) F hF)
  let P : unitary (OddFredholmStandardOperator B) →
      unitary (OddFredholmStandardOperator B) → Prop := fun U V =>
    ∀ hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1),
      ∀ hV : IsModuleCompact ((V : OddFredholmStandardOperator B) - 1),
        oddFredholmStandardUnitaryIndex U hU = oddFredholmStandardUnitaryIndex V hV
  have hP : P
      (standardCountableFibreUnitary (B := B) (X := I) 0
        (oddFredholmExponential (A := OddFredholmStandardOperator C(I, B)) F))
      (standardCountableFibreUnitary (B := B) (X := I) 1
        (oddFredholmExponential (A := OddFredholmStandardOperator C(I, B)) F)) := by
    intro hU hV
    exact h
  have hEndpoints : P
      (oddFredholmExponential (A := OddFredholmStandardOperator B)
        (oddFredholmStandardFibreSelfAdjoint 0 F))
      (oddFredholmExponential (A := OddFredholmStandardOperator B)
        (oddFredholmStandardFibreSelfAdjoint 1 F)) :=
    Eq.mp (congrArg₂ P
      (oddFredholmStandardFibre_exponential (B := B) (X := I) 0 F)
      (oddFredholmStandardFibre_exponential (B := B) (X := I) 1 F)) hP
  unfold oddFredholmStandardIndex
  exact hEndpoints _ _

end BC4lean.KKTheory
