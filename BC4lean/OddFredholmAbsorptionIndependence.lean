import BC4lean.OddFredholmConjugationIndex
import BC4lean.OddFredholmStandardStabilization

/-! # Independence of the actual odd standard-module absorption

Two actual absorption unitaries differ by an actual adjointable unitary of H_B.
The proved doubled-rotation index invariance identifies the corresponding
finite exponential indices. All isomorphisms act on the genuine modules.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- Transport the actual selfadjoint operator through a genuine module unitary. -/
def oddFredholmTransportSelfAdjoint
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (F : selfAdjoint (AdjointableMap B E E)) : selfAdjoint (OddFredholmStandardOperator B) :=
  ⟨u.transport (F : AdjointableMap B E E), F.property.map u.transportStarAlgEquiv.toStarAlgHom⟩

omit [CompleteSpace E] in
theorem oddFredholmTransportSelfAdjoint_square_compact
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) ^ 2 - 1)) :
    IsModuleCompact ((oddFredholmTransportSelfAdjoint u F : OddFredholmStandardOperator B) ^ 2 - 1) := by
  have h := u.transportMap_isModuleCompact u hF
  change IsModuleCompact (u.transport ((F : AdjointableMap B E E) ^ 2 - 1)) at h
  simpa only [oddFredholmTransportSelfAdjoint, pow_two, HilbertModuleEquiv.transport_sub,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_one] using h

def oddFredholmTransportUnitary
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (U : unitary (AdjointableMap B E E)) : unitary (OddFredholmStandardOperator B) :=
  ⟨u.transport (U : AdjointableMap B E E), Unitary.map_mem u.transportStarAlgEquiv.toStarAlgHom U.property⟩

set_option maxHeartbeats 1200000 in
theorem oddFredholmTransport_exponential
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (F : selfAdjoint (AdjointableMap B E E)) :
    oddFredholmTransportUnitary (B := B) (E := E) u
        (oddFredholmExponential (A := AdjointableMap B E E) F) =
      oddFredholmExponential (A := OddFredholmStandardOperator B)
        (oddFredholmTransportSelfAdjoint (B := B) (E := E) u F) := by
  let φ : AdjointableMap B E E →+* OddFredholmStandardOperator B := {
    toFun := u.transport
    map_one' := u.transport_one
    map_mul' := u.transport_mul
    map_zero' := u.transport_zero
    map_add' := u.transport_add }
  have hφ (S : AdjointableMap B E E) : φ S = u.transport S := rfl
  have hφcont : Continuous φ :=
    AddMonoidHomClass.continuous_of_bound φ 1 (fun S => by
      change ‖u.transport S‖ ≤ 1 * ‖S‖
      simpa only [one_mul, HilbertModuleEquiv.transport] using u.transportMap_norm_le u S)
  let +nondep : NormedAlgebra ℚ (AdjointableMap B E E) :=
    NormedAlgebra.restrictScalars ℚ ℂ (AdjointableMap B E E)
  let +nondep : NormedAlgebra ℚ (OddFredholmStandardOperator B) :=
    NormedAlgebra.restrictScalars ℚ ℂ (OddFredholmStandardOperator B)
  have h := NormedSpace.map_exp
    (𝔸 := AdjointableMap B E E) (𝔹 := OddFredholmStandardOperator B)
    φ hφcont
    (Complex.I • ((Real.pi : ℂ) • ((F : AdjointableMap B E E) + 1)))
  simp only [hφ, HilbertModuleEquiv.transport_smul, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_one] at h
  apply Subtype.ext
  change u.transport (NormedSpace.exp
      (Complex.I • (Real.pi • ((F : AdjointableMap B E E) + 1)))) =
    NormedSpace.exp (Complex.I • (Real.pi •
      (u.transport (F : AdjointableMap B E E) + 1)))
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! h

omit [CompleteSpace E] in
theorem oddFredholmTransportUnitary_sub_one_isModuleCompact
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddFredholmTransportUnitary u U : OddFredholmStandardOperator B) - 1) := by
  have h := u.transportMap_isModuleCompact u hU
  change IsModuleCompact (u.transport ((U : AdjointableMap B E E) - 1)) at h
  simpa only [oddFredholmTransportUnitary, HilbertModuleEquiv.transport_sub,
    HilbertModuleEquiv.transport_one] using h

/-- The concrete unitary relating two absorptions; its source and target are H_B. -/
def oddFredholmAbsorptionChange
    (u v : HilbertModuleEquiv B E (StandardCountableHilbertModule B)) :
    HilbertModuleEquiv B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B) :=
  u.symm.trans v

omit [CompleteSpace E] in
theorem oddFredholmAbsorptionChange_transport
    (u v : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (T : AdjointableMap B E E) :
    (oddFredholmAbsorptionChange u v).transport (u.transport T) = v.transport T := by
  ext x
  change v (u.symm (u (T (u.symm (u (v.symm x)))))) = v (T (v.symm x))
  simp only [HilbertModuleEquiv.symm_apply_apply]

omit [CompleteSpace E] in
/-- The genuine index of a compact unitary does not depend on which actual
module unitary identifies its module with H_B. -/
theorem oddFredholmTransportUnitaryIndex_independent
    (u v : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    oddFredholmStandardUnitaryIndex (oddFredholmTransportUnitary u U)
      (oddFredholmTransportUnitary_sub_one_isModuleCompact u U hU) =
      oddFredholmStandardUnitaryIndex (oddFredholmTransportUnitary v U)
        (oddFredholmTransportUnitary_sub_one_isModuleCompact v U hU) := by
  have he : oddFredholmConjugateUnitary
      (oddFredholmStandardEquivUnitary (oddFredholmAbsorptionChange u v))
      (oddFredholmTransportUnitary u U) = oddFredholmTransportUnitary v U := by
    apply Subtype.ext
    rw [← oddFredholmStandardEquiv_transport_unitary]
    exact oddFredholmAbsorptionChange_transport u v (U : AdjointableMap B E E)
  have h := oddFredholmStandardUnitaryIndex_conjugation
    (oddFredholmStandardEquivUnitary (oddFredholmAbsorptionChange u v))
    (oddFredholmTransportUnitary u U) (oddFredholmTransportUnitary_sub_one_isModuleCompact u U hU)
  simpa only [he] using h.symm

def oddFredholmAbsorbedIndex
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) ^ 2 - 1)) : OperatorK1 B :=
  oddFredholmStandardIndex (oddFredholmTransportSelfAdjoint u F)
    (oddFredholmTransportSelfAdjoint_square_compact u F hF)

/-- The actual exponential index is independent of an actual absorption;
this conclusion is proved, rather than imposed as a comparison hypothesis. -/
theorem oddFredholmAbsorbedIndex_independent
    (u v : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) ^ 2 - 1)) :
    oddFredholmAbsorbedIndex u F hF = oddFredholmAbsorbedIndex v F hF := by
  have h := oddFredholmTransportUnitaryIndex_independent u v (oddFredholmExponential F)
    (oddFredholmExponential_sub_one_isModuleCompact F (by simpa only [pow_two] using hF))
  simpa only [oddFredholmAbsorbedIndex, oddFredholmStandardIndex, oddFredholmTransport_exponential] using h

set_option maxHeartbeats 1200000 in
/-- The selected standard stabilization can be replaced by any concrete
absorption of E ⊕ H_B. -/
theorem oddFredholmStabilizedIndex_eq_absorption
    (hE : IsCountablyGeneratedModule B E) (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1))
    (u : HilbertModuleEquiv B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B)) :
    oddFredholmStabilizedIndex hE F hF = oddFredholmAbsorbedIndex u
      ⟨oddFredholmStandardAugmentedOperator F, oddFredholmStandardAugmentedOperator_isSelfAdjoint F⟩
      (by simpa only [pow_two] using oddFredholmStandardAugmentedOperator_square_compact F hF) := by
  have h := oddFredholmAbsorbedIndex_independent (standardModuleStabilization hE) u
    ⟨oddFredholmStandardAugmentedOperator F, oddFredholmStandardAugmentedOperator_isSelfAdjoint F⟩
    (by simpa only [pow_two] using oddFredholmStandardAugmentedOperator_square_compact F hF)
  simpa only [oddFredholmStabilizedIndex, oddFredholmStandardStabilizedOperator,
    oddFredholmAbsorbedIndex, oddFredholmTransportSelfAdjoint] using h

end BC4lean.KKTheory
