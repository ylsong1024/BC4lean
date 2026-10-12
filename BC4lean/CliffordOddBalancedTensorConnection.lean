import BC4lean.CliffordOddBalancedTensorCompatibility
import BC4lean.CliffordParityCycle
import BC4lean.GradedConnectionDefectAlgebra

/-! # Actual creators under the odd balanced tensor unitary

Every original pair vector has a genuine rectangular diagonal creator in
the completed Hilbert direct sum. The signed creation defect, including
the adjoint defect, transfers through the onto coefficient-form unitary.
No restriction to homogeneous or equal-coordinate vectors is made.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddBalancedTensor

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance cliffordOddBalancedTensorConnectionLocalInstance1 : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete
local instance cliffordOddBalancedTensorConnectionLocalInstance2 : CompleteSpace (Target (E := E) φ) := hilbertModuleSum_complete

def coordinateCreation (x : CliffordPairModule B E) :
    AdjointableMap C (HilbertModuleSum C F F) (Target (E := E) φ) :=
  sumMap (moduleCreationMap φ x.1) (moduleCreationMap φ x.2)

@[simp] theorem coordinateCreation_apply (x : CliffordPairModule B E)
    (y : HilbertModuleSum C F F) :
    coordinateCreation φ x y = sumMk
      (interiorModuleTensorMk φ x.1 y.fst) (interiorModuleTensorMk φ x.2 y.snd) := by
  simp only [coordinateCreation, sumMap_apply, moduleCreationMap_apply]
  rfl

theorem transport_creation (x : CliffordPairModule B E) :
    (hilbertEquiv φ).toAdjointable.comp
      (moduleCreationMap (CliffordOddSourceCycle.representation φ) x) =
        coordinateCreation φ x := by
  ext y
  change hilbertEquiv φ
    (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ) x y) =
      coordinateCreation φ x y
  rw [hilbertEquiv_mk, coordinateCreation_apply]

/-- The actual operator transported to the complete base-sum carrier. -/
def coordinateOperator
    (R : AdjointableMap C (Source (E := E) φ) (Source (E := E) φ)) :
    AdjointableMap C (Target (E := E) φ) (Target (E := E) φ) :=
  (hilbertEquiv φ).transport R

theorem transport_creation_defect
    (R : AdjointableMap C (Source (E := E) φ) (Source (E := E) φ))
    (D : AdjointableMap C (HilbertModuleSum C F F) (HilbertModuleSum C F F))
    (x : CliffordPairModule B E) :
    (hilbertEquiv φ).toAdjointable.comp
      (R.comp (moduleCreationMap (CliffordOddSourceCycle.representation φ) x) -
        (moduleCreationMap (CliffordOddSourceCycle.representation φ)
          (cliffordPairGrading.grading x)).comp D) =
      (coordinateOperator φ R).comp (coordinateCreation φ x) -
        (coordinateCreation φ (cliffordPairGrading.grading x)).comp D := by
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.map_sub,
    coordinateOperator, HilbertModuleEquiv.transport_apply,
    ← transport_creation φ x, ← transport_creation φ (cliffordPairGrading.grading x),
    AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.symm_apply_apply]

/-- Compactness is equivalent on the original and the actual complete
coordinate carrier, since the coefficient-form map is onto. -/
theorem coordinate_creation_defect_compact_iff
    (R : AdjointableMap C (Source (E := E) φ) (Source (E := E) φ))
    (D : AdjointableMap C (HilbertModuleSum C F F) (HilbertModuleSum C F F))
    (x : CliffordPairModule B E) :
    IsModuleCompact ((coordinateOperator φ R).comp (coordinateCreation φ x) -
      (coordinateCreation φ (cliffordPairGrading.grading x)).comp D) ↔
    IsModuleCompact (R.comp (moduleCreationMap (CliffordOddSourceCycle.representation φ) x) -
      (moduleCreationMap (CliffordOddSourceCycle.representation φ)
        (cliffordPairGrading.grading x)).comp D) := by
  rw [← transport_creation_defect]
  constructor
  · intro h
    have hs := h.comp_left (hilbertEquiv φ).symm.toAdjointable
    convert hs using 1
    ext y
    simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
      HilbertModuleEquiv.symm_apply_apply]
  · intro h
    exact h.comp_left (hilbertEquiv φ).toAdjointable

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : OddKasparovCycle α β E) (d : OddKasparovCycle β γ F)
  (R : AdjointableMap C (Source (E := E) d.representation)
    (Source (E := E) d.representation))

/-- All four original homogeneous laws imply the true coordinate defect
for each arbitrary original pair vector. -/
theorem coordinate_connection_creation_defect
    (hR : GradedKasparovConnection c.cliffordExpansion (CliffordOddSourceCycle.cycle d) R)
    (x : CliffordPairModule B E) :
    IsModuleCompact ((coordinateOperator d.representation R).comp
      (coordinateCreation d.representation x) -
        (coordinateCreation d.representation (cliffordPairGrading.grading x)).comp
          (CliffordOddSourceCycle.operator d.operator)) :=
  (coordinate_creation_defect_compact_iff d.representation R
    (CliffordOddSourceCycle.operator d.operator) x).2 (hR.creation_defect x)

/-- The adjoint law uses the actual stars of both original operators. -/
theorem coordinate_connection_creation_adjoint_defect
    (hR : GradedKasparovConnection c.cliffordExpansion (CliffordOddSourceCycle.cycle d) R)
    (x : CliffordPairModule B E) :
    IsModuleCompact ((star (coordinateOperator d.representation R)).comp
      (coordinateCreation d.representation x) -
        (coordinateCreation d.representation (cliffordPairGrading.grading x)).comp
          (CliffordOddSourceCycle.operator (star d.operator))) := by
  have h := (coordinate_creation_defect_compact_iff d.representation (star R)
    (star (CliffordOddSourceCycle.operator d.operator)) x).2
      (hR.creation_adjoint_defect x)
  simpa only [coordinateOperator, HilbertModuleEquiv.transport_star,
    CliffordOddSourceCycle.operator_star] using h

end BC4lean.KKTheory.CliffordOddBalancedTensor
