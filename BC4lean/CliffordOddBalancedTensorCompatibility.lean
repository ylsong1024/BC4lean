import BC4lean.CliffordOddBalancedTensor
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # Actual grading and operator compatibility of odd balancing

The full completed unitary preserves the swap tensor grading. Its induced
first-factor map is the genuine diagonal pair of the base tensor operators,
with the original signed odd operator retaining its minus sign.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddBalancedTensor
open scoped InnerProductSpace

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance cliffordOddBalancedTensorCompatibilityLocalInstance1 : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete
local instance cliffordOddBalancedTensorCompatibilityLocalInstance2 : CompleteSpace (Target (E := E) φ) := hilbertModuleSum_complete

omit [PartialOrder B] [StarOrderedRing B] [CompleteSpace F] in
theorem representation_graded :
    ModuleTensorRepresentationGraded (δB := cliffordCoefficientGrading)
      (CliffordOddSourceCycle.representation φ) CliffordOddSourceCycle.grading := by
  intro b y
  change sumSwap (sumMap (φ b.1) (φ b.2) y) =
    sumMap (φ b.2) (φ b.1) (sumSwap y)
  simp only [sumSwap_apply, sumMap_apply, sumMk_fst, sumMk_snd]

def sourceGrading : GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
    (Source (E := E) φ) :=
  cliffordPairGrading.interiorTensor CliffordOddSourceCycle.grading (representation_graded φ)

/-- The genuine completed unitary intertwines both original tensor gradings. -/
theorem hilbertEquiv_grading (u : Source (E := E) φ) :
    hilbertEquiv φ ((sourceGrading φ).grading u) = sumSwap (hilbertEquiv φ u) := by
  let L : Source (E := E) φ →L[ℂ] Target (E := E) φ :=
    (hilbertEquiv (E := E) φ).linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  let J : Source (E := E) φ →L[ℂ] Source (E := E) φ :=
    (sourceGrading (E := E) φ).grading.toLinearIsometry.toContinuousLinearMap
  let K : Target (E := E) φ →L[ℂ] Target (E := E) φ :=
    (sumSwap (B := C) (E := BaseTensor (E := E) φ)
      (F := BaseTensor (E := E) φ)).toLinearIsometry.toContinuousLinearMap
  have h : L.comp J = K.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ ((sourceGrading φ).grading
      (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ) x y)) =
        sumSwap (hilbertEquiv φ
          (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ) x y))
    rw [sourceGrading, GradedHilbertModule.interiorTensor_grading_mk,
      hilbertEquiv_mk, hilbertEquiv_mk]
    rfl
  exact DFunLike.congr_fun h u

/-- Both genuine first-factor maps pass through the completed balanced unitary. -/
theorem hilbertEquiv_firstFactor (S T : AdjointableMap B E E) (u : Source (E := E) φ) :
    hilbertEquiv φ (interiorModuleTensorOperator (CliffordOddSourceCycle.representation φ)
      (cliffordPairMap S T) u) =
        sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ T)
          (hilbertEquiv φ u) := by
  let L : Source (E := E) φ →L[ℂ] Target (E := E) φ :=
    (hilbertEquiv (E := E) φ).linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have h : L.comp
      (interiorModuleTensorOperator (CliffordOddSourceCycle.representation φ) (cliffordPairMap S T)).toCLM =
    (sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ T)).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ
      (interiorModuleTensorOperator (CliffordOddSourceCycle.representation φ) (cliffordPairMap S T)
        (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ) x y)) =
      sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ T)
        (hilbertEquiv φ (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ) x y))
    rw [interiorModuleTensorOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext <;>
      simp only [cliffordPairMap_apply, cliffordPairMk, sumMap_apply,
        sumMk_fst, sumMk_snd, interiorModuleTensorOperator_mk]
  exact DFunLike.congr_fun h u

/-- The original odd first operator retains the correct actual signed diagonal. -/
theorem hilbertEquiv_signedFirstFactor (T : AdjointableMap B E E) (u : Source (E := E) φ) :
    hilbertEquiv φ (interiorModuleTensorOperator (CliffordOddSourceCycle.representation φ)
      (cliffordPairMap T (-T)) u) =
        sumMap (interiorModuleTensorOperator φ T) (-interiorModuleTensorOperator φ T)
          (hilbertEquiv φ u) := by
  rw [hilbertEquiv_firstFactor]
  have hneg : interiorModuleTensorOperator φ (-T) = -interiorModuleTensorOperator φ T :=
    map_neg (interiorModuleTensorOperatorHom φ) T
  rw [hneg]

end BC4lean.KKTheory.CliffordOddBalancedTensor
