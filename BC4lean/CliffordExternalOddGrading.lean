import BC4lean.CliffordExternalOddModule
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # The actual grading of the odd external Clifford tensor

The completed module has the genuine tensor grading σ_x on the first
factor and the matrix row grading on the second. Its elementary external
formula is the original pair swap tensored with the second Clifford swap.
The completed-coordinate identities follow from coefficient approximate
units and the actual elementary tensor grading, without a coefficient unit.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddGrading
open scoped InnerProductSpace TensorProduct Topology
open CliffordExternalOddCoordinates MatrixHilbertModuleCoordinateEmbedding

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [externalOddGradingComplete : CompleteSpace H]

local instance cliffordExternalOddGradingLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

/-- The actual completed tensor grading, with both factor gradings explicit. -/
def grading : GradedHilbertModule (GradedMatrixMoritaMatrix.grading (B := C))
    (ExternalModule (C := C) (H := H)) :=
  CliffordOddSourceCycle.grading.interiorTensor GradedMatrixMoritaRow.grading
    GradedMatrixMoritaRow.leftAction_graded

set_option maxHeartbeats 1200000 in
theorem grading_coordinate_zero (x : HilbertModuleSum C H H) :
    grading.grading (coordinate 0 x) = coordinate 0 (sumSwap x) := by
  have hleft := (grading.grading.continuous.tendsto (coordinate (C := C) (H := HilbertModuleSum C H H) 0 x)).comp
    (((coordinate (C := C) (H := HilbertModuleSum C H H) 0).continuous.tendsto x).comp
      (tendsto_coefficient_approximateUnit_smul (D := Cᵐᵒᵖ) x))
  have hright := ((coordinate (C := C) (H := HilbertModuleSum C H H) 0).continuous.tendsto
    (sumSwap x)).comp
      (tendsto_coefficient_approximateUnit_smul (D := Cᵐᵒᵖ) (sumSwap x))
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall fun a => by
    change (coordinate (C := C) (H := HilbertModuleSum C H H)) 0 (a • sumSwap x) =
      (grading (C := C) (H := H)).grading
        ((coordinate (C := C) (H := HilbertModuleSum C H H)) 0 (a • x))
    rw [coordinate_smul, coordinate_smul]
    have hφ : ModuleTensorRepresentationGraded
        (δB := (CStarGrading.trivial : CStarGrading C))
        (GradedMatrixMoritaRow.leftAction (B := C))
        (GradedMatrixMoritaRow.grading (B := C)) := by
      intro b y
      exact GradedMatrixMoritaRow.leftAction_graded (B := C) b y
    change interiorModuleTensorMk (E := HilbertModuleSum C H H)
        (GradedMatrixMoritaRow.leftAction (B := C)) (sumSwap x) (rowElement 0 a) =
      ((CliffordOddSourceCycle.grading (C := C) (H := H)).interiorTensor
        (φ := GradedMatrixMoritaRow.leftAction (B := C))
        (GradedMatrixMoritaRow.grading (B := C)) hφ).grading
        (interiorModuleTensorMk (E := HilbertModuleSum C H H)
          (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement 0 a))
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := GradedMatrixMoritaRow.leftAction (B := C))
      (CliffordOddSourceCycle.grading (C := C) (H := H))
      (GradedMatrixMoritaRow.grading (B := C)) hφ x (rowElement 0 a)]
    change interiorModuleTensorMk (E := HilbertModuleSum C H H)
        (GradedMatrixMoritaRow.leftAction (B := C)) (sumSwap x) (rowElement 0 a) =
      interiorModuleTensorMk (E := HilbertModuleSum C H H)
        (GradedMatrixMoritaRow.leftAction (B := C)) (sumSwap x)
          (GradedMatrixMoritaRow.parity (rowElement 0 a))
    rw [rowElement_parity_zero]

set_option maxHeartbeats 1200000 in
theorem grading_coordinate_one (x : HilbertModuleSum C H H) :
    grading.grading (coordinate 1 x) = -coordinate 1 (sumSwap x) := by
  have hleft := (grading.grading.continuous.tendsto (coordinate (C := C) (H := HilbertModuleSum C H H) 1 x)).comp
    (((coordinate (C := C) (H := HilbertModuleSum C H H) 1).continuous.tendsto x).comp
      (tendsto_coefficient_approximateUnit_smul (D := Cᵐᵒᵖ) x))
  have hright := (((coordinate (C := C) (H := HilbertModuleSum C H H) 1).continuous.tendsto
    (sumSwap x)).comp
      (tendsto_coefficient_approximateUnit_smul (D := Cᵐᵒᵖ) (sumSwap x))).neg
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall fun a => by
    change -((coordinate (C := C) (H := HilbertModuleSum C H H)) 1 (a • sumSwap x)) =
      (grading (C := C) (H := H)).grading
        ((coordinate (C := C) (H := HilbertModuleSum C H H)) 1 (a • x))
    rw [coordinate_smul, coordinate_smul]
    have hφ : ModuleTensorRepresentationGraded
        (δB := (CStarGrading.trivial : CStarGrading C))
        (GradedMatrixMoritaRow.leftAction (B := C))
        (GradedMatrixMoritaRow.grading (B := C)) := by
      intro b y
      exact GradedMatrixMoritaRow.leftAction_graded (B := C) b y
    change -(interiorModuleTensorMk (E := HilbertModuleSum C H H)
        (GradedMatrixMoritaRow.leftAction (B := C)) (sumSwap x) (rowElement 1 a)) =
      ((CliffordOddSourceCycle.grading (C := C) (H := H)).interiorTensor
        (φ := GradedMatrixMoritaRow.leftAction (B := C))
        (GradedMatrixMoritaRow.grading (B := C)) hφ).grading
        (interiorModuleTensorMk (E := HilbertModuleSum C H H)
          (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement 1 a))
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := GradedMatrixMoritaRow.leftAction (B := C))
      (CliffordOddSourceCycle.grading (C := C) (H := H))
      (GradedMatrixMoritaRow.grading (B := C)) hφ x (rowElement 1 a)]
    change -(interiorModuleTensorMk (E := HilbertModuleSum C H H)
        (GradedMatrixMoritaRow.leftAction (B := C)) (sumSwap x) (rowElement 1 a)) =
      interiorModuleTensorMk (E := HilbertModuleSum C H H)
        (GradedMatrixMoritaRow.leftAction (B := C)) (sumSwap x)
          (GradedMatrixMoritaRow.parity (rowElement 1 a))
    rw [rowElement_parity_one, map_neg]

/-- Both actual matrix coordinates retain their correct grading signs. -/
theorem grading_coordinateSum (x : RowCoordinates (C := C) (H := H)) :
    grading.grading (coordinateSum x) = coordinateSum (sumSwap x.1, -sumSwap x.2) := by
  simp only [coordinateSum_apply, map_add, grading_coordinate_zero,
    grading_coordinate_one, map_neg]

omit externalOddGradingComplete in
theorem pureColumns_grading [CompleteSpace H] (y : CliffordPairModule C H) (z : CliffordOne) :
    pureColumns (cliffordPairMk y.2 y.1) (CliffordOne.grading.automorphism z) =
      (sumSwap (pureColumns y z).1, -sumSwap (pureColumns y z).2) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [pureColumns, cliffordPairMk, CliffordOne.grading, CliffordOne.swap,
      CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient, sumSwap_apply] <;> module

theorem rotation_symm_swap (x : HilbertModuleSum C H H) :
    CliffordOddPauliRotation.hilbertEquiv.symm (sumSwap x) =
      sumSwap (CliffordOddPauliRotation.hilbertEquiv.symm x) := by
  apply CliffordOddPauliRotation.hilbertEquiv.injective
  simp only [HilbertModuleEquiv.apply_symm_apply]
  change sumSwap x = CliffordOddPauliRotation.rotation
    (sumSwap (CliffordOddPauliRotation.hilbertEquiv.symm x))
  rw [CliffordOddPauliRotation.rotation_swap]
  change sumSwap x = sumSwap
    (CliffordOddPauliRotation.hilbertEquiv (CliffordOddPauliRotation.hilbertEquiv.symm x))
  rw [HilbertModuleEquiv.apply_symm_apply]

/-- The genuine completed tensor grading is the external tensor grading. -/
theorem coordinates_grading_tmul (y : CliffordPairModule C H) (z : CliffordOne) :
    grading.grading (coordinates (y ⊗ₜ[ℂ] z)) =
      coordinates ((cliffordPairMk y.2 y.1) ⊗ₜ[ℂ] (CliffordOne.grading.automorphism z)) := by
  simp only [coordinates_apply, grading_coordinateSum, rowCoordinates_tmul,
    pureColumns_grading, rotation_symm_swap, HilbertModuleEquiv.map_neg]

end BC4lean.KKTheory.CliffordExternalOddGrading
