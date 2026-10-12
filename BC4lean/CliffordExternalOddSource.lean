import BC4lean.CliffordExternalOddModule

/-! # Genuine source Clifford action on the odd external module

The second source Clifford generator acts by the original semilinear pair
grading together with the new Clifford generator. On actual completed row
coordinates this is the corrected Pauli operator −σ_y. The full source
representation consequently agrees with the genuine matrix Morita cycle.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddSource
open scoped TensorProduct
open CliffordExternalOddCoordinates

variable {B C H : Type*} [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [sourceComplete : CompleteSpace H]

local instance cliffordExternalOddSourceLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

def evenCoefficient (b : B × B) : B := (2 : ℂ)⁻¹ • (b.1 + b.2)
def oddCoefficient (b : B × B) : B := (2 : ℂ)⁻¹ • (b.1 - b.2)

theorem diagonal_rotation (T : AdjointableMap C H H) (x : HilbertModuleSum C H H) :
    CliffordOddPauliRotation.rotation (sumMap T T x) =
      sumMap T T (CliffordOddPauliRotation.rotation x) := by
  apply Prod.ext <;>
    simp only [CliffordOddPauliRotation.rotation_apply, sumMap_apply,
      sumMk_fst, sumMk_snd, map_add, map_smul]

omit sourceComplete in
theorem representation_split [CompleteSpace H] (φ : B →⋆ₙₐ[ℂ] AdjointableMap C H H) (b : B × B) :
    sumMap (φ b.1) (φ b.2) =
      sumMap (φ (evenCoefficient b)) (φ (evenCoefficient b)) +
        sumMap (φ (oddCoefficient b)) (-φ (oddCoefficient b)) := by
  ext x
  apply Prod.ext <;>
    simp [sumMap_apply, evenCoefficient, oddCoefficient, map_smul, map_add,
      map_sub] <;> module

theorem representation_rotation_symm
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C H H) (b : B × B)
    (x : HilbertModuleSum C H H) :
    sumMap (φ b.1) (φ b.2) (CliffordOddPauliRotation.hilbertEquiv.symm x) =
      CliffordOddPauliRotation.hilbertEquiv.symm
        (sumMap (φ (evenCoefficient b)) (φ (evenCoefficient b)) x +
          CliffordOddSourceCycle.operator (-φ (oddCoefficient b)) x) := by
  apply CliffordOddPauliRotation.hilbertEquiv.injective
  simp only [HilbertModuleEquiv.apply_symm_apply]
  change CliffordOddPauliRotation.rotation
    (sumMap (φ b.1) (φ b.2) (CliffordOddPauliRotation.hilbertEquiv.symm x)) = _
  rw [representation_split, AdjointableMap.coe_add_apply, map_add,
    diagonal_rotation, CliffordOddPauliRotation.rotation_signed_diagonal]
  change sumMap (φ (evenCoefficient b)) (φ (evenCoefficient b))
      (CliffordOddPauliRotation.hilbertEquiv (CliffordOddPauliRotation.hilbertEquiv.symm x)) +
    CliffordOddSourceCycle.operator (-φ (oddCoefficient b))
      (CliffordOddPauliRotation.hilbertEquiv (CliffordOddPauliRotation.hilbertEquiv.symm x)) = _
  rw [HilbertModuleEquiv.apply_symm_apply]

omit sourceComplete in
/-- The original grading and new Clifford generator supply the actual source action. -/
theorem pureColumns_source [CompleteSpace H] (R T : AdjointableMap C H H)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    (sumMap R R (pureColumns y z).1 + CliffordOddSourceCycle.operator (-T) (pureColumns y z).1,
      sumMap R R (pureColumns y z).2 + CliffordOddSourceCycle.operator (-T) (pureColumns y z).2) =
        pureColumns (cliffordPairMap R R y) z +
          pureColumns (cliffordPairMk (T y.2) (T y.1)) (CliffordOne.epsilon * z) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [pureColumns, sumMap_apply, CliffordOddSourceCycle.operator_apply,
      cliffordPairMap_apply, cliffordPairMk, CliffordOne.epsilon,
      CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      map_smul, smul_smul] <;>
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- The actual completed representation realizes the full external source formula. -/
theorem coordinates_source_tmul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C H H) (b : B × B)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    interiorModuleTensorOperator GradedMatrixMoritaRow.leftAction
      (sumMap (φ b.1) (φ b.2)) (coordinates (y ⊗ₜ[ℂ] z)) =
        coordinates ((cliffordPairMap (φ (evenCoefficient b)) (φ (evenCoefficient b)) y) ⊗ₜ[ℂ] z +
          (cliffordPairMk (φ (oddCoefficient b) y.2) (φ (oddCoefficient b) y.1)) ⊗ₜ[ℂ]
            (CliffordOne.epsilon * z)) := by
  simp only [coordinates_apply, MatrixRowCoordinateAction.operator_coordinateSum,
    rowCoordinates_tmul, representation_rotation_symm, map_add]
  have h := pureColumns_source (φ (evenCoefficient b)) (φ (oddCoefficient b)) y z
  let U : RowCoordinates (C := C) (H := H) ≃ₗ[ℂ] RowCoordinates (C := C) (H := H) :=
    (CliffordOddPauliRotation.hilbertEquiv (C := C) (H := H)).symm.linearIsometryEquiv.toLinearEquiv.prodCongr
      (CliffordOddPauliRotation.hilbertEquiv (C := C) (H := H)).symm.linearIsometryEquiv.toLinearEquiv
  have hrot := congrArg U h
  rw [map_add] at hrot
  have hsum := congrArg
    (MatrixHilbertModuleCoordinateEmbedding.coordinateSum
      (C := C) (H := HilbertModuleSum C H H)) hrot
  rw [map_add] at hsum
  simpa only [U, LinearEquiv.prodCongr_apply, map_add,
    LinearIsometryEquiv.coe_toLinearEquiv] using hsum

end BC4lean.KKTheory.CliffordExternalOddSource
