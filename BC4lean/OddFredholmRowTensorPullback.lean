import BC4lean.CountableHilbertModuleTensor
import BC4lean.OddFredholmPullbackNaturality

/-! # Whole periodic row inverse and actual coefficient tensors

The genuine tensor-row unitary intertwines the actual coefficient diagonal
and all twenty-one signed coordinate rules. Continuous functional calculus
then identifies the full first-factor tensor of the periodic row operator.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

def oddFredholmRowTensorOperatorHom : OddKTheoryCountableOperator B E →⋆ₐ[ℂ]
    OddKTheoryCountableOperator C (InteriorModuleTensor (E := E) φ) :=
  (countableModuleTensorEquiv φ).transportStarAlgEquiv.toStarAlgHom.comp
    (interiorModuleTensorOperatorHom φ)

theorem oddFredholmRowTensorOperatorHom_inclusion_mk
    (T : OddKTheoryCountableOperator B E) (z : ℤ) (x : E) (y : F) :
    oddFredholmRowTensorOperatorHom φ T
      (oddKTheoryRowIntegerInclusion z (interiorModuleTensorMk φ x y)) =
    countableModuleTensorEquiv φ
      (interiorModuleTensorMk φ (T (oddKTheoryRowIntegerInclusion z x)) y) := by
  have hinc : countableModuleTensorEquiv φ
      (interiorModuleTensorMk φ (oddKTheoryRowIntegerInclusion z x) y) =
      oddKTheoryRowIntegerInclusion z (interiorModuleTensorMk φ x y) :=
    countableModuleTensorEquiv_mk_inclusion φ (oddKTheoryRowIntegerIndex z) x y
  rw [← hinc]
  change countableModuleTensorEquiv φ
    (interiorModuleTensorOperator φ T
      ((countableModuleTensorEquiv φ).symm
        (countableModuleTensorEquiv φ (interiorModuleTensorMk φ
          (oddKTheoryRowIntegerInclusion z x) y)))) = _
  rw [HilbertModuleEquiv.symm_apply_apply, interiorModuleTensorOperator_mk]

theorem oddFredholmRowTensorOperatorHom_diagonal (T : AdjointableMap B E E) :
    oddFredholmRowTensorOperatorHom φ (countableModuleDiagonal T) =
      countableModuleDiagonal (interiorModuleTensorOperator φ T) := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z
  have h : (oddFredholmRowTensorOperatorHom φ (countableModuleDiagonal T)).toCLM.comp
      (oddKTheoryRowIntegerInclusion z).toCLM =
    (countableModuleDiagonal (interiorModuleTensorOperator φ T)).toCLM.comp
      (oddKTheoryRowIntegerInclusion z).toCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [ContinuousLinearMap.comp_apply, oddFredholmRowTensorOperatorHom_inclusion_mk,
      oddKTheoryRowDiagonal_integerInclusion, interiorModuleTensorOperator_mk]
    change countableModuleTensorEquiv φ
      (interiorModuleTensorMk φ (oddKTheoryRowIntegerInclusion z (T x)) y) =
      oddKTheoryRowIntegerInclusion z (interiorModuleTensorMk φ (T x) y)
    exact countableModuleTensorEquiv_mk_inclusion φ (oddKTheoryRowIntegerIndex z) (T x) y
  exact DFunLike.congr_fun h

theorem oddFredholmRowTensorOperatorHom_fixed (i : OddKTheoryLoopTerm) :
    oddFredholmRowTensorOperatorHom φ (oddKTheoryRowLoopTermOperator i) =
      (oddKTheoryRowLoopTermOperator (B := C) (E := InteriorModuleTensor (E := E) φ) i) := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z
  have h : (oddFredholmRowTensorOperatorHom φ (oddKTheoryRowLoopTermOperator i)).toCLM.comp
      (oddKTheoryRowIntegerInclusion z).toCLM =
    (oddKTheoryRowLoopTermOperator (B := C) (E := InteriorModuleTensor (E := E) φ) i).toCLM.comp
      (oddKTheoryRowIntegerInclusion z).toCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [ContinuousLinearMap.comp_apply, oddFredholmRowTensorOperatorHom_inclusion_mk,
      oddKTheoryRowLoopTermOperator_coordinateRule, map_smul, LinearMap.smul_apply]
    change oddKTheoryLoopTermWeight i z •
      countableModuleTensorEquiv φ
        (interiorModuleTensorMk φ
          (oddKTheoryRowIntegerInclusion (oddKTheoryLoopTermTarget i z) x) y) =
      oddKTheoryLoopTermWeight i z •
        oddKTheoryRowIntegerInclusion (oddKTheoryLoopTermTarget i z)
          (interiorModuleTensorMk φ x y)
    exact congrArg (fun v : CountableModuleTensorTarget (E := E) φ =>
      oddKTheoryLoopTermWeight i z • v)
      (countableModuleTensorEquiv_mk_inclusion φ
        (oddKTheoryRowIntegerIndex (oddKTheoryLoopTermTarget i z)) x y)
  exact DFunLike.congr_fun h

def oddFredholmTensorOperatorUnitary (U : unitary (AdjointableMap B E E)) :
    unitary (AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) :=
  ⟨interiorModuleTensorOperator φ U, Unitary.map_mem (interiorModuleTensorOperatorHom φ) U.property⟩

theorem oddFredholmRowTensorOperatorHom_pullback (U : unitary (AdjointableMap B E E)) :
    oddFredholmRowTensorOperatorHom φ (oddFredholmRowUnitaryPullback U) =
      oddFredholmRowUnitaryPullback (oddFredholmTensorOperatorUnitary φ U) := by
  unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, oddFredholmRowTensorOperatorHom_diagonal, oddFredholmRowTensorOperatorHom_fixed]
  have h := oddKTheoryCircleCFC_map (interiorModuleTensorOperatorHom φ) (map_continuous _)
    U (oddFredholmTensorOperatorUnitary φ U) rfl (oddKTheoryLoopTermCoefficient i)
  change interiorModuleTensorOperator φ (oddKTheoryCircleCFC U (oddKTheoryLoopTermCoefficient i)) =
    oddKTheoryCircleCFC (oddFredholmTensorOperatorUnitary φ U) (oddKTheoryLoopTermCoefficient i) at h
  rw [h]

theorem countableModuleTensorEquiv_pullback (U : unitary (AdjointableMap B E E))
    (z : InteriorModuleTensor (E := CountableHilbertModuleSum B E) φ) :
    countableModuleTensorEquiv φ
      (interiorModuleTensorOperator φ (oddFredholmRowUnitaryPullback U) z) =
    oddFredholmRowUnitaryPullback (oddFredholmTensorOperatorUnitary φ U)
      (countableModuleTensorEquiv φ z) := by
  have h := congrArg (fun T => T (countableModuleTensorEquiv φ z))
    (oddFredholmRowTensorOperatorHom_pullback φ U)
  change countableModuleTensorEquiv φ
    (interiorModuleTensorOperator φ (oddFredholmRowUnitaryPullback U)
      ((countableModuleTensorEquiv φ).symm (countableModuleTensorEquiv φ z))) = _ at h
  rw [HilbertModuleEquiv.symm_apply_apply] at h
  exact h

end BC4lean.KKTheory
