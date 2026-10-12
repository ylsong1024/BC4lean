import BC4lean.FinitePairedPrefixCoordinates
import BC4lean.StandardCountablePrefixProjectionIndex
import BC4lean.RectangularFredholmProjectionIndex

/-! # Genuine index recovery for an equal-scalar finite projection pair

The aligned source and target projective absorptions give an actual
contractive standard Fredholm map. Its whole Julia projection difference is
the corner of the recovered finite Julia matrix. Actual paired coordinates,
full scalar equality and finite reindexing identify the supported index.
The finite partial-isometry relation then recovers precisely [p]-[q].
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] [Fintype ι] [DecidableEq ι]
local notation "Std" => StandardCountableHilbertModule B
local notation "StdPair" => HilbertModuleSum B Std Std
local notation "StdEnd" => AdjointableMap B StdPair StdPair

local instance standardFiniteJuliaProjectionIndexRecoveryLocalInstance01 (κ : Type) [Fintype κ] : CompleteSpace (FiniteStandardModule B κ) := finiteStandardModule_complete
local instance standardFiniteJuliaProjectionIndexRecoveryLocalInstance02 (A : Type*) [CStarAlgebra A] : PartialOrder A := CStarAlgebra.spectralOrder A
local instance standardFiniteJuliaProjectionIndexRecoveryLocalInstance03 (A : Type*) [CStarAlgebra A] : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance standardFiniteJuliaProjectionIndexRecoveryLocalInstance04 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

theorem finitePairedPrefixReindex_reference :
    CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι))
      (matrixBlockSum (0 : CStarMatrix ι ι (Unitization ℂ B)) 1) =
        pairedStandardFiniteReferenceMatrix (B := B) (Fintype.card ι) := by
  apply CStarMatrix.ext
  intro i j
  cases i <;> cases j
  all_goals
    simp [CStarMatrix.reindexₐ_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      finitePairedPrefixReindex, matrixBlockSum, Matrix.fromBlocks,
      pairedStandardFiniteReferenceMatrix, Matrix.diagonal_apply]

omit [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] [DecidableEq ι] in
theorem unitizationScalarMatrix_reindex {κ : Type} [Fintype κ]
    (e : ι ≃ κ) (M : CStarMatrix ι ι (Unitization ℂ B)) :
    unitizationScalarMatrix (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e M) =
      CStarMatrix.reindexₐ ℂ ℂ e (unitizationScalarMatrix M) := by
  apply CStarMatrix.ext
  intro i j
  rfl

theorem finiteAlignedUnitizationJulia_difference_prefix
    (p q : MatrixProjection (Unitization ℂ B) ι) :
    juliaFredholmProjection (finiteAlignedUnitizationFredholm p q) - standardCountablePairedReferenceProjection =
      ((pairedStandardFiniteInclusion (Fintype.card ι)).comp
        (unitizedModuleMatrixRepresentation
          (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι))
            (finiteJuliaRecoveryProjection p q) - pairedStandardFiniteReferenceMatrix (Fintype.card ι)))).comp
              (pairedStandardFiniteInclusion (Fintype.card ι)).adjoint := by
  let e := oddKTheoryFiniteReindexEquiv (B := B) (finitePairedPrefixReindex (ι := ι))
  let A : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B) :=
    finiteJuliaRecoveryProjection p q - matrixBlockSum (0 : CStarMatrix ι ι (Unitization ℂ B)) 1
  have hDiff : juliaFredholmProjection (finiteAlignedUnitizationFredholm p q) -
      standardCountablePairedReferenceProjection =
      ((finitePairedPrefixCoordinateInclusion (B := B) (ι := ι)).comp
        (unitizedModuleMatrixRepresentation A)).comp finitePairedPrefixCoordinateInclusion.adjoint := by
    rw [finiteAlignedUnitizationJulia_difference_matrix]
    ext x
    rfl
  have he : e.transport (unitizedModuleMatrixRepresentation A) =
      unitizedModuleMatrixRepresentation
        (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι)) A) := by
    ext x
    rw [HilbertModuleEquiv.transport_apply, oddKTheoryFiniteReindexEquiv_matrix,
      HilbertModuleEquiv.apply_symm_apply]
  rw [hDiff, finitePairedPrefixCoordinateInclusion_eq_reindex,
    AdjointableMap.adjoint_comp]
  have hA : CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι)) A =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι))
        (finiteJuliaRecoveryProjection p q) - pairedStandardFiniteReferenceMatrix (Fintype.card ι) := by
    rw [A, map_sub, finitePairedPrefixReindex_reference]
  rw [← hA, ← he]
  ext x
  rfl

theorem finiteAlignedUnitizationFredholm_index_recovery
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B)) =
      unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B)))
    (hs : IsModuleCompact (1 - (finiteAlignedUnitizationFredholm p q).adjoint.comp
      (finiteAlignedUnitizationFredholm p q)))
    (ht : IsModuleCompact ((finiteAlignedUnitizationFredholm p q).comp
      (finiteAlignedUnitizationFredholm p q).adjoint - 1)) :
    standardNormalizedRectangularFredholmIndex (finiteAlignedUnitizationFredholm p q) hs ht =
      unitizationRelativeProjectionK0 p q p.property q.property hScalar := by
  let n := Fintype.card ι
  let e := finitePairedPrefixReindex (ι := ι)
  let R : StdEnd := juliaFredholmProjection (finiteAlignedUnitizationFredholm p q)
  let r : MatrixProjection (Unitization ℂ B) (ι ⊕ ι) := finiteJuliaRecoveryProjection p q
  let q₀ : MatrixProjection (Unitization ℂ B) (ι ⊕ ι) := projectionBlockSum Projection.zero Projection.one
  let M := CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e (r : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B))
  have hM : IsStarProjection M := r.property.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e).toStarAlgHom
  have hs₀ : unitizationScalarMatrix (r : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) =
      unitizationScalarMatrix (q₀ : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) := by
    rw [finiteJuliaRecoveryProjection_scalar p q hScalar]
    apply CStarMatrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hsM : unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) := by
    rw [M, unitizationScalarMatrix_reindex, hs₀, ← unitizationScalarMatrix_reindex]
    rw [finitePairedPrefixReindex_reference]
  have hR : IsStarProjection R := juliaFredholmProjection_isStarProjection _
    (finiteProjectionAlignedFredholm_norm_le_one _ _ _ _)
  have hc : IsModuleCompact (R - standardCountablePairedReferenceProjection) :=
    juliaFredholmProjection_difference_isModuleCompact _
      (finiteProjectionAlignedFredholm_norm_le_one _ _ _ _) hs ht
  change standardCountableRelativeProjectionIndex
    (juliaFredholmProjection (globalFredholmNormalization (finiteAlignedUnitizationFredholm p q))) _ _ = _
  rw [finiteAlignedUnitizationNormalization_fixed]
  rw [standardCountableRelativeProjectionIndex_prefix_matrix R hR hc n M hM hsM
    (finiteAlignedUnitizationJulia_difference_prefix p q)]
  apply operatorK0Inclusion_injective
  have hRef : pairedStandardFiniteReferenceMatrix (B := B) n =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e q₀ :=
    finitePairedPrefixReindex_reference.symm
  change k0Projection (unitizationFiniteProjection M hM) -
      k0Projection (unitizationFiniteProjection (pairedStandardFiniteReferenceMatrix n) _) = _
  rw [hRef]
  rw [unitizationFiniteProjection_k0_reindex r e,
    unitizationFiniteProjection_k0_reindex q₀ e]
  exact finiteJuliaRecoveryProjection_k0 p q

end BC4lean.KKTheory
