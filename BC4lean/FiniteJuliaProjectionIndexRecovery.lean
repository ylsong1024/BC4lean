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
open scoped Matrix

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

omit [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] in
theorem finitePairedPrefixReindex_reference :
    CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι))
      (matrixBlockSum (0 : CStarMatrix ι ι (Unitization ℂ B)) 1) =
        pairedStandardFiniteReferenceMatrix (B := B) (Fintype.card ι) := by
  let e := finitePairedPrefixReindex (ι := ι)
  have hReindex (M : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) (i j : ι ⊕ ι) :
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e M (e i) (e j) = M i j := by
    change M (e.symm (e i)) (e.symm (e j)) = M i j
    simp only [Equiv.symm_apply_apply]
  apply CStarMatrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rw [hReindex]
  cases i <;> cases j
  all_goals
    simp [e, finitePairedPrefixReindex, matrixBlockSum, Matrix.fromBlocks,
      pairedStandardFiniteReferenceMatrix, Matrix.diagonal_apply, CStarMatrix.one_apply]

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
      ((pairedStandardFiniteInclusion (B := B) (Fintype.card ι)).comp
        (unitizedModuleMatrixRepresentation
          (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι))
            (finiteJuliaRecoveryProjection p q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) -
              pairedStandardFiniteReferenceMatrix (B := B) (Fintype.card ι)))).comp
              (pairedStandardFiniteInclusion (B := B) (Fintype.card ι)).adjoint := by
  let e := oddKTheoryFiniteReindexEquiv (B := B) (finitePairedPrefixReindex (ι := ι))
  let A : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B) :=
    (finiteJuliaRecoveryProjection p q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) -
      matrixBlockSum (0 : CStarMatrix ι ι (Unitization ℂ B)) (1 : CStarMatrix ι ι (Unitization ℂ B))
  have hReference : standardCountablePairedReferenceProjection (B := B) =
      (juliaReferenceProjection (B := B) (E := Std) (F := Std)) := by
    apply AdjointableMap.ext
    intro x
    simp only [standardCountablePairedReferenceProjection, sumMap_apply,
      AdjointableMap.coe_zero_apply, AdjointableMap.one_apply, juliaReferenceProjection_apply]
  have hDiff : juliaFredholmProjection (finiteAlignedUnitizationFredholm p q) -
      standardCountablePairedReferenceProjection =
      ((finitePairedPrefixCoordinateInclusion (B := B) (ι := ι)).comp
        (unitizedModuleMatrixRepresentation A)).comp finitePairedPrefixCoordinateInclusion.adjoint := by
    rw [hReference, finiteAlignedUnitizationJulia_difference_matrix]
    apply AdjointableMap.ext
    intro x
    rfl
  have he : e.transport (unitizedModuleMatrixRepresentation A) =
      unitizedModuleMatrixRepresentation
        (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι)) A) := by
    apply AdjointableMap.ext
    intro x
    change e (unitizedModuleMatrixRepresentation A (e.symm x)) = _
    rw [oddKTheoryFiniteReindexEquiv_matrix, HilbertModuleEquiv.apply_symm_apply]
  /- The complete reindexed Julia corner uses the same actual inclusion. -/
  rw [hDiff, finitePairedPrefixCoordinateInclusion_eq_reindex,
    AdjointableMap.adjoint_comp]
  have hA : CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι)) A =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (finitePairedPrefixReindex (ι := ι))
        (finiteJuliaRecoveryProjection p q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) -
          pairedStandardFiniteReferenceMatrix (B := B) (Fintype.card ι) := by
    dsimp only [A]
    rw [map_sub, finitePairedPrefixReindex_reference]
  rw [← hA, ← he]
  apply AdjointableMap.ext
  intro x
  rfl

/- Actual finite matrix coefficients identify the whole supported Julia corner. -/

theorem finiteAlignedUnitizationFredholm_index_recovery
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B)) =
      unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B)))
    (hs : IsModuleCompact (1 - (finiteAlignedUnitizationFredholm p q).adjoint.comp
      (finiteAlignedUnitizationFredholm p q)))
    (ht : IsModuleCompact ((finiteAlignedUnitizationFredholm p q).comp
      (finiteAlignedUnitizationFredholm p q).adjoint - 1)) :
    standardNormalizedRectangularFredholmIndex (finiteAlignedUnitizationFredholm p q) hs ht =
      unitizationRelativeProjectionK0
        (p : CStarMatrix ι ι (Unitization ℂ B))
        (q : CStarMatrix ι ι (Unitization ℂ B)) p.property q.property hScalar := by
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
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change (if i = j then (1 : ℂ) else 0) =
          (if i = j then (1 : Unitization ℂ B) else 0).fst
        by_cases hij : i = j
        · simp only [if_pos hij, Unitization.fst_one]
        · simp only [if_neg hij, Unitization.fst_zero]
  have hsM : unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) := by
    dsimp only [M]
    rw [unitizationScalarMatrix_reindex, hs₀, ← unitizationScalarMatrix_reindex]
    have hReferenceMatrix : CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e
        (q₀ : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) =
          pairedStandardFiniteReferenceMatrix (B := B) n := by
      simpa only [e, n, q₀, projectionBlockSum_coe, Projection.zero, Projection.one] using
        (finitePairedPrefixReindex_reference (B := B) (ι := ι))
    exact congrArg unitizationScalarMatrix hReferenceMatrix
  have hR : IsStarProjection R := juliaFredholmProjection_isStarProjection _
    (finiteProjectionAlignedFredholm_norm_le_one _ _ _ _)
  have hReference : juliaReferenceProjection (B := B) (E := Std) (F := Std) =
      standardCountablePairedReferenceProjection (B := B) := by
    apply AdjointableMap.ext
    intro x
    simp only [standardCountablePairedReferenceProjection, sumMap_apply,
      AdjointableMap.coe_zero_apply, AdjointableMap.one_apply, juliaReferenceProjection_apply]
  have hc : IsModuleCompact (R - standardCountablePairedReferenceProjection) := by
    simpa only [R, hReference] using
      (juliaFredholmProjection_difference_isModuleCompact (finiteAlignedUnitizationFredholm p q)
        (finiteProjectionAlignedFredholm_norm_le_one _ _ _ _) hs ht)
  have hNormalized : standardNormalizedFredholmJuliaProjection
      (finiteAlignedUnitizationFredholm p q) = R := by
    unfold standardNormalizedFredholmJuliaProjection
    rw [finiteAlignedUnitizationNormalization_fixed]
  suffices hIndex : standardCountableRelativeProjectionIndex R hR hc =
      unitizationRelativeProjectionK0 (p : CStarMatrix ι ι (Unitization ℂ B))
        (q : CStarMatrix ι ι (Unitization ℂ B)) p.property q.property hScalar by
    simpa only [standardNormalizedRectangularFredholmIndex, hNormalized] using hIndex
  rw [standardCountableRelativeProjectionIndex_prefix_matrix R hR hc n M hM hsM
    (finiteAlignedUnitizationJulia_difference_prefix p q)]
  apply operatorK0Inclusion_injective
  have hRef : pairedStandardFiniteReferenceMatrix (B := B) n =
      CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e (q₀ : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) :=
    finitePairedPrefixReindex_reference.symm
  change k0Projection (unitizationFiniteProjection M hM) -
      k0Projection (unitizationFiniteProjection (pairedStandardFiniteReferenceMatrix n) _) = _
  have hMclass : k0Projection (unitizationFiniteProjection M hM) =
      k0Projection (unitizationFiniteProjection
        (r : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) r.property) := by
    have hProjection : (⟨M, hM⟩ : MatrixProjection (Unitization ℂ B)
        (PairedStandardFiniteIndex (Fintype.card ι))) =
        Projection.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e).toStarAlgHom r := by
      apply Subtype.ext
      rfl
    simpa only [unitizationFiniteProjection] using
      ((congrArg (fun t : MatrixProjection (Unitization ℂ B)
          (PairedStandardFiniteIndex (Fintype.card ι)) =>
        k0Projection (FiniteProjection.ofProjection t)) hProjection).trans
          (unitizationFiniteProjection_k0_reindex (B := B) r e))
  have hQclass : k0Projection (unitizationFiniteProjection
      (pairedStandardFiniteReferenceMatrix (B := B) n)
      (pairedStandardFiniteReferenceMatrix_isStarProjection (B := B) n)) =
      k0Projection (unitizationFiniteProjection
        (q₀ : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) q₀.property) := by
    have hProjection :
        (⟨pairedStandardFiniteReferenceMatrix (B := B) n,
          pairedStandardFiniteReferenceMatrix_isStarProjection (B := B) n⟩ :
          MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n)) =
        Projection.map (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e).toStarAlgHom q₀ := by
      apply Subtype.ext
      exact hRef
    simpa only [unitizationFiniteProjection] using
      ((congrArg (fun t : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) =>
        k0Projection (FiniteProjection.ofProjection t)) hProjection).trans
          (unitizationFiniteProjection_k0_reindex (B := B) q₀ e))
  rw [hMclass, hQclass]
  exact finiteJuliaRecoveryProjection_k0 p q

end BC4lean.KKTheory
