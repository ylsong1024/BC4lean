import BC4lean.FiniteProjectionAlignedAbsorption
import BC4lean.AdjointableIsometricCornerHom
import BC4lean.UnitizationFiniteJuliaRecovery
import BC4lean.UnitizedFiniteMatrixBlocks
import BC4lean.GlobalFredholmNormalizationFixed

/-! # The whole actual Julia defect of an aligned finite projection pair

The source and target complement absorptions may differ. Their contribution
nevertheless cancels from the two Fredholm defects. Nonunital functional
calculus puts the actual defect root in the same finite prefix. The remaining
off-diagonal equations follow from the genuine projection-range cross maps.
-/

noncomputable section
open scoped CStarAlgebra
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open scoped Matrix

set_option synthInstance.maxSize 512

variable {B : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] [Fintype ι] [DecidableEq ι]

local notation "FinMod" => FiniteStandardModule B ι
local notation "Std" => StandardCountableHilbertModule B
local notation "FinEnd" => AdjointableMap B FinMod FinMod
local notation "StdEnd" => AdjointableMap B Std Std

local instance standardFiniteJuliaAlignedCornerLocalInstance01 : CompleteSpace FinMod := finiteStandardModule_complete
local instance standardFiniteJuliaAlignedCornerLocalInstance02 (A : Type*) [CStarAlgebra A] : PartialOrder A := CStarAlgebra.spectralOrder A
local instance standardFiniteJuliaAlignedCornerLocalInstance03 (A : Type*) [CStarAlgebra A] : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance standardFiniteJuliaAlignedCornerLocalInstance04 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

set_option maxHeartbeats 4000000 in
def finiteAlignedUnitizationFredholm (p q : MatrixProjection (Unitization ℂ B) ι) : StdEnd :=
  finiteProjectionAlignedFredholm (B := B) (ι := ι)
    (unitizedModuleMatrixRepresentation (B := B) (ι := ι)
      (p : CStarMatrix ι ι (Unitization ℂ B)))
    (unitizedModuleMatrixRepresentation (B := B) (ι := ι)
      (q : CStarMatrix ι ι (Unitization ℂ B)))
    (p.property.map (unitizedModuleMatrixRepresentation (B := B) (ι := ι)))
    (q.property.map (unitizedModuleMatrixRepresentation (B := B) (ι := ι)))

def finitePrefixUnitizationCornerHom : CStarMatrix ι ι (Unitization ℂ B) →⋆ₙₐ[ℂ] StdEnd :=
  (adjointableIsometricCornerHom (B := B) (E := FinMod) (F := Std)
    (finiteStandardPrefixInclusion (B := B) (ι := ι))
    (finiteStandardPrefixInclusion_adjoint_comp (B := B) (ι := ι))).comp
      (unitizedModuleMatrixRepresentation (B := B) (ι := ι))

theorem finiteAlignedUnitizationFredholm_source_defect (p q : MatrixProjection (Unitization ℂ B) ι) :
    1 - (finiteAlignedUnitizationFredholm p q).adjoint.comp (finiteAlignedUnitizationFredholm p q) =
      finitePrefixUnitizationCornerHom (finiteJuliaCompression p q) := by
  rw [finiteAlignedUnitizationFredholm, finiteProjectionAlignedFredholm_source_defect]
  change _ = (finiteStandardPrefixInclusion.comp
    (unitizedModuleMatrixRepresentation ((p : CStarMatrix ι ι (Unitization ℂ B)) - (p : CStarMatrix ι ι (Unitization ℂ B)) * (q : CStarMatrix ι ι (Unitization ℂ B)) * (p : CStarMatrix ι ι (Unitization ℂ B))))).comp
      finiteStandardPrefixInclusion.adjoint
  rw [map_sub, map_mul, map_mul]
  rfl

theorem finiteAlignedUnitizationFredholm_source_root (p q : MatrixProjection (Unitization ℂ B) ι) :
    juliaSourceDefect (finiteAlignedUnitizationFredholm p q) =
      finitePrefixUnitizationCornerHom (finiteJuliaCompressionRoot p q) := by
  let : NonUnitalContinuousFunctionalCalculus ℝ
      (CStarMatrix ι ι (Unitization ℂ B)) IsSelfAdjoint := by
    with_unfolding_all
      exact (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
        (A := CStarMatrix ι ι (Unitization ℂ B))).toNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι (Unitization ℂ B)) := by
    with_unfolding_all
      exact CStarAlgebra.instNonnegSpectrumClass' (A := CStarMatrix ι ι (Unitization ℂ B))
  rw [juliaSourceDefect, finiteAlignedUnitizationFredholm_source_defect]
  unfold finiteJuliaCompressionRoot CFC.sqrt
  have hφ : Continuous (finitePrefixUnitizationCornerHom (B := B) (ι := ι)) :=
    AddMonoidHomClass.continuous_of_bound (finitePrefixUnitizationCornerHom (B := B) (ι := ι)) 1
      (fun A => by
        simpa only [one_mul] using
          NonUnitalStarAlgHom.norm_apply_le (finitePrefixUnitizationCornerHom (B := B) (ι := ι)) A)
  exact (finitePrefixUnitizationCornerHom.map_cfcₙ (R := NNReal) NNReal.sqrt (finiteJuliaCompression p q)
    NNReal.continuous_sqrt.continuousOn NNReal.sqrt_zero hφ
    (finiteJuliaCompression_nonneg p q)
    (map_nonneg finitePrefixUnitizationCornerHom (finiteJuliaCompression_nonneg p q))).symm

theorem finiteAlignedUnitizationFredholm_root_square (p q : MatrixProjection (Unitization ℂ B) ι) :
    juliaSourceDefect (finiteAlignedUnitizationFredholm p q) *
      juliaSourceDefect (finiteAlignedUnitizationFredholm p q) =
        finitePrefixUnitizationCornerHom (finiteJuliaCompression p q) := by
  rw [finiteAlignedUnitizationFredholm_source_root, ← map_mul, finiteJuliaCompressionRoot_square]

theorem finiteAlignedUnitizationFredholm_target_defect (p q : MatrixProjection (Unitization ℂ B) ι) :
    (finiteAlignedUnitizationFredholm p q).comp (finiteAlignedUnitizationFredholm p q).adjoint - 1 =
      finitePrefixUnitizationCornerHom ((q : CStarMatrix ι ι (Unitization ℂ B)) * (p : CStarMatrix ι ι (Unitization ℂ B)) * (q : CStarMatrix ι ι (Unitization ℂ B)) - (q : CStarMatrix ι ι (Unitization ℂ B))) := by
  rw [finiteAlignedUnitizationFredholm, finiteProjectionAlignedFredholm_target_defect]
  change _ = (finiteStandardPrefixInclusion.comp
    (unitizedModuleMatrixRepresentation ((q : CStarMatrix ι ι (Unitization ℂ B)) * (p : CStarMatrix ι ι (Unitization ℂ B)) * (q : CStarMatrix ι ι (Unitization ℂ B)) - (q : CStarMatrix ι ι (Unitization ℂ B))))).comp
      finiteStandardPrefixInclusion.adjoint
  rw [map_sub, map_mul, map_mul]
  rfl

set_option maxRecDepth 2048 in
theorem finiteAlignedUnitizationFredholm_times_root (p q : MatrixProjection (Unitization ℂ B) ι) :
    (finiteAlignedUnitizationFredholm p q).comp (juliaSourceDefect (finiteAlignedUnitizationFredholm p q)) =
      finitePrefixUnitizationCornerHom
        ((q : CStarMatrix ι ι (Unitization ℂ B)) * (p : CStarMatrix ι ι (Unitization ℂ B)) * finiteJuliaCompressionRoot p q) := by
  let P : FinEnd := unitizedModuleMatrixRepresentation p
  let Q : FinEnd := unitizedModuleMatrixRepresentation q
  let S : FinEnd := unitizedModuleMatrixRepresentation (finiteJuliaCompressionRoot p q)
  have hPS : P.comp S = S := by
    change unitizedModuleMatrixRepresentation p * unitizedModuleMatrixRepresentation (finiteJuliaCompressionRoot p q) = _
    rw [← map_mul, finiteJuliaCompressionRoot_left_support]
  have hAction := finiteProjectionAlignedFredholm_comp_prefixProjection P Q
    (p.property.map unitizedModuleMatrixRepresentation) (q.property.map unitizedModuleMatrixRepresentation)
  rw [finiteAlignedUnitizationFredholm_source_root]
  ext x
  have ha := congrArg (fun T => T (S (finiteStandardPrefixInclusion.adjoint x))) hAction
  change finiteProjectionAlignedFredholm P Q
      (p.property.map unitizedModuleMatrixRepresentation) (q.property.map unitizedModuleMatrixRepresentation)
        (finiteStandardPrefixInclusion (S (finiteStandardPrefixInclusion.adjoint x))) =
    finiteStandardPrefixInclusion (unitizedModuleMatrixRepresentation
      ((q : CStarMatrix ι ι (Unitization ℂ B)) * (p : CStarMatrix ι ι (Unitization ℂ B)) * finiteJuliaCompressionRoot p q)
        (finiteStandardPrefixInclusion.adjoint x))
  have hpv (z : FinMod) : P (S z) = S z := congrArg (fun T => T z) hPS
  simp only [AdjointableMap.comp_apply, hpv] at ha
  rw [map_mul, map_mul]
  change finiteProjectionAlignedFredholm P Q
      (p.property.map unitizedModuleMatrixRepresentation) (q.property.map unitizedModuleMatrixRepresentation)
        (finiteStandardPrefixInclusion (S (finiteStandardPrefixInclusion.adjoint x))) =
    finiteStandardPrefixInclusion (Q (P (S (finiteStandardPrefixInclusion.adjoint x))))
  rw [hpv]
  exact ha

theorem finiteAlignedUnitizationFredholm_root_times_adjoint (p q : MatrixProjection (Unitization ℂ B) ι) :
    (juliaSourceDefect (finiteAlignedUnitizationFredholm p q)).comp (finiteAlignedUnitizationFredholm p q).adjoint =
      finitePrefixUnitizationCornerHom
        (finiteJuliaCompressionRoot p q * (p : CStarMatrix ι ι (Unitization ℂ B)) * (q : CStarMatrix ι ι (Unitization ℂ B))) := by
  have h := congrArg AdjointableMap.adjoint (finiteAlignedUnitizationFredholm_times_root p q)
  rw [AdjointableMap.adjoint_comp, juliaSourceDefect_adjoint] at h
  simpa only [← AdjointableMap.star_eq_adjoint, ← map_star, star_mul, Projection.star_coe,
    finiteJuliaCompressionRoot_star, mul_assoc] using h

def finitePairedPrefixInclusion : AdjointableMap B (HilbertModuleSum B FinMod FinMod)
    (HilbertModuleSum B Std Std) :=
  sumMap (B := B) (E := FinMod) (F := FinMod) (G := Std) (H := Std)
    (finiteStandardPrefixInclusion (B := B) (ι := ι))
    (finiteStandardPrefixInclusion (B := B) (ι := ι))

omit [TopologicalSpace.SeparableSpace B] [DecidableEq ι] in
theorem finitePairedPrefixInclusion_adjoint_comp :
    (finitePairedPrefixInclusion (B := B) (ι := ι)).adjoint.comp finitePairedPrefixInclusion =
      AdjointableMap.id := by
  have hJ := finiteStandardPrefixInclusion_adjoint_comp (B := B) (ι := ι)
  apply AdjointableMap.ext
  intro x
  simp only [finitePairedPrefixInclusion, sumMap_adjoint, AdjointableMap.comp_apply,
    sumMap_apply, AdjointableMap.id_apply]
  apply Prod.ext
  · exact congrArg (fun R : FinEnd => R x.fst) hJ
  · exact congrArg (fun R : FinEnd => R x.snd) hJ

omit [TopologicalSpace.SeparableSpace B] [DecidableEq ι] in
theorem finitePairedPrefixInclusion_fourBlocks (A D S T : FinEnd) :
    ((finitePairedPrefixInclusion (B := B) (ι := ι)).comp (finiteModuleFourBlockOperator A D S T)).comp
      finitePairedPrefixInclusion.adjoint =
    sumMap ((finiteStandardPrefixInclusion.comp A).comp finiteStandardPrefixInclusion.adjoint)
      ((finiteStandardPrefixInclusion.comp D).comp finiteStandardPrefixInclusion.adjoint) +
      (sumInl.comp ((finiteStandardPrefixInclusion.comp S).comp finiteStandardPrefixInclusion.adjoint)).comp sumSnd +
      (sumInr.comp ((finiteStandardPrefixInclusion.comp T).comp finiteStandardPrefixInclusion.adjoint)).comp sumFst := by
  apply AdjointableMap.ext
  intro x
  simp only [finitePairedPrefixInclusion, sumMap_adjoint, AdjointableMap.comp_apply,
    finiteModuleFourBlockOperator_apply, sumMap_apply, AdjointableMap.coe_add_apply,
    sumInl_apply, sumInr_apply, sumSnd_apply, sumFst_apply, sumMk_fst, sumMk_snd]
  apply Prod.ext
  · simp only [sumMk_fst, WithCStarModule.add_fst,
      (finiteStandardPrefixInclusion (B := B) (ι := ι)).toCLM.map_add, add_zero]
  · simp only [sumMk_snd, WithCStarModule.add_snd,
      (finiteStandardPrefixInclusion (B := B) (ι := ι)).toCLM.map_add, add_zero]
    exact add_comm _ _

theorem finiteAlignedUnitizationJulia_difference (p q : MatrixProjection (Unitization ℂ B) ι) :
    juliaFredholmProjection (finiteAlignedUnitizationFredholm p q) - juliaReferenceProjection =
      (finitePairedPrefixInclusion.comp
        (finiteModuleFourBlockOperator (unitizedModuleMatrixRepresentation (finiteJuliaCompression p q))
          (unitizedModuleMatrixRepresentation ((q : CStarMatrix ι ι (Unitization ℂ B)) * (p : CStarMatrix ι ι (Unitization ℂ B)) * (q : CStarMatrix ι ι (Unitization ℂ B)) - (q : CStarMatrix ι ι (Unitization ℂ B))))
          (unitizedModuleMatrixRepresentation (finiteJuliaCompressionRoot p q * (p : CStarMatrix ι ι (Unitization ℂ B)) * (q : CStarMatrix ι ι (Unitization ℂ B))))
          (unitizedModuleMatrixRepresentation ((q : CStarMatrix ι ι (Unitization ℂ B)) * (p : CStarMatrix ι ι (Unitization ℂ B)) * finiteJuliaCompressionRoot p q)))).comp
            finitePairedPrefixInclusion.adjoint := by
  rw [juliaFredholmProjection_difference, finiteAlignedUnitizationFredholm_root_square,
    finiteAlignedUnitizationFredholm_target_defect, finiteAlignedUnitizationFredholm_root_times_adjoint,
    finiteAlignedUnitizationFredholm_times_root, finitePairedPrefixInclusion_fourBlocks]
  rfl

theorem finiteAlignedUnitizationNormalization_fixed (p q : MatrixProjection (Unitization ℂ B) ι) :
    globalFredholmNormalization (finiteAlignedUnitizationFredholm p q) = finiteAlignedUnitizationFredholm p q :=
  globalFredholmNormalization_eq_of_contractive _ (finiteProjectionAlignedFredholm_norm_le_one _ _ _ _)

/-- The actual whole Julia defect is the corner of the recovered finite matrix. -/
theorem finiteAlignedUnitizationJulia_difference_matrix
    (p q : MatrixProjection (Unitization ℂ B) ι) :
    juliaFredholmProjection (finiteAlignedUnitizationFredholm p q) - juliaReferenceProjection =
      (finitePairedPrefixInclusion.comp
        ((oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := ι)).transport
          (unitizedModuleMatrixRepresentation
            ((finiteJuliaRecoveryProjection p q :
              CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) -
                matrixBlockSum (0 : CStarMatrix ι ι (Unitization ℂ B)) 1)))).comp
                  finitePairedPrefixInclusion.adjoint := by
  rw [finiteJuliaRecoveryProjection_difference_fourBlocks,
    unitizedModuleMatrixRepresentation_fourBlocks]
  exact finiteAlignedUnitizationJulia_difference p q

end BC4lean.KKTheory
