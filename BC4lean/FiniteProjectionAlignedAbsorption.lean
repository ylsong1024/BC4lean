import BC4lean.ProjectionModuleAlignedStabilization
import BC4lean.OddKTheoryStandardPrefixEquiv
import BC4lean.OddKTheoryFiniteCoordinateEquiv
import BC4lean.FiniteModuleCountableGeneration
import BC4lean.RectangularFredholmNormalizationNaturality
import BC4lean.RectangularFredholmContraction

/-! # Projective absorption aligned with an actual finite standard prefix

Each projective range has its own complement absorption. The actual included
finite free vector nevertheless occupies the same standard prefix for both
ranges. No complement unitary is required to have finite support.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] [Fintype ι] [DecidableEq ι]

local notation "FinMod" => FiniteStandardModule B ι
local notation "Std" => StandardCountableHilbertModule B

local instance standardFiniteProjectionAlignedAbsorptionLocalInstance01 : CompleteSpace FinMod := finiteStandardModule_complete
local instance standardFiniteProjectionAlignedAbsorptionLocalInstance02 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

def finiteStandardPrefixEquiv : HilbertModuleEquiv B (HilbertModuleSum B FinMod Std) Std :=
  HilbertModuleEquiv.trans (B := B)
    (E := HilbertModuleSum B FinMod Std)
    (F := HilbertModuleSum B (FiniteStandardModule B (Fin (Fintype.card ι))) Std)
    (G := Std)
    (HilbertModuleEquiv.sum (B := B) (E := FinMod) (F := Std)
      (G := FiniteStandardModule B (Fin (Fintype.card ι))) (H := Std)
      (oddKTheoryFiniteReindexEquiv (B := B) (ι := ι) (κ := Fin (Fintype.card ι))
        (Fintype.equivFin ι))
      (HilbertModuleEquiv.refl (B := B) (E := Std)))
    (oddKTheoryStandardPrefixEquiv (B := B) (Fintype.card ι))

def finiteStandardPrefixInclusion : AdjointableMap B FinMod Std :=
  (finiteStandardPrefixEquiv (B := B) (ι := ι)).toAdjointable.comp
    (sumInl (B := B) (E := FinMod) (F := Std))

omit [TopologicalSpace.SeparableSpace B] [DecidableEq ι] in
@[simp] theorem finiteStandardPrefixInclusion_apply (x : FinMod) :
    finiteStandardPrefixInclusion x = oddFredholmStandardFiniteInclusion (Fintype.card ι)
      (oddKTheoryFiniteReindexEquiv (Fintype.equivFin ι) x) := by
  change oddKTheoryStandardPrefixEquiv (B := B) (Fintype.card ι)
    (sumMk (B := B)
      (oddKTheoryFiniteReindexEquiv (B := B) (ι := ι) (κ := Fin (Fintype.card ι))
        (Fintype.equivFin ι) x) (0 : Std)) = _
  exact oddKTheoryStandardPrefixEquiv_inl (B := B) (Fintype.card ι) _

omit [TopologicalSpace.SeparableSpace B] [DecidableEq ι] in
theorem finiteStandardPrefixInclusion_adjoint_comp :
    (finiteStandardPrefixInclusion (B := B) (ι := ι)).adjoint.comp
      finiteStandardPrefixInclusion = AdjointableMap.id := by
  apply AdjointableMap.ext
  intro x
  change ((finiteStandardPrefixEquiv (B := B) (ι := ι)).symm
    (finiteStandardPrefixEquiv (B := B) (ι := ι) (sumMk (B := B) x (0 : Std)))).fst = x
  exact congrArg (fun y : HilbertModuleSum B FinMod Std => y.fst)
    (HilbertModuleEquiv.symm_apply_apply (finiteStandardPrefixEquiv (B := B) (ι := ι))
      (sumMk (B := B) x (0 : Std)))

def finiteProjectionAlignedAbsorption (P : AdjointableMap B FinMod FinMod)
    (hP : IsStarProjection P) : HilbertModuleEquiv B
    (HilbertModuleSum B (ProjectionModule P) Std) Std :=
  HilbertModuleEquiv.trans (B := B)
    (E := HilbertModuleSum B (ProjectionModule P) Std)
    (F := HilbertModuleSum B FinMod Std) (G := Std)
    (projectionModuleAlignedStabilization (B := B) (E := FinMod) P hP
      (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι)))
    (finiteStandardPrefixEquiv (B := B) (ι := ι))

@[simp] theorem finiteProjectionAlignedAbsorption_inl
    (P : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (x : ProjectionModule P) :
    finiteProjectionAlignedAbsorption P hP (sumMk x 0) = finiteStandardPrefixInclusion (x : FinMod) := by
  change finiteStandardPrefixEquiv (B := B) (ι := ι)
    (projectionModuleAlignedStabilization (B := B) (E := FinMod) P hP
      (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι))
      (sumMk (B := B) x (0 : Std))) =
    finiteStandardPrefixEquiv (B := B) (ι := ι) (sumMk (B := B) (x : FinMod) (0 : Std))
  exact congrArg (finiteStandardPrefixEquiv (B := B) (ι := ι))
    (projectionModuleAlignedStabilization_inl (B := B) (E := FinMod) P hP
      (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι)) x)

def finiteProjectionAlignedFredholm (P Q : AdjointableMap B FinMod FinMod)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : AdjointableMap B Std Std :=
  HilbertModuleEquiv.transportMap (B := B)
    (E := HilbertModuleSum B (ProjectionModule P) Std) (F := Std)
    (G := HilbertModuleSum B (ProjectionModule Q) Std) (H := Std)
    (finiteProjectionAlignedAbsorption (B := B) (ι := ι) P hP)
    (finiteProjectionAlignedAbsorption (B := B) (ι := ι) Q hQ)
    (augmentedRectangularFredholm (B := B) (E := ProjectionModule P) (F := ProjectionModule Q)
      (projectionCrossMap (B := B) (E := FinMod) P Q hP hQ))

theorem finiteProjectionAlignedFredholm_on_range
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (x : ProjectionModule P) :
    finiteProjectionAlignedFredholm P Q hP hQ (finiteStandardPrefixInclusion (x : FinMod)) =
      finiteStandardPrefixInclusion (Q (x : FinMod)) := by
  rw [← finiteProjectionAlignedAbsorption_inl (B := B) (ι := ι) P hP x]
  change finiteProjectionAlignedAbsorption (B := B) (ι := ι) Q hQ
    (augmentedRectangularFredholm (B := B) (E := ProjectionModule P) (F := ProjectionModule Q)
      (projectionCrossMap (B := B) (E := FinMod) P Q hP hQ)
      ((finiteProjectionAlignedAbsorption (B := B) (ι := ι) P hP).symm
        (finiteProjectionAlignedAbsorption (B := B) (ι := ι) P hP
          (sumMk (B := B) x (0 : Std))))) = _
  rw [HilbertModuleEquiv.symm_apply_apply]
  simp only [augmentedRectangularFredholm, sumMap_apply, sumMk_fst, sumMk_snd,
    AdjointableMap.one_apply, finiteProjectionAlignedAbsorption_inl, projectionCrossMap_coe]

set_option maxRecDepth 2048 in
theorem finiteProjectionAlignedFredholm_comp_prefixProjection
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (finiteProjectionAlignedFredholm P Q hP hQ).comp (finiteStandardPrefixInclusion.comp P) =
      (finiteStandardPrefixInclusion.comp Q).comp P := by
  apply AdjointableMap.ext
  intro x
  simp only [AdjointableMap.comp_apply]
  let y : ProjectionModule P := projectionCorestrict (B := B) (E := FinMod) P hP x
  have hy : (y : FinMod) = P x := projectionCorestrict_coe (B := B) (E := FinMod) P hP x
  have h : finiteProjectionAlignedFredholm (B := B) (ι := ι) P Q hP hQ
      (finiteStandardPrefixInclusion (B := B) (ι := ι) (y : FinMod)) =
    finiteStandardPrefixInclusion (B := B) (ι := ι) (Q (y : FinMod)) :=
    finiteProjectionAlignedFredholm_on_range (B := B) (ι := ι) P Q hP hQ y
  rw [hy] at h
  exact h

@[simp] theorem finiteProjectionAlignedFredholm_adjoint
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (finiteProjectionAlignedFredholm P Q hP hQ).adjoint =
      finiteProjectionAlignedFredholm Q P hQ hP := by
  have hOne : (1 : AdjointableMap B Std Std).adjoint = 1 :=
    AdjointableMap.adjoint_id (B := B) (E := Std)
  simp only [finiteProjectionAlignedFredholm, HilbertModuleEquiv.transportMap_adjoint,
    augmentedRectangularFredholm, sumMap_adjoint, projectionCrossMap_adjoint, hOne]

theorem finiteProjectionAlignedFredholm_norm_le_one
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖finiteProjectionAlignedFredholm P Q hP hQ‖ ≤ 1 := by
  rw [finiteProjectionAlignedFredholm, HilbertModuleEquiv.transportMap_norm]
  exact augmentedRectangularFredholm_norm_le_one _ (projectionCrossMap_norm_le_one P Q hP hQ)

omit [TopologicalSpace.SeparableSpace B] [DecidableEq ι] in
theorem finiteStandardPrefixEquiv_transport_corner (A : AdjointableMap B FinMod FinMod) :
    (finiteStandardPrefixEquiv (B := B) (ι := ι)).transport
      (sumMap A (0 : AdjointableMap B Std Std)) =
        (finiteStandardPrefixInclusion.comp A).comp finiteStandardPrefixInclusion.adjoint := by
  apply AdjointableMap.ext
  intro x
  change finiteStandardPrefixEquiv (B := B) (ι := ι)
      (sumMap A (0 : AdjointableMap B Std Std)
        ((finiteStandardPrefixEquiv (B := B) (ι := ι)).symm x)) =
    finiteStandardPrefixEquiv (B := B) (ι := ι)
      (sumMk (B := B) (A (((finiteStandardPrefixEquiv (B := B) (ι := ι)).symm x).fst))
        (0 : Std))
  rw [sumMap_apply, AdjointableMap.coe_zero_apply]

theorem finiteProjectionAlignedFredholm_source_defect
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    1 - (finiteProjectionAlignedFredholm P Q hP hQ).adjoint.comp
      (finiteProjectionAlignedFredholm P Q hP hQ) =
        (finiteStandardPrefixInclusion.comp (P - (P.comp Q).comp P)).comp
          finiteStandardPrefixInclusion.adjoint := by
  have hsq : 1 - (finiteProjectionAlignedFredholm P Q hP hQ).adjoint.comp
      (finiteProjectionAlignedFredholm P Q hP hQ) =
      (finiteProjectionAlignedAbsorption P hP).transport
        (1 - (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).adjoint.comp
          (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ))) := by
    rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
      ← HilbertModuleEquiv.transportMap_source_square
        (finiteProjectionAlignedAbsorption P hP) (finiteProjectionAlignedAbsorption Q hQ)
        (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ))]
    rfl
  rw [hsq]
  have ht (A : AdjointableMap B (HilbertModuleSum B (ProjectionModule P) Std)
      (HilbertModuleSum B (ProjectionModule P) Std)) :
      (finiteProjectionAlignedAbsorption P hP).transport A =
        finiteStandardPrefixEquiv.transport
          ((projectionModuleAlignedStabilization P hP
            finiteStandardModule_isCountablyGenerated_nonunital).transport A) := by
    ext x
    rfl
  rw [ht, projectionModuleAlignedStabilization_source_defect,
    finiteStandardPrefixEquiv_transport_corner]

theorem finiteProjectionAlignedFredholm_target_defect
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (finiteProjectionAlignedFredholm P Q hP hQ).comp
      (finiteProjectionAlignedFredholm P Q hP hQ).adjoint - 1 =
        (finiteStandardPrefixInclusion.comp ((Q.comp P).comp Q - Q)).comp
          finiteStandardPrefixInclusion.adjoint := by
  have hsq : (finiteProjectionAlignedFredholm P Q hP hQ).comp
      (finiteProjectionAlignedFredholm P Q hP hQ).adjoint - 1 =
      (finiteProjectionAlignedAbsorption Q hQ).transport
        ((augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).comp
          (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).adjoint - 1) := by
    rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
      ← HilbertModuleEquiv.transportMap_target_square
        (finiteProjectionAlignedAbsorption P hP) (finiteProjectionAlignedAbsorption Q hQ)
        (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ))]
    rfl
  rw [hsq]
  have ht (A : AdjointableMap B (HilbertModuleSum B (ProjectionModule Q) Std)
      (HilbertModuleSum B (ProjectionModule Q) Std)) :
      (finiteProjectionAlignedAbsorption Q hQ).transport A =
        finiteStandardPrefixEquiv.transport
          ((projectionModuleAlignedStabilization Q hQ
            finiteStandardModule_isCountablyGenerated_nonunital).transport A) := by
    ext x
    rfl
  rw [ht, projectionModuleAlignedStabilization_target_defect,
    finiteStandardPrefixEquiv_transport_corner]

end BC4lean.KKTheory
