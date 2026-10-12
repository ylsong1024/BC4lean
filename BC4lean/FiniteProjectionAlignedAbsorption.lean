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
  ((oddKTheoryFiniteReindexEquiv (Fintype.equivFin ι)).sum
    (HilbertModuleEquiv.refl (B := B) (E := Std))).trans
      (oddKTheoryStandardPrefixEquiv (Fintype.card ι))

def finiteStandardPrefixInclusion : AdjointableMap B FinMod Std :=
  finiteStandardPrefixEquiv.toAdjointable.comp (sumInl (B := B) (E := FinMod) (F := Std))

@[simp] theorem finiteStandardPrefixInclusion_apply (x : FinMod) :
    finiteStandardPrefixInclusion x = oddFredholmStandardFiniteInclusion (Fintype.card ι)
      (oddKTheoryFiniteReindexEquiv (Fintype.equivFin ι) x) := by
  change oddKTheoryStandardPrefixEquiv (Fintype.card ι)
    (sumMk (oddKTheoryFiniteReindexEquiv (Fintype.equivFin ι) x) 0) = _
  exact oddKTheoryStandardPrefixEquiv_inl _ _

theorem finiteStandardPrefixInclusion_adjoint_comp :
    (finiteStandardPrefixInclusion (B := B) (ι := ι)).adjoint.comp
      finiteStandardPrefixInclusion = AdjointableMap.id := by
  ext x
  change ((finiteStandardPrefixEquiv (B := B) (ι := ι)).symm
    (finiteStandardPrefixEquiv (sumMk x 0))).fst = x
  rw [HilbertModuleEquiv.symm_apply_apply]
  rfl

def finiteProjectionAlignedAbsorption (P : AdjointableMap B FinMod FinMod)
    (hP : IsStarProjection P) : HilbertModuleEquiv B
    (HilbertModuleSum B (ProjectionModule P) Std) Std :=
  (projectionModuleAlignedStabilization P hP
    finiteStandardModule_isCountablyGenerated_nonunital).trans finiteStandardPrefixEquiv

@[simp] theorem finiteProjectionAlignedAbsorption_inl
    (P : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (x : ProjectionModule P) :
    finiteProjectionAlignedAbsorption P hP (sumMk x 0) = finiteStandardPrefixInclusion (x : FinMod) := by
  change finiteStandardPrefixEquiv
    (projectionModuleAlignedStabilization P hP
      finiteStandardModule_isCountablyGenerated_nonunital (sumMk x 0)) = _
  rw [projectionModuleAlignedStabilization_inl]
  rfl

def finiteProjectionAlignedFredholm (P Q : AdjointableMap B FinMod FinMod)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : AdjointableMap B Std Std :=
  (finiteProjectionAlignedAbsorption P hP).transportMap
    (finiteProjectionAlignedAbsorption Q hQ)
      (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ))

theorem finiteProjectionAlignedFredholm_on_range
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (x : ProjectionModule P) :
    finiteProjectionAlignedFredholm P Q hP hQ (finiteStandardPrefixInclusion (x : FinMod)) =
      finiteStandardPrefixInclusion (Q (x : FinMod)) := by
  rw [← finiteProjectionAlignedAbsorption_inl P hP x]
  change finiteProjectionAlignedAbsorption Q hQ
    (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)
      ((finiteProjectionAlignedAbsorption P hP).symm
        (finiteProjectionAlignedAbsorption P hP (sumMk x 0)))) = _
  rw [HilbertModuleEquiv.symm_apply_apply]
  change finiteProjectionAlignedAbsorption Q hQ
    (sumMk (projectionCrossMap P Q hP hQ x) 0) = _
  rw [finiteProjectionAlignedAbsorption_inl]
  rfl

theorem finiteProjectionAlignedFredholm_comp_prefixProjection
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (finiteProjectionAlignedFredholm P Q hP hQ).comp (finiteStandardPrefixInclusion.comp P) =
      (finiteStandardPrefixInclusion.comp Q).comp P := by
  ext x
  exact finiteProjectionAlignedFredholm_on_range P Q hP hQ (projectionCorestrict P hP x)

@[simp] theorem finiteProjectionAlignedFredholm_adjoint
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (finiteProjectionAlignedFredholm P Q hP hQ).adjoint =
      finiteProjectionAlignedFredholm Q P hQ hP := by
  rw [finiteProjectionAlignedFredholm, HilbertModuleEquiv.transportMap_adjoint]
  congr 1
  rw [augmentedRectangularFredholm, sumMap_adjoint, projectionCrossMap_adjoint]
  rfl

theorem finiteProjectionAlignedFredholm_norm_le_one
    (P Q : AdjointableMap B FinMod FinMod) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖finiteProjectionAlignedFredholm P Q hP hQ‖ ≤ 1 := by
  rw [finiteProjectionAlignedFredholm, HilbertModuleEquiv.transportMap_norm]
  exact augmentedRectangularFredholm_norm_le_one _ (projectionCrossMap_norm_le_one P Q hP hQ)

theorem finiteStandardPrefixEquiv_transport_corner (A : AdjointableMap B FinMod FinMod) :
    (finiteStandardPrefixEquiv (B := B) (ι := ι)).transport
      (sumMap A (0 : AdjointableMap B Std Std)) =
        (finiteStandardPrefixInclusion.comp A).comp finiteStandardPrefixInclusion.adjoint := by
  ext x
  rfl

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
