import BC4lean.GradedHilbertModuleHomogeneousSplit
import BC4lean.RelativeProjectionKasparovCycle

/-! # The actual homogeneous modules of the canonical graded direct sum

The two coordinate inclusions, with their actual adjoints, identify the
homogeneous closed ranges with the original summands and recover the whole
rectangular block of the off-diagonal operator.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

local notation "γ" => (GradedHilbertModule.trivial.sum GradedHilbertModule.trivial.opposite :
  GradedHilbertModule (CStarGrading.trivial : CStarGrading B) (HilbertModuleSum B E F))

theorem canonicalGradedSum_evenProjection : (γ).evenProjection =
    sumMap (1 : AdjointableMap B E E) (0 : AdjointableMap B F F) := by
  ext x
  simp only [GradedHilbertModule.evenProjection_apply, GradedHilbertModule.evenPart,
    GradedHilbertModule.sum_grading_apply, GradedHilbertModule.opposite_grading_apply,
    sumMap_apply, AdjointableMap.one_apply, AdjointableMap.coe_zero_apply]
  apply Prod.ext
  · change (2 : ℂ)⁻¹ • (x.fst + x.fst) = x.fst
    rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  · change (2 : ℂ)⁻¹ • (x.snd + -x.snd) = 0
    rw [add_neg_cancel, smul_zero]

theorem canonicalGradedSum_oddProjection : (γ).oddProjection =
    sumMap (0 : AdjointableMap B E E) (1 : AdjointableMap B F F) := by
  rw [GradedHilbertModule.oddProjection, canonicalGradedSum_evenProjection]
  ext x
  simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    sumMap_apply, AdjointableMap.coe_zero_apply]
  apply Prod.ext <;> simp only [WithCStarModule.sub_fst, WithCStarModule.sub_snd,
    sumMk_fst, sumMk_snd, sub_self, sub_zero]

omit [StarOrderedRing B] in
def canonicalProjectionOneEquiv : HilbertModuleEquiv B E
    (ProjectionModule (1 : AdjointableMap B E E)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := ⟨x, rfl⟩
          invFun x := (x : E)
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      norm_map' _ := rfl }
  inner_map _ _ := rfl

def canonicalGradedSumEvenEmbeddingEquiv : HilbertModuleEquiv B E (γ).EvenModule :=
  canonicalProjectionOneEquiv.trans
    (projectionRangeEquiv 1 (γ).evenProjection (sumInl (B := B) (E := E) (F := F))
      (by ext x; rfl) (by
        rw [canonicalGradedSum_evenProjection, sumInl_adjoint]
        ext x
        simp only [AdjointableMap.comp_apply, sumFst_apply, sumInl_apply,
          sumMap_apply, AdjointableMap.one_apply, AdjointableMap.coe_zero_apply]))

def canonicalGradedSumOddEmbeddingEquiv : HilbertModuleEquiv B F (γ).OddModule :=
  canonicalProjectionOneEquiv.trans
    (projectionRangeEquiv 1 (γ).oddProjection (sumInr (B := B) (E := E) (F := F))
      (by ext x; rfl) (by
        rw [canonicalGradedSum_oddProjection, sumInr_adjoint]
        ext x
        simp only [AdjointableMap.comp_apply, sumSnd_apply, sumInr_apply,
          sumMap_apply, AdjointableMap.one_apply, AdjointableMap.coe_zero_apply]))

@[simp] theorem canonicalGradedSumEvenEmbeddingEquiv_coe (x : E) :
    (canonicalGradedSumEvenEmbeddingEquiv (B := B) (F := F) x : HilbertModuleSum B E F) =
      sumMk x 0 := rfl

@[simp] theorem canonicalGradedSumOddEmbeddingEquiv_coe (x : F) :
    (canonicalGradedSumOddEmbeddingEquiv (B := B) (E := E) x : HilbertModuleSum B E F) =
      sumMk 0 x := rfl

@[simp] theorem canonicalGradedSumEvenEmbeddingEquiv_symm (x : (γ).EvenModule) :
    (canonicalGradedSumEvenEmbeddingEquiv (B := B) (E := E) (F := F)).symm x =
      (x : HilbertModuleSum B E F).fst := rfl

@[simp] theorem canonicalGradedSumOddEmbeddingEquiv_symm (x : (γ).OddModule) :
    (canonicalGradedSumOddEmbeddingEquiv (B := B) (E := E) (F := F)).symm x =
      (x : HilbertModuleSum B E F).snd := rfl

theorem canonicalGradedSum_homogeneousOddMap (T : AdjointableMap B E F) :
    (canonicalGradedSumEvenEmbeddingEquiv (B := B) (E := E) (F := F)).symm.transportMap
      (canonicalGradedSumOddEmbeddingEquiv (B := B) (E := E) (F := F)).symm
      ((γ).homogeneousOddMap (offDiagonalAdjointable T)) = T := by
  ext x
  simp only [HilbertModuleEquiv.transportMap_apply, HilbertModuleEquiv.symm_symm,
    canonicalGradedSumOddEmbeddingEquiv_symm]
  rw [(γ).homogeneousOddMap_coe _ (offDiagonalAdjointable_odd T),
    canonicalGradedSumEvenEmbeddingEquiv_coe]
  simp only [offDiagonalAdjointable_apply, sumMk_fst, sumMk_snd]

end BC4lean.KKTheory
