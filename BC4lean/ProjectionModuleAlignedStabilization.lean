import BC4lean.ProjectionHilbertModuleSplit
import BC4lean.StandardModuleStabilization
import BC4lean.RelativeProjectionKasparovCycle
import BC4lean.RectangularFredholmStandardStabilization

/-! # Absorbing a projection range while retaining its actual ambient inclusion

The orthogonal complement is absorbed with the standard module. The projection
range itself remains the original included submodule, rather than being treated
as a free module or as a module with compact identity.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local notation "Std" => StandardCountableHilbertModule B

local instance standardProjectionModuleAlignedStabilizationLocalInstance01 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

def projectionModuleAlignedStabilization
    (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (hE : IsCountablyGeneratedModule B E) :
    HilbertModuleEquiv B (HilbertModuleSum B (ProjectionModule P) Std)
      (HilbertModuleSum B E Std) :=
  (((HilbertModuleEquiv.refl (B := B) (E := ProjectionModule P)).sum
    (standardModuleStabilization
      (projectionModule_isCountablyGenerated (1 - P) hP.one_sub hE)).symm).trans
        HilbertModuleEquiv.sumAssocEquiv.symm).trans
          ((projectionModuleSplitEquiv P hP).symm.sum
            (HilbertModuleEquiv.refl (B := B) (E := Std)))

@[simp] theorem projectionModuleAlignedStabilization_inl
    (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (hE : IsCountablyGeneratedModule B E) (x : ProjectionModule P) :
    projectionModuleAlignedStabilization P hP hE (sumMk x 0) = sumMk (x : E) 0 := by
  change sumMk ((x : E) +
    ((standardModuleStabilization
      (projectionModule_isCountablyGenerated (1 - P) hP.one_sub hE)).symm (0 : Std)).fst)
    ((standardModuleStabilization
      (projectionModule_isCountablyGenerated (1 - P) hP.one_sub hE)).symm (0 : Std)).snd = _
  rw [HilbertModuleEquiv.map_zero]
  simp only [WithCStarModule.zero_fst, WithCStarModule.zero_snd,
    ZeroMemClass.coe_zero, add_zero]

theorem projectionModuleAlignedStabilization_first
    (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (hE : IsCountablyGeneratedModule B E)
    (x : HilbertModuleSum B (ProjectionModule P) Std) :
    P (projectionModuleAlignedStabilization P hP hE x).fst = (x.fst : E) := by
  change P ((x.fst : E) +
    ((standardModuleStabilization
      (projectionModule_isCountablyGenerated (1 - P) hP.one_sub hE)).symm x.snd).fst) = _
  rw [P.toCLM.map_add, x.fst.property, projection_complement_fixed_eq_zero, add_zero]

theorem projectionModuleAlignedStabilization_symm_first
    (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (hE : IsCountablyGeneratedModule B E) (x : HilbertModuleSum B E Std) :
    (((projectionModuleAlignedStabilization P hP hE).symm x).fst : E) = P x.fst := by
  have h := projectionModuleAlignedStabilization_first P hP hE
    ((projectionModuleAlignedStabilization P hP hE).symm x)
  rw [HilbertModuleEquiv.apply_symm_apply] at h
  exact h.symm

/-- The source defect is precisely the original finite ambient compression.
The independent complement absorptions cancel from this identity. -/
theorem projectionModuleAlignedStabilization_source_defect
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hE : IsCountablyGeneratedModule B E) :
    (projectionModuleAlignedStabilization P hP hE).transport
      (1 - (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).adjoint.comp
        (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ))) =
      sumMap (P - (P.comp Q).comp P) (0 : AdjointableMap B Std Std) := by
  apply AdjointableMap.ext
  intro x
  have hOne : (1 : AdjointableMap B Std Std).adjoint = 1 := rfl
  let y := (projectionModuleAlignedStabilization P hP hE).symm x
  have hy := projectionModuleAlignedStabilization_symm_first P hP hE x
  have hz : (1 - (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).adjoint.comp
      (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ))) y =
      sumMk (y.fst - (projectionCrossMap Q P hQ hP) (projectionCrossMap P Q hP hQ y.fst)) 0 := by
    apply Prod.ext <;> simp only [augmentedRectangularFredholm, sumMap_adjoint,
      projectionCrossMap_adjoint, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.one_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.sub_fst, WithCStarModule.sub_snd, hOne, sub_self]
  change projectionModuleAlignedStabilization P hP hE
    ((1 - (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).adjoint.comp
      (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ))) y) = _
  rw [hz, projectionModuleAlignedStabilization_inl]
  simp only [sumMap_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.comp_apply, AdjointableMap.coe_zero_apply]
  apply Prod.ext
  · simp only [sumMk_fst, Submodule.coe_sub, projectionCrossMap_coe]
    rw [hy]
  · simp only [sumMk_snd]

/-- The target defect has the corresponding original ambient compression. -/
theorem projectionModuleAlignedStabilization_target_defect
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hE : IsCountablyGeneratedModule B E) :
    (projectionModuleAlignedStabilization Q hQ hE).transport
      ((augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).comp
        (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).adjoint - 1) =
      sumMap ((Q.comp P).comp Q - Q) (0 : AdjointableMap B Std Std) := by
  have h := projectionModuleAlignedStabilization_source_defect Q P hQ hP hE
  have ha : augmentedRectangularFredholm (projectionCrossMap Q P hQ hP) =
      (augmentedRectangularFredholm (projectionCrossMap P Q hP hQ)).adjoint := by
    rw [augmentedRectangularFredholm, augmentedRectangularFredholm, sumMap_adjoint,
      projectionCrossMap_adjoint]
    rfl
  rw [ha, AdjointableMap.adjoint_adjoint] at h
  rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one] at h ⊢
  have hn : sumMap ((Q.comp P).comp Q - Q) (0 : AdjointableMap B Std Std) =
      -sumMap (Q - (Q.comp P).comp Q) (0 : AdjointableMap B Std Std) := by
    rw [← sumMap_neg, neg_sub, neg_zero]
  rw [hn, ← h]
  abel

end BC4lean.KKTheory
