import BC4lean.OrdinaryScalarCoefficientTensor
import BC4lean.ProjectionInteriorModuleTensorEquiv
import BC4lean.GradedMatrixMoritaTensorDirectSum
import BC4lean.RelativeProjectionKasparovCycle

/-! # Actual coefficient extension of compact-relative projection cycles

The completed tensor of each genuine projection range is the range of its
actual tensor projection. The completed tensor of the supported direct sum
is identified by a whole coefficient-Hilbert unitary. The cross maps are
intertwined through their actual ambient inclusions, so the entire cycle,
including its off-diagonal Fredholm operator, is transported exactly.
-/

noncomputable section
namespace BC4lean.KKTheory
open RectangularInteriorModuleTensorOperator

variable {B C E : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]
  (f : B →⋆ₙₐ[ℂ] C)

local notation "φ" => standardCoefficientImageRepresentation f
local notation "TensorE" => InteriorModuleTensor (E := E) φ
local instance standardRelativeProjectionCoefficientTensorLocalInstance01 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete
local instance standardRelativeProjectionCoefficientTensorLocalInstance02 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M]
    [CStarModule Cᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Cᵐᵒᵖ N] [CStarModule Cᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum C M N) := hilbertModuleSum_complete

def relativeProjectionCoefficientTensorEquiv
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    HilbertModuleEquiv C
      (InteriorModuleTensor (E := HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q)) φ)
      (HilbertModuleSum C (ProjectionModule (interiorModuleTensorOperator φ P))
        (ProjectionModule (interiorModuleTensorOperator φ Q))) :=
  (GradedMatrixMoritaTensorDirectSum.hilbertEquiv φ).trans
    ((projectionInteriorModuleTensorEquiv φ P hP).sum
      (projectionInteriorModuleTensorEquiv φ Q hQ))

omit [TopologicalSpace.SeparableSpace C] in
@[simp] theorem relativeProjectionCoefficientTensorEquiv_mk
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (x : HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q)) (y : Cᵐᵒᵖ) :
    relativeProjectionCoefficientTensorEquiv f P Q hP hQ (interiorModuleTensorMk φ x y) =
      sumMk (projectionInteriorModuleTensorEquiv φ P hP (interiorModuleTensorMk φ x.fst y))
        (projectionInteriorModuleTensorEquiv φ Q hQ (interiorModuleTensorMk φ x.snd y)) := by
  simp only [relativeProjectionCoefficientTensorEquiv, HilbertModuleEquiv.trans_apply,
    GradedMatrixMoritaTensorDirectSum.hilbertEquiv_mk, HilbertModuleEquiv.sum_apply,
    sumMk_fst, sumMk_snd]

omit [TopologicalSpace.SeparableSpace C] in
/-- The whole range cross map is intertwined, with no surjectivity of f assumed. -/
theorem projectionInteriorModuleTensorEquiv_crossMap
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (z : InteriorModuleTensor (E := ProjectionModule P) φ) :
    projectionInteriorModuleTensorEquiv φ Q hQ (tensor φ (projectionCrossMap P Q hP hQ) z) =
      projectionCrossMap (interiorModuleTensorOperator φ P) (interiorModuleTensorOperator φ Q)
        (hP.map (interiorModuleTensorOperatorHom φ)) (hQ.map (interiorModuleTensorOperatorHom φ))
          (projectionInteriorModuleTensorEquiv φ P hP z) := by
  apply Subtype.ext
  change tensor φ (projectionInclusion Q hQ)
      (tensor φ (projectionCrossMap P Q hP hQ) z) =
    interiorModuleTensorOperator φ Q (tensor φ (projectionInclusion P hP) z)
  rw [← AdjointableMap.comp_apply, ← tensor_comp, ← tensor_endo,
    ← AdjointableMap.comp_apply, ← tensor_comp]
  congr 2
  ext x
  rfl

set_option maxHeartbeats 2000000 in
def relativeProjectionCoefficientTensorCycleIso
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E) :
    KasparovCycleIso
      ((relativeProjectionCycle (Γ := PUnit) P Q hP hQ hc hE).scalarCoefficientTensor f)
      (relativeProjectionCycle (Γ := PUnit) (interiorModuleTensorOperator φ P)
        (interiorModuleTensorOperator φ Q)
        (hP.map (interiorModuleTensorOperatorHom φ)) (hQ.map (interiorModuleTensorOperatorHom φ))
        (by
          have h := hc.interiorModuleTensorOperator φ
            (fun b => standardLeftMul_mem_moduleCompact (f b))
          change IsModuleCompact ((interiorModuleTensorOperatorHom φ) (P - Q)) at h
          simpa only [map_sub, interiorModuleTensorOperatorHom_apply] using h)
        (hE.interiorTensor standard_module_isCountablyGenerated φ)) where
  moduleEquiv := relativeProjectionCoefficientTensorEquiv f P Q hP hQ
  grading_intertwine z := by
    let U := (relativeProjectionCoefficientTensorEquiv f P Q hP hQ).toAdjointable.toCLM
    let J := (GradedHilbertModule.trivial :
      GradedHilbertModule (CStarGrading.trivial : CStarGrading B) (ProjectionModule P)).sum
        (GradedHilbertModule.trivial :
          GradedHilbertModule (CStarGrading.trivial : CStarGrading B) (ProjectionModule Q)).opposite
    let K := (GradedHilbertModule.trivial :
      GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
        (ProjectionModule (interiorModuleTensorOperator φ P))).sum
          (GradedHilbertModule.trivial :
            GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
              (ProjectionModule (interiorModuleTensorOperator φ Q))).opposite
    let K₀ : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) Cᵐᵒᵖ :=
      GradedHilbertModule.trivial
    have hφ : ModuleTensorRepresentationGraded
        (δB := (CStarGrading.trivial : CStarGrading B))
        (standardCoefficientImageRepresentation f) K₀ := by
      intro b y
      rfl
    let JT : GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
        (InteriorModuleTensor
          (E := HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q)) φ) :=
      J.interiorTensor K₀ hφ
    have hu : U.comp JT.grading.toContinuousLinearEquiv.toContinuousLinearMap =
      K.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp U := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change relativeProjectionCoefficientTensorEquiv f P Q hP hQ
          ((J.interiorTensor K₀ hφ).grading (interiorModuleTensorMk φ x y)) = _
      rw [GradedHilbertModule.interiorTensor_grading_mk]
      change relativeProjectionCoefficientTensorEquiv f P Q hP hQ
          (interiorModuleTensorMk φ (sumMk x.fst (-x.snd)) y) =
        sumMk ((relativeProjectionCoefficientTensorEquiv f P Q hP hQ
          (interiorModuleTensorMk φ x y)).fst)
          (-((relativeProjectionCoefficientTensorEquiv f P Q hP hQ
            (interiorModuleTensorMk φ x y)).snd))
      rw [relativeProjectionCoefficientTensorEquiv_mk, relativeProjectionCoefficientTensorEquiv_mk]
      simp only [sumMk_fst, sumMk_snd, map_neg, LinearMap.neg_apply]
    exact DFunLike.congr_fun hu z
  action_intertwine _ _ := rfl
  representation_intertwine a z := by
    change relativeProjectionCoefficientTensorEquiv f P Q hP hQ
      (interiorModuleTensorOperator φ (scalarModuleRepresentation a) z) =
        a • relativeProjectionCoefficientTensorEquiv f P Q hP hQ z
    have hs : (scalarModuleRepresentation a : AdjointableMap B
        (HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))
          (HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))) = a • 1 := by ext x; rfl
    rw [hs]
    change relativeProjectionCoefficientTensorEquiv f P Q hP hQ
      (interiorModuleTensorOperatorHom φ (a • 1) z) = _
    rw [map_smul, map_one]
    exact HilbertModuleEquiv.map_smul _ _ _
  operator_intertwine z := by
    let U := (relativeProjectionCoefficientTensorEquiv f P Q hP hQ).toAdjointable.toCLM
    let T := projectionCrossMap (interiorModuleTensorOperator φ P) (interiorModuleTensorOperator φ Q)
      (hP.map (interiorModuleTensorOperatorHom φ)) (hQ.map (interiorModuleTensorOperatorHom φ))
    have hu : U.comp (interiorModuleTensorOperator φ
        (offDiagonalAdjointable (projectionCrossMap P Q hP hQ))).toCLM =
        (offDiagonalAdjointable T).toCLM.comp U := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change relativeProjectionCoefficientTensorEquiv f P Q hP hQ
        (interiorModuleTensorOperator φ (offDiagonalAdjointable (projectionCrossMap P Q hP hQ))
          (interiorModuleTensorMk φ x y)) =
        offDiagonalAdjointable T
          (relativeProjectionCoefficientTensorEquiv f P Q hP hQ (interiorModuleTensorMk φ x y))
      rw [interiorModuleTensorOperator_mk, relativeProjectionCoefficientTensorEquiv_mk,
        relativeProjectionCoefficientTensorEquiv_mk]
      dsimp only [T]
      simp only [offDiagonalAdjointable_apply, projectionCrossMap_adjoint, sumMk_fst, sumMk_snd]
      let xP : ProjectionModule P :=
        sumFst (B := B) (E := ProjectionModule P) (F := ProjectionModule Q) x
      let xQ : ProjectionModule Q :=
        sumSnd (B := B) (E := ProjectionModule P) (F := ProjectionModule Q) x
      apply Prod.ext
      · change projectionInteriorModuleTensorEquiv φ P hP
            (interiorModuleTensorMk φ (projectionCrossMap Q P hQ hP xQ) y) =
          projectionCrossMap (interiorModuleTensorOperator φ Q) (interiorModuleTensorOperator φ P)
            (hQ.map (interiorModuleTensorOperatorHom φ))
            (hP.map (interiorModuleTensorOperatorHom φ))
              (projectionInteriorModuleTensorEquiv φ Q hQ (interiorModuleTensorMk φ xQ y))
        simpa only [tensor_mk] using
          projectionInteriorModuleTensorEquiv_crossMap f Q P hQ hP
            (interiorModuleTensorMk φ xQ y)
      · change projectionInteriorModuleTensorEquiv φ Q hQ
            (interiorModuleTensorMk φ (projectionCrossMap P Q hP hQ xP) y) =
          projectionCrossMap (interiorModuleTensorOperator φ P) (interiorModuleTensorOperator φ Q)
            (hP.map (interiorModuleTensorOperatorHom φ))
            (hQ.map (interiorModuleTensorOperatorHom φ))
              (projectionInteriorModuleTensorEquiv φ P hP (interiorModuleTensorMk φ xP y))
        simpa only [tensor_mk] using
          projectionInteriorModuleTensorEquiv_crossMap f P Q hP hQ
            (interiorModuleTensorMk φ xP y)
    exact DFunLike.congr_fun hu z

end BC4lean.KKTheory
