import BC4lean.GradedMatrixMoritaCompletion
import BC4lean.HilbertModuleSum

/-! # The actual interior-tensor/direct-sum unitary

The source and target use their coefficient-valued Hilbert norms. The map
(x,z) ⊗ y ↦ (x ⊗ y,z ⊗ y) preserves the entire balanced coefficient form,
descends through the actual tensor radical and extends to its completion.
Surjectivity follows from the closed isometric range and dense pure tensors
in each actual Hilbert summand.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaTensorDirectSum
open scoped InnerProductSpace

variable {B C E G F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace G] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance sourceSumComplete : CompleteSpace (HilbertModuleSum B E G) := hilbertModuleSum_complete
local instance targetSumComplete : CompleteSpace
    (HilbertModuleSum C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := G) φ)) :=
  hilbertModuleSum_complete

abbrev SourceTensor := InteriorModuleTensor (E := HilbertModuleSum B E G) φ
abbrev TargetSum := HilbertModuleSum C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := G) φ)

def bilinear : HilbertModuleSum B E G →ₗ[ℂ] F →ₗ[ℂ] TargetSum (E := E) (G := G) φ where
  toFun x :=
    { toFun y := sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y)
      map_add' y z := by
        change sumMk (interiorModuleTensorMk φ x.fst (y + z))
          (interiorModuleTensorMk φ x.snd (y + z)) =
          sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y) +
            sumMk (interiorModuleTensorMk φ x.fst z) (interiorModuleTensorMk φ x.snd z)
        rw [sumMk_add]
        exact congrArg₂ (sumMk (B := C))
          ((interiorModuleTensorMk (E := E) φ x.fst).map_add y z)
          ((interiorModuleTensorMk (E := G) φ x.snd).map_add y z)
      map_smul' a y := by
        change sumMk (interiorModuleTensorMk φ x.fst (a • y))
          (interiorModuleTensorMk φ x.snd (a • y)) =
          a • sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y)
        rw [sumMk_smul]
        exact congrArg₂ (sumMk (B := C))
          ((interiorModuleTensorMk (E := E) φ x.fst).map_smul a y)
          ((interiorModuleTensorMk (E := G) φ x.snd).map_smul a y) }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change sumMk (interiorModuleTensorMk φ (x.fst + z.fst) y)
      (interiorModuleTensorMk φ (x.snd + z.snd) y) =
      sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y) +
        sumMk (interiorModuleTensorMk φ z.fst y) (interiorModuleTensorMk φ z.snd y)
    rw [sumMk_add]
    exact congrArg₂ (sumMk (B := C))
      (LinearMap.congr_fun ((interiorModuleTensorMk (E := E) φ).map_add x.fst z.fst) y)
      (LinearMap.congr_fun ((interiorModuleTensorMk (E := G) φ).map_add x.snd z.snd) y)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change sumMk (interiorModuleTensorMk φ (a • x.fst) y)
      (interiorModuleTensorMk φ (a • x.snd) y) =
      a • sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y)
    rw [sumMk_smul]
    exact congrArg₂ (sumMk (B := C))
      (LinearMap.congr_fun ((interiorModuleTensorMk (E := E) φ).map_smul a x.fst) y)
      (LinearMap.congr_fun ((interiorModuleTensorMk (E := G) φ).map_smul a x.snd) y)

theorem bilinear_balance (b : B) (x : HilbertModuleSum B E G) (y : F) :
    bilinear φ (MulOpposite.op b • x) y = bilinear φ x (φ b y) := by
  change sumMk (interiorModuleTensorMk φ (MulOpposite.op b • x.fst) y)
    (interiorModuleTensorMk φ (MulOpposite.op b • x.snd) y) = _
  rw [interiorModuleTensorMk_balance, interiorModuleTensorMk_balance]
  rfl

def balancedMap : BalancedModuleTensor (E := HilbertModuleSum B E G) φ →ₗ[ℂ]
    TargetSum (E := E) (G := G) φ := moduleTensorLift φ (bilinear φ) (bilinear_balance φ)

@[simp] theorem balancedMap_mk (x : HilbertModuleSum B E G) (y : F) :
    balancedMap φ (moduleTensorMk φ x y) =
      sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y) := rfl

theorem balancedMap_inner (u v : BalancedModuleTensor (E := HilbertModuleSum B E G) φ) :
    ⟪balancedMap φ u, balancedMap φ v⟫_(Cᵐᵒᵖ) = moduleTensorInner φ u v := by
  revert v
  refine moduleTensor_induction (E := HilbertModuleSum B E G) φ u ?_ ?_ ?_
  · intro v
    simp [CStarModule.inner_zero_left (A := Cᵐᵒᵖ)
      (E := TargetSum (E := E) (G := G) φ)]
  · intro x y v
    refine moduleTensor_induction (E := HilbertModuleSum B E G) φ v ?_ ?_ ?_
    · simp [CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := TargetSum (E := E) (G := G) φ)]
    · intro x' y'
      simp only [balancedMap_mk,
        inner_sum (B := C) (E := InteriorModuleTensor (E := E) φ)
          (F := InteriorModuleTensor (E := G) φ),
        inner_sum (B := B) (E := E) (F := G), sumMk_fst, sumMk_snd,
        interiorModuleTensorInner_mk_mk, moduleTensorInner_mk_mk, moduleTensorPureInner,
        MulOpposite.unop_add, map_add, AdjointableMap.coe_add_apply,
        CStarModule.inner_add_right (A := Cᵐᵒᵖ) (E := F)]
    · intro v w hv hw
      simp only [map_add,
        CStarModule.inner_add_right (A := Cᵐᵒᵖ)
          (E := TargetSum (E := E) (G := G) φ), hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply,
      CStarModule.inner_add_left (A := Cᵐᵒᵖ)
        (E := TargetSum (E := E) (G := G) φ), hu, hv]

def isometry : SourceTensor (E := E) (G := G) φ →ₗᵢ[ℂ] TargetSum (E := E) (G := G) φ :=
  GradedMatrixMoritaCompletion.completedIsometry φ (balancedMap φ) (balancedMap_inner φ)

@[simp] theorem isometry_mk (x : HilbertModuleSum B E G) (y : F) :
    isometry φ (interiorModuleTensorMk φ x y) =
      sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y) :=
  GradedMatrixMoritaCompletion.completedIsometry_mk
    (B := B) (C := C) (E := HilbertModuleSum B E G) (F := F)
    (H := TargetSum (E := E) (G := G) φ) φ (balancedMap φ) (balancedMap_inner φ) x y

theorem isometry_surjective : Function.Surjective (isometry (E := E) (G := G) φ) := by
  let R := (isometry (E := E) (G := G) φ).toLinearMap.range
  have hR : IsClosed (R : Set (TargetSum (E := E) (G := G) φ)) :=
    (isometry (E := E) (G := G) φ).isometry.isClosedEmbedding.isClosed_range
  have hleft (z : InteriorModuleTensor (E := E) φ) : sumMk z (0 : InteriorModuleTensor (E := G) φ) ∈ R := by
    let P := R.comap (sumInlCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
      (F := InteriorModuleTensor (E := G) φ)).toLinearMap
    have hP : IsClosed (P : Set (InteriorModuleTensor (E := E) φ)) :=
      hR.preimage (sumInlCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
        (F := InteriorModuleTensor (E := G) φ)).continuous
    have hspan : Submodule.span ℂ (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      refine ⟨interiorModuleTensorMk φ (sumMk x (0 : G)) y, ?_⟩
      change isometry (E := E) (G := G) φ
        (interiorModuleTensorMk (E := HilbertModuleSum B E G) φ (sumMk x (0 : G)) y) =
        sumMk (interiorModuleTensorMk (E := E) φ x y) (0 : InteriorModuleTensor (E := G) φ)
      rw [isometry_mk]
      change sumMk (interiorModuleTensorMk (E := E) φ x y)
        (interiorModuleTensorMk (E := G) φ (0 : G) y) = _
      have hz : interiorModuleTensorMk (E := G) φ (0 : G) y = 0 :=
        LinearMap.congr_fun (map_zero (interiorModuleTensorMk (E := G) φ)) y
      rw [hz]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  have hright (z : InteriorModuleTensor (E := G) φ) : sumMk (0 : InteriorModuleTensor (E := E) φ) z ∈ R := by
    let P := R.comap (sumInrCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
      (F := InteriorModuleTensor (E := G) φ)).toLinearMap
    have hP : IsClosed (P : Set (InteriorModuleTensor (E := G) φ)) :=
      hR.preimage (sumInrCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
        (F := InteriorModuleTensor (E := G) φ)).continuous
    have hspan : Submodule.span ℂ (Set.range fun p : G × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      refine ⟨interiorModuleTensorMk φ (sumMk (0 : E) x) y, ?_⟩
      change isometry (E := E) (G := G) φ
        (interiorModuleTensorMk (E := HilbertModuleSum B E G) φ (sumMk (0 : E) x) y) =
        sumMk (0 : InteriorModuleTensor (E := E) φ) (interiorModuleTensorMk (E := G) φ x y)
      rw [isometry_mk]
      change sumMk (interiorModuleTensorMk (E := E) φ (0 : E) y)
        (interiorModuleTensorMk (E := G) φ x y) = _
      have hz : interiorModuleTensorMk (E := E) φ (0 : E) y = 0 :=
        LinearMap.congr_fun (map_zero (interiorModuleTensorMk (E := E) φ)) y
      rw [hz]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  intro z
  change z ∈ R
  have h := R.add_mem (hleft z.fst) (hright z.snd)
  simpa only [sumMk_add, add_zero, zero_add, sumMk_eta] using h

/-- The constructed unitary preserves the actual entire coefficient inner product. -/
def hilbertEquiv : HilbertModuleEquiv C (SourceTensor (E := E) (G := G) φ)
    (TargetSum (E := E) (G := G) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ) (isometry_surjective φ)
  inner_map := GradedMatrixMoritaCompletion.completedIsometry_inner
    (B := B) (C := C) (E := HilbertModuleSum B E G) (F := F)
    (H := TargetSum (E := E) (G := G) φ) φ (balancedMap φ) (balancedMap_inner φ)

@[simp] theorem hilbertEquiv_mk (x : HilbertModuleSum B E G) (y : F) :
    hilbertEquiv φ (interiorModuleTensorMk φ x y) =
      sumMk (interiorModuleTensorMk φ x.fst y) (interiorModuleTensorMk φ x.snd y) := isometry_mk φ x y

@[simp] theorem hilbertEquiv_sumMk_tensor (x : E) (z : G) (y : F) :
    hilbertEquiv φ (interiorModuleTensorMk φ (sumMk x z) y) =
      sumMk (interiorModuleTensorMk φ x y) (interiorModuleTensorMk φ z y) := hilbertEquiv_mk φ _ y

end BC4lean.KKTheory.GradedMatrixMoritaTensorDirectSum
