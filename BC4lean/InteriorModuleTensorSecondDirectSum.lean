import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.KasparovDirectSumIso
import BC4lean.ModuleCreationMap

/-! # Interior tensor distributivity in the second Hilbert module

For the actual block representation, x tensor (y,z) maps to
(x tensor y,x tensor z). The complete coefficient-valued form is
preserved before radical descent. Closed range and pure-tensor density
prove that the resulting completed isometry is onto. Neither source
representation is required to be nondegenerate or compact.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorSecondDirectSum
open scoped InnerProductSpace

variable {B C E F G : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C G G)

local instance secondSourceSumComplete : CompleteSpace (HilbertModuleSum C F G) :=
  hilbertModuleSum_complete
local instance secondTargetSumComplete : CompleteSpace
    (HilbertModuleSum C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) ψ)) :=
  hilbertModuleSum_complete

abbrev SourceTensor := InteriorModuleTensor (E := E) (sumRepresentation φ ψ)
abbrev TargetSum := HilbertModuleSum C (InteriorModuleTensor (E := E) φ)
  (InteriorModuleTensor (E := E) ψ)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
def bilinear : E →ₗ[ℂ] HilbertModuleSum C F G →ₗ[ℂ] TargetSum (E := E) φ ψ where
  toFun x := (sumMap (moduleCreationMap φ x) (moduleCreationMap ψ x)).toCLM.toLinearMap
  map_add' x z := by
    ext y
    change sumMap (moduleCreationMap φ (x + z)) (moduleCreationMap ψ (x + z)) y =
      sumMap (moduleCreationMap φ x) (moduleCreationMap ψ x) y +
        sumMap (moduleCreationMap φ z) (moduleCreationMap ψ z) y
    rw [moduleCreationMap_add, moduleCreationMap_add, sumMap_add, AdjointableMap.coe_add_apply]
  map_smul' a x := by
    ext y
    change sumMap (moduleCreationMap φ (a • x)) (moduleCreationMap ψ (a • x)) y =
      a • sumMap (moduleCreationMap φ x) (moduleCreationMap ψ x) y
    rw [moduleCreationMap_smul, moduleCreationMap_smul, sumMap_smul,
      AdjointableMap.coe_smul_apply]

theorem bilinear_balance (b : B) (x : E) (y : HilbertModuleSum C F G) :
    bilinear φ ψ (MulOpposite.op b • x) y = bilinear φ ψ x (sumRepresentation φ ψ b y) := by
  change sumMap (moduleCreationMap φ (MulOpposite.op b • x))
    (moduleCreationMap ψ (MulOpposite.op b • x)) y =
      sumMap (moduleCreationMap φ x) (moduleCreationMap ψ x) (sumMap (φ b) (ψ b) y)
  simp only [sumMap_apply, moduleCreationMap_apply, sumMk_fst, sumMk_snd]
  change sumMk (interiorModuleTensorMk φ (MulOpposite.op b • x) y.fst)
    (interiorModuleTensorMk ψ (MulOpposite.op b • x) y.snd) = _
  rw [interiorModuleTensorMk_balance, interiorModuleTensorMk_balance]
  rfl

def balancedMap : BalancedModuleTensor (E := E) (sumRepresentation φ ψ) →ₗ[ℂ]
    TargetSum (E := E) φ ψ :=
  moduleTensorLift (sumRepresentation φ ψ) (bilinear φ ψ) (bilinear_balance φ ψ)

@[simp] theorem balancedMap_mk (x : E) (y : HilbertModuleSum C F G) :
    balancedMap φ ψ (moduleTensorMk (sumRepresentation φ ψ) x y) =
      sumMk (interiorModuleTensorMk φ x y.fst) (interiorModuleTensorMk ψ x y.snd) := by
  change sumMap (moduleCreationMap φ x) (moduleCreationMap ψ x) y = _
  rw [sumMap_apply]
  rfl

theorem balancedMap_inner (u v : BalancedModuleTensor (E := E) (sumRepresentation φ ψ)) :
    ⟪balancedMap φ ψ u, balancedMap φ ψ v⟫_(Cᵐᵒᵖ) =
      moduleTensorInner (sumRepresentation φ ψ) u v := by
  revert v
  refine moduleTensor_induction (sumRepresentation φ ψ) u ?_ ?_ ?_
  · intro v; simp
  · intro x y v
    refine moduleTensor_induction (sumRepresentation φ ψ) v ?_ ?_ ?_
    · simp
    · intro x' y'
      simp only [balancedMap_mk, inner_sum, sumMk_fst, sumMk_snd,
        interiorModuleTensorInner_mk_mk, moduleTensorInner_mk_mk, moduleTensorPureInner,
        sumRepresentation_apply, sumMap_apply]
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hv]

def isometry : SourceTensor (E := E) φ ψ →ₗᵢ[ℂ] TargetSum (E := E) φ ψ :=
  InteriorModuleTensorFormCompletion.completedIsometry (sumRepresentation φ ψ)
    (balancedMap φ ψ) (balancedMap_inner φ ψ)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
@[simp] theorem isometry_mk (x : E) (y : HilbertModuleSum C F G) :
    isometry φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x y) =
      sumMk (interiorModuleTensorMk φ x y.fst) (interiorModuleTensorMk ψ x y.snd) :=
  by
    simpa only [isometry, balancedMap_mk] using
      (InteriorModuleTensorFormCompletion.completedIsometry_mk
        (B := B) (C := C) (E := E) (F := HilbertModuleSum C F G)
        (H := TargetSum (E := E) φ ψ) (sumRepresentation φ ψ)
        (balancedMap φ ψ) (balancedMap_inner φ ψ) x y)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem isometry_surjective : Function.Surjective (isometry (E := E) φ ψ) := by
  let R : Submodule ℂ (TargetSum (E := E) φ ψ) := (isometry (E := E) φ ψ).toLinearMap.range
  have hR : IsClosed (R : Set (TargetSum (E := E) φ ψ)) :=
    (isometry φ ψ).isometry.isUniformInducing.isComplete_range.isClosed
  have hleft (z : InteriorModuleTensor (E := E) φ) :
      sumMk z (0 : InteriorModuleTensor (E := E) ψ) ∈ R := by
    let P := R.comap (sumInlCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
      (F := InteriorModuleTensor (E := E) ψ)).toLinearMap
    have hP : IsClosed (P : Set (InteriorModuleTensor (E := E) φ)) :=
      hR.preimage (sumInlCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
        (F := InteriorModuleTensor (E := E) ψ)).continuous
    have hspan : Submodule.span ℂ
        (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,y⟩,rfl⟩
      refine ⟨interiorModuleTensorMk (sumRepresentation φ ψ) x (sumMk y (0 : G)), ?_⟩
      change isometry φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x (sumMk y (0 : G))) = _
      simp only [isometry_mk, sumMk_fst, sumMk_snd, map_zero]
      rfl
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  have hright (z : InteriorModuleTensor (E := E) ψ) :
      sumMk (0 : InteriorModuleTensor (E := E) φ) z ∈ R := by
    let P := R.comap (sumInrCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
      (F := InteriorModuleTensor (E := E) ψ)).toLinearMap
    have hP : IsClosed (P : Set (InteriorModuleTensor (E := E) ψ)) :=
      hR.preimage (sumInrCLM (B := C) (E := InteriorModuleTensor (E := E) φ)
        (F := InteriorModuleTensor (E := E) ψ)).continuous
    have hspan : Submodule.span ℂ
        (Set.range fun p : E × G => interiorModuleTensorMk ψ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,y⟩,rfl⟩
      refine ⟨interiorModuleTensorMk (sumRepresentation φ ψ) x (sumMk (0 : F) y), ?_⟩
      change isometry φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x (sumMk (0 : F) y)) = _
      simp only [isometry_mk, sumMk_fst, sumMk_snd, map_zero]
      rfl
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense ψ z)
  intro z
  change z ∈ R
  have h := R.add_mem (hleft z.fst) (hright z.snd)
  simpa only [sumMk_add, add_zero, zero_add, sumMk_eta] using h

def hilbertEquiv : HilbertModuleEquiv C (SourceTensor (E := E) φ ψ) (TargetSum (E := E) φ ψ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ ψ) (isometry_surjective φ ψ)
  inner_map := InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (x : E) (y : HilbertModuleSum C F G) :
    hilbertEquiv φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x y) =
      sumMk (interiorModuleTensorMk φ x y.fst) (interiorModuleTensorMk ψ x y.snd) :=
  isometry_mk φ ψ x y

end BC4lean.KKTheory.InteriorModuleTensorSecondDirectSum
