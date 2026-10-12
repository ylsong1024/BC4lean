import BC4lean.CliffordOddSourceCycle
import BC4lean.CliffordPairModule
import BC4lean.InteriorModuleTensorFormCompletion

/-! # Actual balancing of an odd Clifford pair against a signed source cycle

The genuine product-coefficient balancing selects the two matching
coordinates. Its completed target is the Hilbert direct sum over C, whose
inner product is the sum of both pairings. The full form, both actual null
quotients, completion and surjectivity are proved without coefficient units.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddBalancedTensor
open scoped InnerProductSpace

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance cliffordOddBalancedTensorLocalInstance1 : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete

abbrev BaseTensor := InteriorModuleTensor (E := E) φ
abbrev Target := HilbertModuleSum C (BaseTensor (E := E) φ) (BaseTensor (E := E) φ)
abbrev Source := InteriorModuleTensor (E := CliffordPairModule B E)
  (CliffordOddSourceCycle.representation φ)

local instance cliffordOddBalancedTensorLocalInstance2 : CompleteSpace (Target (E := E) φ) := hilbertModuleSum_complete

def bilinear : CliffordPairModule B E →ₗ[ℂ] HilbertModuleSum C F F →ₗ[ℂ] Target (E := E) φ where
  toFun x :=
    { toFun y := sumMk (interiorModuleTensorMk φ x.1 y.fst) (interiorModuleTensorMk φ x.2 y.snd)
      map_add' y z := by apply Prod.ext <;> simp
      map_smul' a y := by apply Prod.ext <;> simp }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Prod.ext
    · change interiorModuleTensorMk φ (x.1 + z.1) y.fst =
        interiorModuleTensorMk φ x.1 y.fst + interiorModuleTensorMk φ z.1 y.fst
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.fst)
        ((interiorModuleTensorMk φ).map_add x.1 z.1)
    · change interiorModuleTensorMk φ (x.2 + z.2) y.snd =
        interiorModuleTensorMk φ x.2 y.snd + interiorModuleTensorMk φ z.2 y.snd
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.snd)
        ((interiorModuleTensorMk φ).map_add x.2 z.2)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply Prod.ext
    · change interiorModuleTensorMk φ (a • x.1) y.fst =
        a • interiorModuleTensorMk φ x.1 y.fst
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.fst)
        ((interiorModuleTensorMk φ).map_smul a x.1)
    · change interiorModuleTensorMk φ (a • x.2) y.snd =
        a • interiorModuleTensorMk φ x.2 y.snd
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.snd)
        ((interiorModuleTensorMk φ).map_smul a x.2)

@[simp] theorem bilinear_apply (x : CliffordPairModule B E) (y : HilbertModuleSum C F F) :
    bilinear φ x y = sumMk (interiorModuleTensorMk φ x.1 y.fst)
      (interiorModuleTensorMk φ x.2 y.snd) := rfl

theorem bilinear_balance (b : B × B) (x : CliffordPairModule B E)
    (y : HilbertModuleSum C F F) :
    bilinear φ (MulOpposite.op b • x) y =
      bilinear φ x (CliffordOddSourceCycle.representation φ b y) := by
  apply Prod.ext
  · change interiorModuleTensorMk φ (MulOpposite.op b.1 • x.1) y.fst =
      interiorModuleTensorMk φ x.1 (sumMap (φ b.1) (φ b.2) y).fst
    rw [sumMap_apply, sumMk_fst]
    exact interiorModuleTensorMk_balance φ b.1 x.1 y.fst
  · change interiorModuleTensorMk φ (MulOpposite.op b.2 • x.2) y.snd =
      interiorModuleTensorMk φ x.2 (sumMap (φ b.1) (φ b.2) y).snd
    rw [sumMap_apply, sumMk_snd]
    exact interiorModuleTensorMk_balance φ b.2 x.2 y.snd

def balancedMap : BalancedModuleTensor (E := CliffordPairModule B E)
    (CliffordOddSourceCycle.representation φ) →ₗ[ℂ] Target (E := E) φ :=
  moduleTensorLift (CliffordOddSourceCycle.representation φ) (bilinear φ) (bilinear_balance φ)

@[simp] theorem balancedMap_mk (x : CliffordPairModule B E) (y : HilbertModuleSum C F F) :
    balancedMap φ (moduleTensorMk (CliffordOddSourceCycle.representation φ) x y) =
      bilinear φ x y := rfl

theorem bilinear_inner (x x' : CliffordPairModule B E) (y y' : HilbertModuleSum C F F) :
    ⟪bilinear φ x y, bilinear φ x' y'⟫_(Cᵐᵒᵖ) =
      moduleTensorPureInner (CliffordOddSourceCycle.representation φ) x y x' y' := by
  change
    ⟪interiorModuleTensorMk φ x.1 y.fst,
      interiorModuleTensorMk φ x'.1 y'.fst⟫_(Cᵐᵒᵖ) +
    ⟪interiorModuleTensorMk φ x.2 y.snd,
      interiorModuleTensorMk φ x'.2 y'.snd⟫_(Cᵐᵒᵖ) =
    ⟪y.fst, (sumMap (φ (MulOpposite.unop ⟪x.1, x'.1⟫_(Bᵐᵒᵖ)))
      (φ (MulOpposite.unop ⟪x.2, x'.2⟫_(Bᵐᵒᵖ))) y').fst⟫_(Cᵐᵒᵖ) +
    ⟪y.snd, (sumMap (φ (MulOpposite.unop ⟪x.1, x'.1⟫_(Bᵐᵒᵖ)))
      (φ (MulOpposite.unop ⟪x.2, x'.2⟫_(Bᵐᵒᵖ))) y').snd⟫_(Cᵐᵒᵖ)
  rw [interiorModuleTensorInner_mk_mk, interiorModuleTensorInner_mk_mk]
  simp only [moduleTensorPureInner, sumMap_apply, sumMk_fst, sumMk_snd]

theorem balancedMap_inner
    (u v : BalancedModuleTensor (E := CliffordPairModule B E)
      (CliffordOddSourceCycle.representation φ)) :
    ⟪balancedMap φ u, balancedMap φ v⟫_(Cᵐᵒᵖ) =
      moduleTensorInner (CliffordOddSourceCycle.representation φ) u v := by
  revert v
  refine moduleTensor_induction (CliffordOddSourceCycle.representation φ) u ?_ ?_ ?_
  · intro v; simp
  · intro x y v
    refine moduleTensor_induction (CliffordOddSourceCycle.representation φ) v ?_ ?_ ?_
    · simp
    · intro x' y'
      rw [balancedMap_mk, balancedMap_mk, moduleTensorInner_mk_mk]
      exact bilinear_inner φ x x' y y'
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hv]

def isometry : Source (E := E) φ →ₗᵢ[ℂ] Target (E := E) φ :=
  InteriorModuleTensorFormCompletion.completedIsometry (CliffordOddSourceCycle.representation φ)
    (balancedMap φ) (balancedMap_inner φ)

@[simp] theorem isometry_mk (x : CliffordPairModule B E) (y : HilbertModuleSum C F F) :
    isometry φ (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ) x y) =
      bilinear φ x y := InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x y

set_option synthInstance.maxHeartbeats 80000 in
theorem isometry_surjective : Function.Surjective (isometry (E := E) φ) := by
  let : Module ℂ (Target (E := E) φ) :=
    WithCStarModule.instModule (R := ℂ) (A := Cᵐᵒᵖ)
      (E := BaseTensor (E := E) φ × BaseTensor (E := E) φ)
  let R : Submodule ℂ (Target (E := E) φ) := (isometry (E := E) φ).toLinearMap.range
  have hR : IsClosed (R : Set (Target (E := E) φ)) :=
    (isometry φ).isometry.isUniformInducing.isComplete_range.isClosed
  have hleft (z : BaseTensor (E := E) φ) : sumMk z (0 : BaseTensor (E := E) φ) ∈ R := by
    let L : BaseTensor (E := E) φ →L[ℂ] Target (E := E) φ :=
      sumInlCLM (B := C) (E := BaseTensor (E := E) φ) (F := BaseTensor (E := E) φ)
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set (BaseTensor (E := E) φ)) := hR.preimage L.continuous
    have hspan : Submodule.span ℂ
        (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      refine ⟨interiorModuleTensorMk (CliffordOddSourceCycle.representation φ)
        (cliffordPairMk x 0) (sumMk y 0), ?_⟩
      change isometry φ (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ)
        (cliffordPairMk (B := B) x (0 : E)) (sumMk (B := C) y (0 : F))) =
          sumMk (interiorModuleTensorMk φ x y) (0 : BaseTensor (E := E) φ)
      rw [isometry_mk, bilinear_apply]
      change sumMk (interiorModuleTensorMk φ x y) (interiorModuleTensorMk φ (0 : E) (0 : F)) =
        sumMk (interiorModuleTensorMk φ x y) (0 : BaseTensor (E := E) φ)
      rw [(interiorModuleTensorMk φ (0 : E)).map_zero]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  have hright (z : BaseTensor (E := E) φ) : sumMk (0 : BaseTensor (E := E) φ) z ∈ R := by
    let L : BaseTensor (E := E) φ →L[ℂ] Target (E := E) φ :=
      sumInrCLM (B := C) (E := BaseTensor (E := E) φ) (F := BaseTensor (E := E) φ)
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set (BaseTensor (E := E) φ)) := hR.preimage L.continuous
    have hspan : Submodule.span ℂ
        (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      refine ⟨interiorModuleTensorMk (CliffordOddSourceCycle.representation φ)
        (cliffordPairMk 0 x) (sumMk 0 y), ?_⟩
      change isometry φ (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ)
        (cliffordPairMk (B := B) (0 : E) x) (sumMk (B := C) (0 : F) y)) =
          sumMk (0 : BaseTensor (E := E) φ) (interiorModuleTensorMk φ x y)
      rw [isometry_mk, bilinear_apply]
      change sumMk (interiorModuleTensorMk φ (0 : E) (0 : F)) (interiorModuleTensorMk φ x y) =
        sumMk (0 : BaseTensor (E := E) φ) (interiorModuleTensorMk φ x y)
      rw [(interiorModuleTensorMk φ (0 : E)).map_zero]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  intro z
  have h := R.add_mem (hleft z.fst) (hright z.snd)
  change sumMk z.fst 0 + sumMk 0 z.snd ∈ R at h
  have hz : sumMk z.fst 0 + sumMk 0 z.snd = z := by
    apply Prod.ext <;>
      simp only [WithCStarModule.add_fst, WithCStarModule.add_snd,
        sumMk_fst, sumMk_snd, add_zero, zero_add]
  rw [hz] at h
  exact h

/-- The full coefficient-form map gives an onto completed Hilbert-module unitary. -/
def hilbertEquiv : HilbertModuleEquiv C (Source (E := E) φ) (Target (E := E) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ) (isometry_surjective φ)
  inner_map := InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (x : CliffordPairModule B E) (y : HilbertModuleSum C F F) :
    hilbertEquiv φ (interiorModuleTensorMk (CliffordOddSourceCycle.representation φ) x y) =
      sumMk (interiorModuleTensorMk φ x.1 y.fst) (interiorModuleTensorMk φ x.2 y.snd) :=
  isometry_mk φ x y

end BC4lean.KKTheory.CliffordOddBalancedTensor
