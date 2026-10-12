import BC4lean.CliffordPairModule
import BC4lean.InteriorModuleTensorFormCompletion

/-! # Actual tensoring with a product-coefficient pair in the second factor

The bilinear map x tensor (y,z) maps to (x tensor y,x tensor z). It
preserves the entire product-coefficient inner form, descends through both
actual null quotients and extends to an onto completed module unitary.
The target has its true maximum norm, rather than the C-valued sum norm.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordPairSecondTensor
open scoped InnerProductSpace

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

abbrev representation : B →⋆ₙₐ[ℂ]
    AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F) :=
  cliffordPairDiagonalHom.toNonUnitalStarAlgHom.comp φ

abbrev BaseTensor := InteriorModuleTensor (E := E) φ
abbrev Source := InteriorModuleTensor (E := E) (representation φ)
abbrev Target := CliffordPairModule C (BaseTensor (E := E) φ)

def bilinear : E →ₗ[ℂ] CliffordPairModule C F →ₗ[ℂ] Target (E := E) φ where
  toFun x :=
    { toFun y := cliffordPairMk (B := C)
        (interiorModuleTensorMk φ x y.1) (interiorModuleTensorMk φ x y.2)
      map_add' y z := by
        apply Prod.ext
        · change interiorModuleTensorMk φ x (y.1 + z.1) =
            interiorModuleTensorMk φ x y.1 + interiorModuleTensorMk φ x z.1
          exact (interiorModuleTensorMk φ x).map_add y.1 z.1
        · change interiorModuleTensorMk φ x (y.2 + z.2) =
            interiorModuleTensorMk φ x y.2 + interiorModuleTensorMk φ x z.2
          exact (interiorModuleTensorMk φ x).map_add y.2 z.2
      map_smul' a y := by
        apply Prod.ext
        · change interiorModuleTensorMk φ x (a • y.1) = a • interiorModuleTensorMk φ x y.1
          exact (interiorModuleTensorMk φ x).map_smul a y.1
        · change interiorModuleTensorMk φ x (a • y.2) = a • interiorModuleTensorMk φ x y.2
          exact (interiorModuleTensorMk φ x).map_smul a y.2 }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Prod.ext
    · change interiorModuleTensorMk φ (x + z) y.1 =
        interiorModuleTensorMk φ x y.1 + interiorModuleTensorMk φ z y.1
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.1)
        ((interiorModuleTensorMk φ).map_add x z)
    · change interiorModuleTensorMk φ (x + z) y.2 =
        interiorModuleTensorMk φ x y.2 + interiorModuleTensorMk φ z y.2
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.2)
        ((interiorModuleTensorMk φ).map_add x z)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply Prod.ext
    · change interiorModuleTensorMk φ (a • x) y.1 = a • interiorModuleTensorMk φ x y.1
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.1)
        ((interiorModuleTensorMk φ).map_smul a x)
    · change interiorModuleTensorMk φ (a • x) y.2 = a • interiorModuleTensorMk φ x y.2
      exact congrArg (fun T : F →ₗ[ℂ] BaseTensor (E := E) φ => T y.2)
        ((interiorModuleTensorMk φ).map_smul a x)

@[simp] theorem bilinear_apply (x : E) (y : CliffordPairModule C F) :
    bilinear φ x y = cliffordPairMk (B := C)
      (interiorModuleTensorMk φ x y.1) (interiorModuleTensorMk φ x y.2) := rfl

theorem bilinear_balance (b : B) (x : E) (y : CliffordPairModule C F) :
    bilinear φ (MulOpposite.op b • x) y = bilinear φ x (representation φ b y) := by
  apply Prod.ext
  · exact interiorModuleTensorMk_balance φ b x y.1
  · exact interiorModuleTensorMk_balance φ b x y.2

def balancedMap : BalancedModuleTensor (E := E) (representation φ) →ₗ[ℂ] Target (E := E) φ :=
  moduleTensorLift (representation φ) (bilinear φ) (bilinear_balance φ)

@[simp] theorem balancedMap_mk (x : E) (y : CliffordPairModule C F) :
    balancedMap φ (moduleTensorMk (representation φ) x y) = bilinear φ x y := rfl

theorem bilinear_inner (x x' : E) (y y' : CliffordPairModule C F) :
    ⟪bilinear φ x y, bilinear φ x' y'⟫_((C × C)ᵐᵒᵖ) =
      moduleTensorPureInner (representation φ) x y x' y' := by
  change MulOpposite.op
      (MulOpposite.unop ⟪interiorModuleTensorMk φ x y.1,
        interiorModuleTensorMk φ x' y'.1⟫_(Cᵐᵒᵖ),
       MulOpposite.unop ⟪interiorModuleTensorMk φ x y.2,
        interiorModuleTensorMk φ x' y'.2⟫_(Cᵐᵒᵖ)) =
    MulOpposite.op
      (MulOpposite.unop ⟪y.1, φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) y'.1⟫_(Cᵐᵒᵖ),
       MulOpposite.unop ⟪y.2, φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) y'.2⟫_(Cᵐᵒᵖ))
  rw [interiorModuleTensorInner_mk_mk, interiorModuleTensorInner_mk_mk]
  rfl

theorem balancedMap_inner (u v : BalancedModuleTensor (E := E) (representation φ)) :
    ⟪balancedMap φ u, balancedMap φ v⟫_((C × C)ᵐᵒᵖ) =
      moduleTensorInner (representation φ) u v := by
  revert v
  refine moduleTensor_induction (representation φ) u ?_ ?_ ?_
  · intro v; simp
  · intro x y v
    refine moduleTensor_induction (representation φ) v ?_ ?_ ?_
    · simp
    · intro x' y'
      rw [balancedMap_mk, balancedMap_mk, moduleTensorInner_mk_mk]
      exact bilinear_inner φ x x' y y'
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hv]

def isometry : Source (E := E) φ →ₗᵢ[ℂ] Target (E := E) φ :=
  InteriorModuleTensorFormCompletion.completedIsometry (representation φ)
    (balancedMap φ) (balancedMap_inner φ)

@[simp] theorem isometry_mk (x : E) (y : CliffordPairModule C F) :
    isometry φ (interiorModuleTensorMk (representation φ) x y) = bilinear φ x y :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x y

theorem isometry_surjective : Function.Surjective (isometry (E := E) φ) := by
  let R : Submodule ℂ (Target (E := E) φ) := (isometry (E := E) φ).toLinearMap.range
  have hR : IsClosed (R : Set (Target (E := E) φ)) :=
    (isometry φ).isometry.isUniformInducing.isComplete_range.isClosed
  have hleft (z : BaseTensor (E := E) φ) : cliffordPairMk (B := C) z 0 ∈ R := by
    let L : BaseTensor (E := E) φ →L[ℂ] Target (E := E) φ := ContinuousLinearMap.inl ℂ _ _
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set (BaseTensor (E := E) φ)) := hR.preimage L.continuous
    have hspan : Submodule.span ℂ
        (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      change cliffordPairMk (B := C) (interiorModuleTensorMk φ x y) 0 ∈ R
      refine ⟨interiorModuleTensorMk (representation φ) x (cliffordPairMk (B := C) y 0), ?_⟩
      change isometry φ (interiorModuleTensorMk (representation φ) x
        (cliffordPairMk (B := C) y 0)) =
          cliffordPairMk (B := C) (interiorModuleTensorMk φ x y) 0
      rw [isometry_mk, bilinear_apply]
      change cliffordPairMk (B := C) (interiorModuleTensorMk φ x y)
        (interiorModuleTensorMk φ x 0) = cliffordPairMk (B := C) (interiorModuleTensorMk φ x y) 0
      rw [map_zero]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  have hright (z : BaseTensor (E := E) φ) : cliffordPairMk (B := C) 0 z ∈ R := by
    let L : BaseTensor (E := E) φ →L[ℂ] Target (E := E) φ := ContinuousLinearMap.inr ℂ _ _
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set (BaseTensor (E := E) φ)) := hR.preimage L.continuous
    have hspan : Submodule.span ℂ
        (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      change cliffordPairMk (B := C) 0 (interiorModuleTensorMk φ x y) ∈ R
      refine ⟨interiorModuleTensorMk (representation φ) x (cliffordPairMk (B := C) 0 y), ?_⟩
      change isometry φ (interiorModuleTensorMk (representation φ) x
        (cliffordPairMk (B := C) 0 y)) =
          cliffordPairMk (B := C) 0 (interiorModuleTensorMk φ x y)
      rw [isometry_mk, bilinear_apply]
      change cliffordPairMk (B := C) (interiorModuleTensorMk φ x 0)
        (interiorModuleTensorMk φ x y) = cliffordPairMk (B := C) 0 (interiorModuleTensorMk φ x y)
      rw [map_zero]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  intro z
  have h := R.add_mem (hleft z.1) (hright z.2)
  have hz : cliffordPairMk (B := C) z.1 0 + cliffordPairMk (B := C) 0 z.2 = z := by
    change (z.1, (0 : BaseTensor (E := E) φ)) + (0, z.2) = (z.1, z.2)
    exact Prod.ext (add_zero _) (zero_add _)
  rw [hz] at h
  exact h

def hilbertEquiv : HilbertModuleEquiv (C × C) (Source (E := E) φ) (Target (E := E) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ) (isometry_surjective φ)
  inner_map := InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (x : E) (y : CliffordPairModule C F) :
    hilbertEquiv φ (interiorModuleTensorMk (representation φ) x y) =
      cliffordPairMk (B := C) (interiorModuleTensorMk φ x y.1) (interiorModuleTensorMk φ x y.2) :=
  isometry_mk φ x y

end BC4lean.KKTheory.CliffordPairSecondTensor
