import BC4lean.CliffordTensorHom
import BC4lean.CliffordPairModule
import BC4lean.StandardCoefficientImageTensor
import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.InteriorModuleTensorIsometry

/-! # The actual Clifford pair tensor with an arbitrary coefficient map

The standard target module for the coordinate homomorphism is the genuine
opposite of C × C. Its two coordinates balance separately. The diagonal
pure-tensor map preserves both coefficient coordinates, descends through
the null radical, and is onto after completion by pure-tensor density.
No surjectivity of f or unit in either coefficient algebra is used.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordPairStandardTensor
open scoped InnerProductSpace

variable {B C H : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [CompleteSpace H] (f : B →⋆ₙₐ[ℂ] C)

abbrev representation := standardCoefficientImageRepresentation (cliffordCoordinateHom f)
abbrev Source := InteriorModuleTensor (E := CliffordPairModule B H) (representation f)
abbrev Target := CliffordPairModule C
  (InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f))

def firstCoordinate : (C × C)ᵐᵒᵖ →ₗ[ℂ] Cᵐᵒᵖ where
  toFun y := MulOpposite.op (MulOpposite.unop y).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondCoordinate : (C × C)ᵐᵒᵖ →ₗ[ℂ] Cᵐᵒᵖ where
  toFun y := MulOpposite.op (MulOpposite.unop y).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def bilinear : CliffordPairModule B H →ₗ[ℂ] (C × C)ᵐᵒᵖ →ₗ[ℂ] Target (H := H) f where
  toFun x := ((interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.1).comp
      (firstCoordinate (C := C))).prod
    ((interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.2).comp
      (secondCoordinate (C := C)))
  map_add' x z := by
    ext y
    · change interiorModuleTensorMk (E := H) (standardCoefficientImageRepresentation f)
        (x.1 + z.1) (firstCoordinate y) =
        interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.1 (firstCoordinate y) +
          interiorModuleTensorMk (standardCoefficientImageRepresentation f) z.1 (firstCoordinate y)
      exact ((interiorModuleTensorMk (E := H)
        (standardCoefficientImageRepresentation f)).flip (firstCoordinate y)).map_add x.1 z.1
    · change interiorModuleTensorMk (E := H) (standardCoefficientImageRepresentation f)
        (x.2 + z.2) (secondCoordinate y) =
        interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.2 (secondCoordinate y) +
          interiorModuleTensorMk (standardCoefficientImageRepresentation f) z.2 (secondCoordinate y)
      exact ((interiorModuleTensorMk (E := H)
        (standardCoefficientImageRepresentation f)).flip (secondCoordinate y)).map_add x.2 z.2
  map_smul' a x := by
    ext y
    · change interiorModuleTensorMk (E := H) (standardCoefficientImageRepresentation f)
        (a • x.1) (firstCoordinate y) =
        a • interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.1 (firstCoordinate y)
      exact ((interiorModuleTensorMk (E := H)
        (standardCoefficientImageRepresentation f)).flip (firstCoordinate y)).map_smul a x.1
    · change interiorModuleTensorMk (E := H) (standardCoefficientImageRepresentation f)
        (a • x.2) (secondCoordinate y) =
        a • interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.2 (secondCoordinate y)
      exact ((interiorModuleTensorMk (E := H)
        (standardCoefficientImageRepresentation f)).flip (secondCoordinate y)).map_smul a x.2

@[simp] theorem bilinear_apply (x : CliffordPairModule B H) (y : (C × C)ᵐᵒᵖ) :
    bilinear f x y = cliffordPairMk
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.1
        (MulOpposite.op (MulOpposite.unop y).1))
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.2
        (MulOpposite.op (MulOpposite.unop y).2)) := rfl

theorem bilinear_balance (b : B × B) (x : CliffordPairModule B H) (y : (C × C)ᵐᵒᵖ) :
    bilinear f (MulOpposite.op b • x) y = bilinear f x (representation f b y) := by
  apply Prod.ext <;> exact interiorModuleTensorMk_balance
    (standardCoefficientImageRepresentation f) _ _ _

def balancedMap : BalancedModuleTensor (E := CliffordPairModule B H) (representation f) →ₗ[ℂ]
    Target (H := H) f := moduleTensorLift _ (bilinear f) (bilinear_balance f)

@[simp] theorem balancedMap_mk (x : CliffordPairModule B H) (y : (C × C)ᵐᵒᵖ) :
    balancedMap f (moduleTensorMk (representation f) x y) = bilinear f x y := rfl

theorem bilinear_inner (x x' : CliffordPairModule B H) (y y' : (C × C)ᵐᵒᵖ) :
    ⟪bilinear f x y, bilinear f x' y'⟫_((C × C)ᵐᵒᵖ) =
      moduleTensorPureInner (representation f) x y x' y' := by
  apply MulOpposite.unop_injective
  apply Prod.ext <;> change MulOpposite.unop
    ⟪interiorModuleTensorMk (standardCoefficientImageRepresentation f) _ _,
      interiorModuleTensorMk (standardCoefficientImageRepresentation f) _ _⟫_(Cᵐᵒᵖ) = _
  all_goals rw [interiorModuleTensorInner_mk_mk]; rfl

theorem balancedMap_inner (x y : BalancedModuleTensor (E := CliffordPairModule B H)
    (representation f)) :
    ⟪balancedMap f x, balancedMap f y⟫_((C × C)ᵐᵒᵖ) = moduleTensorInner (representation f) x y := by
  revert y
  refine moduleTensor_induction (representation f) x ?_ ?_ ?_
  · intro y; simp
  · intro x z y
    refine moduleTensor_induction (representation f) y ?_ ?_ ?_
    · simp
    · intro x' z'
      rw [balancedMap_mk, balancedMap_mk, moduleTensorInner_mk_mk]
      exact bilinear_inner f x x' z z'
    · intro y z hy hz
      simp only [map_add, CStarModule.inner_add_right, hy, hz]
  · intro x z hx hz y
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hx, hz]

def isometry : Source (H := H) f →ₗᵢ[ℂ] Target (H := H) f :=
  InteriorModuleTensorFormCompletion.completedIsometry _ (balancedMap f) (balancedMap_inner f)

@[simp] theorem isometry_mk (x : CliffordPairModule B H) (y : (C × C)ᵐᵒᵖ) :
    isometry f (interiorModuleTensorMk (representation f) x y) = bilinear f x y :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x y

theorem isometry_surjective : Function.Surjective (isometry (H := H) f) := by
  let R : Submodule ℂ (Target (H := H) f) := (isometry (H := H) f).toLinearMap.range
  have hR : IsClosed (R : Set (Target (H := H) f)) :=
    (isometry f).isometry.isUniformInducing.isComplete_range.isClosed
  have hL (x : H) (y : Cᵐᵒᵖ) : cliffordPairMk
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x y) 0 ∈ R := by
    refine ⟨interiorModuleTensorMk (representation f) (cliffordPairMk x 0)
      (MulOpposite.op (MulOpposite.unop y, 0)), ?_⟩
    change isometry f (interiorModuleTensorMk (representation f) (cliffordPairMk x 0)
      (MulOpposite.op (MulOpposite.unop y, 0))) =
      cliffordPairMk (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x y) 0
    rw [isometry_mk, bilinear_apply]
    change cliffordPairMk
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x y)
      (interiorModuleTensorMk (E := H) (standardCoefficientImageRepresentation f) 0 0) = _
    rw [map_zero]
  have hR' (x : H) (y : Cᵐᵒᵖ) : cliffordPairMk 0
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x y) ∈ R := by
    refine ⟨interiorModuleTensorMk (representation f) (cliffordPairMk 0 x)
      (MulOpposite.op (0, MulOpposite.unop y)), ?_⟩
    change isometry f (interiorModuleTensorMk (representation f) (cliffordPairMk 0 x)
      (MulOpposite.op (0, MulOpposite.unop y))) =
      cliffordPairMk 0 (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x y)
    rw [isometry_mk, bilinear_apply]
    change cliffordPairMk
      (interiorModuleTensorMk (E := H) (standardCoefficientImageRepresentation f) 0 0)
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x y) = _
    rw [map_zero]
  have hleft (z : InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f)) :
      cliffordPairMk z 0 ∈ R := by
    let L : InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f) →L[ℂ]
        Target (H := H) f := ContinuousLinearMap.inl ℂ _ _
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set
        (InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f))) := by
      change IsClosed (L ⁻¹' (R : Set (Target (H := H) f)))
      exact hR.preimage L.continuous
    have hspan : Submodule.span ℂ (Set.range fun p : H × Cᵐᵒᵖ =>
        interiorModuleTensorMk (standardCoefficientImageRepresentation f) p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      exact hL x y
    change z ∈ P
    exact closure_minimal hspan hP
      (interiorModuleTensor_span_dense (standardCoefficientImageRepresentation f) z)
  have hright (z : InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f)) :
      cliffordPairMk 0 z ∈ R := by
    let L : InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f) →L[ℂ]
        Target (H := H) f := ContinuousLinearMap.inr ℂ _ _
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set
        (InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f))) := by
      change IsClosed (L ⁻¹' (R : Set (Target (H := H) f)))
      exact hR.preimage L.continuous
    have hspan : Submodule.span ℂ (Set.range fun p : H × Cᵐᵒᵖ =>
        interiorModuleTensorMk (standardCoefficientImageRepresentation f) p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      exact hR' x y
    change z ∈ P
    exact closure_minimal hspan hP
      (interiorModuleTensor_span_dense (standardCoefficientImageRepresentation f) z)
  intro z
  change z ∈ R
  have hz := R.add_mem (hleft z.1) (hright z.2)
  have heq : (cliffordPairMk z.1 0 + cliffordPairMk 0 z.2 : Target (H := H) f) = z := by
    apply Prod.ext
    · change z.1 + 0 = z.1
      exact add_zero _
    · change 0 + z.2 = z.2
      exact zero_add _
  rw [heq] at hz
  exact hz

def hilbertEquiv : HilbertModuleEquiv (C × C) (Source (H := H) f) (Target (H := H) f) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry f) (isometry_surjective f)
  inner_map := InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (x : CliffordPairModule B H) (y : (C × C)ᵐᵒᵖ) :
    hilbertEquiv f (interiorModuleTensorMk (representation f) x y) = bilinear f x y :=
  isometry_mk f x y

theorem hilbertEquiv_operator (S T : AdjointableMap B H H) (z : Source (H := H) f) :
    hilbertEquiv f (interiorModuleTensorOperator (representation f) (cliffordPairMap S T) z) =
      cliffordPairMap (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) S)
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T) (hilbertEquiv f z) := by
  let W := (hilbertEquiv (H := H) f).toAdjointable.toCLM
  have h : W.comp (interiorModuleTensorOperator (representation f) (cliffordPairMap S T)).toCLM =
      (cliffordPairMap (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) S)
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T)).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [ContinuousLinearMap.comp_apply, W, HilbertModuleEquiv.toAdjointable_apply,
      interiorModuleTensorOperator_mk, hilbertEquiv_mk, bilinear_apply, cliffordPairMap_apply]
    change cliffordPairMk
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) (S x.1) (firstCoordinate y))
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) (T x.2) (secondCoordinate y)) =
      cliffordPairMk
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) S
          (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.1 (firstCoordinate y)))
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T
          (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.2 (secondCoordinate y)))
    rw [interiorModuleTensorOperator_mk, interiorModuleTensorOperator_mk]
  exact DFunLike.congr_fun h z

end BC4lean.KKTheory.CliffordPairStandardTensor
