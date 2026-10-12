import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.InteriorModuleTensorIsometry
import BC4lean.ModuleTensorOperator

/-! # A completed interior tensor unitary from a first-factor unitary

The map x tensor y to u(x) tensor y preserves the complete coefficient form,
annihilates the actual null radical, and extends isometrically to completion.
Pure-tensor density proves surjectivity. Operator intertwining follows on
pure tensors and extends by continuity.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorFirstFactorEquiv
open scoped InnerProductSpace

variable {B C E G F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace G] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (u : HilbertModuleEquiv B E G)

def bilinear : E →ₗ[ℂ] F →ₗ[ℂ] InteriorModuleTensor (E := G) φ :=
  (interiorModuleTensorMk (E := G) φ).comp u.linearIsometryEquiv.toLinearEquiv.toLinearMap

omit [CompleteSpace E] in
theorem bilinear_balance (b : B) (x : E) (y : F) :
    bilinear φ u (MulOpposite.op b • x) y = bilinear φ u x (φ b y) := by
  change interiorModuleTensorMk φ (u (MulOpposite.op b • x)) y =
    interiorModuleTensorMk φ (u x) (φ b y)
  rw [u.map_op_smul, interiorModuleTensorMk_balance]

def balancedMap : BalancedModuleTensor (E := E) φ →ₗ[ℂ] InteriorModuleTensor (E := G) φ :=
  moduleTensorLift φ (bilinear φ u) (bilinear_balance φ u)

omit [CompleteSpace E] in
@[simp] theorem balancedMap_mk (x : E) (y : F) :
    balancedMap φ u (moduleTensorMk φ x y) = interiorModuleTensorMk φ (u x) y := rfl

omit [CompleteSpace E] in
theorem balancedMap_inner (x y : BalancedModuleTensor (E := E) φ) :
    ⟪balancedMap φ u x, balancedMap φ u y⟫_(Cᵐᵒᵖ) = moduleTensorInner φ x y := by
  revert y
  refine moduleTensor_induction φ x ?_ ?_ ?_
  · intro y
    simp only [map_zero, LinearMap.zero_apply]
    exact CStarModule.inner_zero_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := G) φ)
  · intro x z y
    refine moduleTensor_induction φ y ?_ ?_ ?_
    · simp only [map_zero]
      exact CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := G) φ)
    · intro x' z'
      rw [balancedMap_mk, balancedMap_mk, interiorModuleTensorInner_mk_mk,
        moduleTensorInner_mk_mk]
      unfold moduleTensorPureInner
      rw [u.inner_map]
    · intro y z hy hz
      simp only [map_add]
      rw [CStarModule.inner_add_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := G) φ), hy, hz]
  · intro x z hx hz y
    simp only [map_add, LinearMap.add_apply]
    rw [CStarModule.inner_add_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := G) φ), hx y, hz y]

def isometry : InteriorModuleTensor (E := E) φ →ₗᵢ[ℂ] InteriorModuleTensor (E := G) φ :=
  InteriorModuleTensorFormCompletion.completedIsometry φ (balancedMap φ u) (balancedMap_inner φ u)

@[simp] theorem isometry_mk (x : E) (y : F) :
    isometry φ u (interiorModuleTensorMk φ x y) = interiorModuleTensorMk φ (u x) y :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x y

theorem isometry_surjective : Function.Surjective (isometry φ u) := by
  let R : Submodule ℂ (InteriorModuleTensor (E := G) φ) := (isometry φ u).toLinearMap.range
  have hR : IsClosed (R : Set (InteriorModuleTensor (E := G) φ)) :=
    (isometry φ u).isometry.isUniformInducing.isComplete_range.isClosed
  have hspan : Submodule.span ℂ (Set.range fun p : G × F => interiorModuleTensorMk φ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    refine ⟨interiorModuleTensorMk φ (u.symm x) y, ?_⟩
    change isometry φ u (interiorModuleTensorMk φ (u.symm x) y) =
      interiorModuleTensorMk φ x y
    rw [isometry_mk, HilbertModuleEquiv.apply_symm_apply]
  intro z
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense φ z)

def hilbertEquiv : HilbertModuleEquiv C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := G) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ u) (isometry_surjective φ u)
  inner_map := InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (x : E) (y : F) :
    hilbertEquiv φ u (interiorModuleTensorMk φ x y) = interiorModuleTensorMk φ (u x) y :=
  isometry_mk φ u x y

theorem hilbertEquiv_operator (S : AdjointableMap B E E) (T : AdjointableMap B G G)
    (hST : ∀ x, u (S x) = T (u x)) (z : InteriorModuleTensor (E := E) φ) :
    hilbertEquiv φ u (interiorModuleTensorOperator φ S z) =
      interiorModuleTensorOperator φ T (hilbertEquiv φ u z) := by
  let L := (hilbertEquiv φ u).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (interiorModuleTensorOperator φ S).toCLM =
      (interiorModuleTensorOperator φ T).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ u
        (interiorModuleTensorOperator φ S (interiorModuleTensorMk φ x y)) =
      interiorModuleTensorOperator φ T
        (hilbertEquiv φ u (interiorModuleTensorMk φ x y))
    rw [interiorModuleTensorOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk,
      interiorModuleTensorOperator_mk, hST]
  change L (interiorModuleTensorOperator φ S z) =
    interiorModuleTensorOperator φ T (L z)
  exact DFunLike.congr_fun h z

end BC4lean.KKTheory.InteriorModuleTensorFirstFactorEquiv
