import BC4lean.GradedMatrixMoritaCompletion
import BC4lean.InteriorModuleTensorAssociatorCompatibility
import BC4lean.RightStandardModuleTensor

/-! # Actual second-factor tensor transport by correspondence unitaries

An already constructed Hilbert-module unitary intertwining two left actions
induces an actual unitary of the interior tensors. Balancing, the entire
coefficient form, radical descent, completion and onto-ness are all proved.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaTensorUnitary
open scoped InnerProductSpace

variable {B C E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C G G)
  (u : HilbertModuleEquiv C F G) (hu : ∀ b y, u (φ b y) = ψ b (u y))

def bilinear : E →ₗ[ℂ] F →ₗ[ℂ] InteriorModuleTensor (E := E) ψ where
  toFun x := (interiorModuleTensorMk ψ x).comp u.linearIsometryEquiv.toLinearEquiv.toLinearMap
  map_add' x y := by ext z; simp
  map_smul' a x := by ext z; simp

include hu in
theorem bilinear_balance (b : B) (x : E) (y : F) :
    bilinear ψ u (MulOpposite.op b • x) y = bilinear ψ u x (φ b y) := by
  let _retainedCompleteF : CompleteSpace F := inferInstance
  change interiorModuleTensorMk ψ (MulOpposite.op b • x) (u y) =
    interiorModuleTensorMk ψ x (u (φ b y))
  rw [interiorModuleTensorMk_balance, hu]

def balancedMap : BalancedModuleTensor (E := E) φ →ₗ[ℂ] InteriorModuleTensor (E := E) ψ :=
  moduleTensorLift φ (bilinear ψ u) (bilinear_balance φ ψ u hu)

@[simp] theorem balancedMap_mk (x : E) (y : F) :
    balancedMap φ ψ u hu (moduleTensorMk φ x y) = interiorModuleTensorMk ψ x (u y) := rfl

theorem balancedMap_inner (x y : BalancedModuleTensor (E := E) φ) :
    ⟪balancedMap φ ψ u hu x, balancedMap φ ψ u hu y⟫_(Cᵐᵒᵖ) = moduleTensorInner φ x y := by
  revert y
  refine moduleTensor_induction φ x ?_ ?_ ?_
  · intro y
    simp [CStarModule.inner_zero_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := E) ψ)]
  · intro x z y
    refine moduleTensor_induction φ y ?_ ?_ ?_
    · simp [CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := E) ψ)]
    · intro x' z'
      rw [balancedMap_mk, balancedMap_mk, interiorModuleTensorInner_mk_mk,
        moduleTensorInner_mk_mk]
      unfold moduleTensorPureInner
      rw [← hu, u.inner_map]
    · intro y z hy hz
      simp only [map_add,
        CStarModule.inner_add_right (A := Cᵐᵒᵖ)
          (E := InteriorModuleTensor (E := E) ψ), hy, hz]
  · intro x z hx hz y
    simp only [map_add, LinearMap.add_apply,
      CStarModule.inner_add_left (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := E) ψ), hx, hz]

def isometry : InteriorModuleTensor (E := E) φ →ₗᵢ[ℂ] InteriorModuleTensor (E := E) ψ :=
  GradedMatrixMoritaCompletion.completedIsometry φ (balancedMap φ ψ u hu)
    (balancedMap_inner φ ψ u hu)

@[simp] theorem isometry_mk (x : E) (y : F) :
    isometry φ ψ u hu (interiorModuleTensorMk φ x y) = interiorModuleTensorMk ψ x (u y) :=
  GradedMatrixMoritaCompletion.completedIsometry_mk (B := B) (C := C)
    (E := E) (F := F) (H := InteriorModuleTensor (E := E) ψ)
    φ (balancedMap φ ψ u hu) (balancedMap_inner φ ψ u hu) x y

theorem isometry_surjective : Function.Surjective (isometry (E := E) φ ψ u hu) := by
  let R := (isometry (E := E) φ ψ u hu).toLinearMap.range
  have hR : IsClosed (R : Set (InteriorModuleTensor (E := E) ψ)) :=
    (isometry (E := E) φ ψ u hu).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ (Set.range fun p : E × G => interiorModuleTensorMk ψ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    refine ⟨interiorModuleTensorMk φ x (u.symm y), ?_⟩
    change isometry (E := E) φ ψ u hu
      (interiorModuleTensorMk φ x (u.symm y)) = interiorModuleTensorMk ψ x y
    rw [isometry_mk, HilbertModuleEquiv.apply_symm_apply]
  intro y
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense ψ y)

def hilbertEquiv : HilbertModuleEquiv C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) ψ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ ψ u hu)
    (isometry_surjective φ ψ u hu)
  inner_map := GradedMatrixMoritaCompletion.completedIsometry_inner (B := B) (C := C)
    (E := E) (F := F) (H := InteriorModuleTensor (E := E) ψ)
    φ (balancedMap φ ψ u hu) (balancedMap_inner φ ψ u hu)

@[simp] theorem hilbertEquiv_mk (x : E) (y : F) :
    hilbertEquiv φ ψ u hu (interiorModuleTensorMk φ x y) = interiorModuleTensorMk ψ x (u y) :=
  isometry_mk φ ψ u hu x y

theorem hilbertEquiv_operator (T : AdjointableMap B E E) (x : InteriorModuleTensor (E := E) φ) :
    hilbertEquiv φ ψ u hu (interiorModuleTensorOperator φ T x) =
      interiorModuleTensorOperator ψ T (hilbertEquiv φ ψ u hu x) := by
  let L := (hilbertEquiv (E := E) φ ψ u hu).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (interiorModuleTensorOperator φ T).toCLM =
      (interiorModuleTensorOperator ψ T).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B) (C := C) (E := E) (F := F) (φ := φ)
    intro x y
    change hilbertEquiv (E := E) φ ψ u hu
      (interiorModuleTensorOperator φ T (interiorModuleTensorMk φ x y)) =
        interiorModuleTensorOperator ψ T
          (hilbertEquiv (E := E) φ ψ u hu (interiorModuleTensorMk φ x y))
    simp only [interiorModuleTensorOperator_mk, hilbertEquiv_mk]
  exact DFunLike.congr_fun h x

end BC4lean.KKTheory.GradedMatrixMoritaTensorUnitary
