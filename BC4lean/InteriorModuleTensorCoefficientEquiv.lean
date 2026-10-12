import BC4lean.HilbertModuleCoefficientEquiv
import BC4lean.GradedMatrixMoritaCompletion

/-! # Actual simultaneous coefficient-change interior-tensor unitary

Changing the intermediate algebra by a star equivalence and the final
coefficient algebra by another one gives an actual tensor unitary. The
reverse map is built on balanced tensors, preserves their whole coefficient
form, descends through the actual radical, extends to the completion, and
has closed dense range. The forward map is its constructed inverse.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorCoefficientEquiv
open scoped InnerProductSpace

variable {B B' C C' E F : Type*}
  [NonUnitalCStarAlgebra B] [_originalPartialB : PartialOrder B] [_originalStarOrderB : StarOrderedRing B]
  [NonUnitalCStarAlgebra B'] [_originalPartialB' : PartialOrder B'] [_originalStarOrderB' : StarOrderedRing B']
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [_originalCompleteF : CompleteSpace F]
  (eB : B ≃⋆ₐ[ℂ] B') (eC : C ≃⋆ₐ[ℂ] C')
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

def leftAction : B' →⋆ₙₐ[ℂ]
    AdjointableMap C' (CoefficientChangedModule eC F) (CoefficientChangedModule eC F) :=
  ((coefficientChangedOperatorHom eC).comp φ).comp eB.symm.toNonUnitalStarAlgHom

@[simp] theorem leftAction_apply (b : B') (y : CoefficientChangedModule eC F) :
    leftAction eB eC φ b y = φ (eB.symm b) (y : F) := by
  let _retainedPartialB := _originalPartialB
  let _retainedStarOrderB := _originalStarOrderB
  let _retainedPartialB' := _originalPartialB'
  let _retainedStarOrderB' := _originalStarOrderB'
  let _retainedCompleteF := _originalCompleteF
  rfl

abbrev ChangedTensor := CoefficientChangedModule eC (InteriorModuleTensor (E := E) φ)
abbrev TensorChangedFactors := InteriorModuleTensor
  (E := CoefficientChangedModule eB E) (leftAction eB eC φ)

def reverseBilinear : CoefficientChangedModule eB E →ₗ[ℂ]
    CoefficientChangedModule eC F →ₗ[ℂ] ChangedTensor (E := E) eC φ where
  toFun x :=
    { toFun y := coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
        (interiorModuleTensorMk (E := E) (F := F) φ
          (coefficientChangedToOriginal (M := E) eB x)
          (coefficientChangedToOriginal (M := F) eC y))
      map_add' y z := by
        change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
            (interiorModuleTensorMk (E := E) (F := F) φ
              (coefficientChangedToOriginal (M := E) eB x)
              (coefficientChangedToOriginal (M := F) eC y +
                coefficientChangedToOriginal (M := F) eC z)) =
          coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
            (interiorModuleTensorMk (E := E) (F := F) φ
              (coefficientChangedToOriginal (M := E) eB x)
              (coefficientChangedToOriginal (M := F) eC y)) +
          coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
            (interiorModuleTensorMk (E := E) (F := F) φ
              (coefficientChangedToOriginal (M := E) eB x)
              (coefficientChangedToOriginal (M := F) eC z))
        simp only [map_add]
      map_smul' a y := by
        change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
            (interiorModuleTensorMk (E := E) (F := F) φ
              (coefficientChangedToOriginal (M := E) eB x)
              (a • coefficientChangedToOriginal (M := F) eC y)) =
          a • coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
            (interiorModuleTensorMk (E := E) (F := F) φ
              (coefficientChangedToOriginal (M := E) eB x)
              (coefficientChangedToOriginal (M := F) eC y))
        simp only [map_smul] }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
        (interiorModuleTensorMk (E := E) (F := F) φ
          (coefficientChangedToOriginal (M := E) eB x +
            coefficientChangedToOriginal (M := E) eB z)
          (coefficientChangedToOriginal (M := F) eC y)) =
      coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
        (interiorModuleTensorMk (E := E) (F := F) φ
          (coefficientChangedToOriginal (M := E) eB x)
          (coefficientChangedToOriginal (M := F) eC y)) +
      coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
        (interiorModuleTensorMk (E := E) (F := F) φ
          (coefficientChangedToOriginal (M := E) eB z)
          (coefficientChangedToOriginal (M := F) eC y))
    simp only [map_add, LinearMap.add_apply]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
        (interiorModuleTensorMk (E := E) (F := F) φ
          (a • coefficientChangedToOriginal (M := E) eB x)
          (coefficientChangedToOriginal (M := F) eC y)) =
      a • coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
        (interiorModuleTensorMk (E := E) (F := F) φ
          (coefficientChangedToOriginal (M := E) eB x)
          (coefficientChangedToOriginal (M := F) eC y))
    simp only [map_smul, LinearMap.smul_apply]

theorem reverseBilinear_balance (b : B') (x : CoefficientChangedModule eB E)
    (y : CoefficientChangedModule eC F) :
    reverseBilinear eB eC φ (MulOpposite.op b • x) y =
      reverseBilinear eB eC φ x (leftAction eB eC φ b y) := by
  let _retainedPartialB' := _originalPartialB'
  let _retainedStarOrderB' := _originalStarOrderB'
  change coefficientChangedLinearIsometry eC
    (interiorModuleTensorMk (E := E) (F := F) φ (MulOpposite.op (eB.symm b) • (coefficientChangedToOriginal (M := E) eB x)) (coefficientChangedToOriginal (M := F) eC y)) =
      coefficientChangedLinearIsometry eC
        (interiorModuleTensorMk (E := E) (F := F) φ (coefficientChangedToOriginal (M := E) eB x) (φ (eB.symm b) (coefficientChangedToOriginal (M := F) eC y)))
  rw [interiorModuleTensorMk_balance]

def reverseBalanced : BalancedModuleTensor (E := CoefficientChangedModule eB E)
    (leftAction eB eC φ) →ₗ[ℂ] ChangedTensor (E := E) eC φ :=
  moduleTensorLift (leftAction eB eC φ) (reverseBilinear eB eC φ)
    (reverseBilinear_balance eB eC φ)

@[simp] theorem reverseBalanced_mk (x : CoefficientChangedModule eB E)
    (y : CoefficientChangedModule eC F) :
    reverseBalanced eB eC φ (moduleTensorMk (leftAction eB eC φ) x y) =
      coefficientChangedLinearIsometry eC (interiorModuleTensorMk (E := E) (F := F) φ (x : E) (y : F)) := rfl

theorem reverseBalanced_inner
    (u v : BalancedModuleTensor (E := CoefficientChangedModule eB E) (leftAction eB eC φ)) :
    ⟪reverseBalanced eB eC φ u, reverseBalanced eB eC φ v⟫_(C'ᵐᵒᵖ) =
      moduleTensorInner (leftAction eB eC φ) u v := by
  revert v
  refine moduleTensor_induction (E := CoefficientChangedModule eB E)
    (leftAction eB eC φ) u ?_ ?_ ?_
  · intro v
    simp [CStarModule.inner_zero_left (A := C'ᵐᵒᵖ)
      (E := ChangedTensor (E := E) eC φ)]
  · intro x y v
    refine moduleTensor_induction (E := CoefficientChangedModule eB E)
      (leftAction eB eC φ) v ?_ ?_ ?_
    · simp [CStarModule.inner_zero_right (A := C'ᵐᵒᵖ)
        (E := ChangedTensor (E := E) eC φ)]
    · intro x' y'
      rw [reverseBalanced_mk, reverseBalanced_mk, moduleTensorInner_mk_mk]
      change opStarAlgEquivBetween eC
        ⟪interiorModuleTensorMk (E := E) (F := F) φ (coefficientChangedToOriginal (M := E) eB x) (coefficientChangedToOriginal (M := F) eC y),
          interiorModuleTensorMk (E := E) (F := F) φ (coefficientChangedToOriginal (M := E) eB x') (coefficientChangedToOriginal (M := F) eC y')⟫_(Cᵐᵒᵖ) =
        opStarAlgEquivBetween eC ⟪(coefficientChangedToOriginal (M := F) eC y),
          φ (eB.symm (eB (MulOpposite.unop ⟪(coefficientChangedToOriginal (M := E) eB x), (coefficientChangedToOriginal (M := E) eB x')⟫_(Bᵐᵒᵖ)))) (coefficientChangedToOriginal (M := F) eC y')⟫_(Cᵐᵒᵖ)
      rw [interiorModuleTensorInner_mk_mk, eB.symm_apply_apply]
      rfl
    · intro v w hv hw
      simp only [map_add,
        CStarModule.inner_add_right (A := C'ᵐᵒᵖ)
          (E := ChangedTensor (E := E) eC φ), hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply,
      CStarModule.inner_add_left (A := C'ᵐᵒᵖ)
        (E := ChangedTensor (E := E) eC φ), hu, hv]

def reverseIsometry : TensorChangedFactors (E := E) eB eC φ →ₗᵢ[ℂ] ChangedTensor (E := E) eC φ :=
  GradedMatrixMoritaCompletion.completedIsometry (leftAction eB eC φ)
    (reverseBalanced eB eC φ) (reverseBalanced_inner eB eC φ)

@[simp] theorem reverseIsometry_mk (x : CoefficientChangedModule eB E)
    (y : CoefficientChangedModule eC F) :
    reverseIsometry eB eC φ (interiorModuleTensorMk (leftAction eB eC φ) x y) =
      coefficientChangedLinearIsometry eC (interiorModuleTensorMk (E := E) (F := F) φ (x : E) (y : F)) :=
  GradedMatrixMoritaCompletion.completedIsometry_mk (B := B') (C := C')
    (E := CoefficientChangedModule eB E) (F := CoefficientChangedModule eC F)
    (H := ChangedTensor (E := E) eC φ) (leftAction eB eC φ)
    (reverseBalanced eB eC φ) (reverseBalanced_inner eB eC φ) x y

theorem reverseIsometry_surjective : Function.Surjective (reverseIsometry (E := E) eB eC φ) := by
  let R := (reverseIsometry (E := E) eB eC φ).toLinearMap.range
  have hR : IsClosed (R : Set (ChangedTensor (E := E) eC φ)) :=
    (reverseIsometry (E := E) eB eC φ).isometry.isClosedEmbedding.isClosed_range
  let P := R.comap (coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC).toLinearMap
  have hP : IsClosed (P : Set (InteriorModuleTensor (E := E) φ)) :=
    hR.preimage (coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC).continuous
  have hspan : Submodule.span ℂ (Set.range fun p : E × F => interiorModuleTensorMk (E := E) (F := F) φ p.1 p.2) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    refine ⟨interiorModuleTensorMk (E := CoefficientChangedModule eB E)
      (F := CoefficientChangedModule eC F) (leftAction eB eC φ)
      (coefficientChangedLinearIsometry (M := E) eB x)
      (coefficientChangedLinearIsometry (M := F) eC y), ?_⟩
    change reverseIsometry (E := E) eB eC φ
      (interiorModuleTensorMk (E := CoefficientChangedModule eB E)
        (F := CoefficientChangedModule eC F) (leftAction eB eC φ)
        (coefficientChangedLinearIsometry (M := E) eB x)
        (coefficientChangedLinearIsometry (M := F) eC y)) =
      coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
        (interiorModuleTensorMk (E := E) (F := F) φ x y)
    exact reverseIsometry_mk eB eC φ _ _
  intro z
  change z ∈ R
  exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ (z : InteriorModuleTensor (E := E) φ))

def reverseHilbertEquiv : HilbertModuleEquiv C' (TensorChangedFactors (E := E) eB eC φ) (ChangedTensor (E := E) eC φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (reverseIsometry eB eC φ)
    (reverseIsometry_surjective eB eC φ)
  inner_map := GradedMatrixMoritaCompletion.completedIsometry_inner (B := B') (C := C')
    (E := CoefficientChangedModule eB E) (F := CoefficientChangedModule eC F)
    (H := ChangedTensor (E := E) eC φ) (leftAction eB eC φ)
    (reverseBalanced eB eC φ) (reverseBalanced_inner eB eC φ)

@[simp] theorem reverseHilbertEquiv_mk (x : CoefficientChangedModule eB E)
    (y : CoefficientChangedModule eC F) :
    reverseHilbertEquiv eB eC φ (interiorModuleTensorMk (leftAction eB eC φ) x y) =
      coefficientChangedLinearIsometry eC (interiorModuleTensorMk (E := E) (F := F) φ (x : E) (y : F)) :=
  reverseIsometry_mk eB eC φ x y

def hilbertEquiv : HilbertModuleEquiv C' (ChangedTensor (E := E) eC φ) (TensorChangedFactors (E := E) eB eC φ) :=
  (reverseHilbertEquiv eB eC φ).symm

@[simp] theorem hilbertEquiv_mk (x : E) (y : F) :
    hilbertEquiv eB eC φ (coefficientChangedLinearIsometry eC (interiorModuleTensorMk φ x y)) =
      interiorModuleTensorMk (leftAction eB eC φ)
        (coefficientChangedLinearIsometry eB x) (coefficientChangedLinearIsometry eC y) := by
  apply (reverseHilbertEquiv eB eC φ).injective
  change reverseHilbertEquiv (E := E) eB eC φ
      ((reverseHilbertEquiv (E := E) eB eC φ).symm
        (coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
          (interiorModuleTensorMk (E := E) (F := F) φ x y))) =
    reverseHilbertEquiv (E := E) eB eC φ
      (interiorModuleTensorMk (E := CoefficientChangedModule eB E)
        (F := CoefficientChangedModule eC F) (leftAction eB eC φ)
        (coefficientChangedLinearIsometry (M := E) eB x)
        (coefficientChangedLinearIsometry (M := F) eC y))
  rw [HilbertModuleEquiv.apply_symm_apply, reverseHilbertEquiv_mk]
  rfl

end BC4lean.KKTheory.InteriorModuleTensorCoefficientEquiv
