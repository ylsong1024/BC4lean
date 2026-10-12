import BC4lean.GradedMatrixMoritaEvaluatedTensorExtension
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # Fibre evaluation in the second interior-tensor variable

The first module is fixed over B and the second is an arbitrary module
over C(X,C). Its actual B representation descends by the fibre operator
homomorphism. Evaluation x ⊗ y ↦ x ⊗ fibreMk_t(y) proves the whole pairing,
descends and completes. No extension to a C(X,B) representation is used.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaSecondFibreTensor
open scoped InnerProductSpace

variable {B C X E M : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, C)ᵐᵒᵖ M]
  [CStarModule C(X, C)ᵐᵒᵖ M] [CompleteSpace E] [CompleteSpace M]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C(X, C) M M) (t : X)

def fibreRepresentation : B →⋆ₙₐ[ℂ]
    AdjointableMap C (HilbertModuleFibre C M t) (HilbertModuleFibre C M t) :=
  (hilbertModuleFibreOperatorHom (B := C) (M := M) t).toNonUnitalStarAlgHom.comp φ

omit [PartialOrder B] [StarOrderedRing B] [T2Space X] in
@[simp] theorem fibreRepresentation_mk (b : B) (y : M) :
    fibreRepresentation φ t b (hilbertModuleFibreMk (B := C) t y) =
      hilbertModuleFibreMk (B := C) t (φ b y) := hilbertModuleFibreOperator_mk t (φ b) y

def bilinear : E →ₗ[ℂ] M →ₗ[ℂ]
    InteriorModuleTensor (E := E) (fibreRepresentation φ t) where
  toFun x := (interiorModuleTensorMk (fibreRepresentation φ t) x).comp
    (hilbertModuleFibreMk (B := C) (M := M) t).toLinearMap
  map_add' x y := by ext z; simp
  map_smul' a x := by ext z; simp

omit [T2Space X] in
theorem bilinear_balance (b : B) (x : E) (y : M) :
    bilinear φ t (MulOpposite.op b • x) y = bilinear φ t x (φ b y) := by
  change interiorModuleTensorMk (fibreRepresentation φ t) (MulOpposite.op b • x)
    (hilbertModuleFibreMk (B := C) t y) =
      interiorModuleTensorMk (fibreRepresentation φ t) x (hilbertModuleFibreMk (B := C) t (φ b y))
  rw [interiorModuleTensorMk_balance, fibreRepresentation_mk]

def balancedEvaluation : BalancedModuleTensor (E := E) φ →ₗ[ℂ]
    InteriorModuleTensor (E := E) (fibreRepresentation φ t) :=
  moduleTensorLift φ (bilinear φ t) (bilinear_balance φ t)

omit [T2Space X] in
@[simp] theorem balancedEvaluation_mk (x : E) (y : M) :
    balancedEvaluation φ t (moduleTensorMk φ x y) =
      interiorModuleTensorMk (fibreRepresentation φ t) x (hilbertModuleFibreMk (B := C) t y) := rfl

omit [T2Space X] in
theorem balancedEvaluation_inner (u v : BalancedModuleTensor (E := E) φ) :
    ⟪balancedEvaluation φ t u, balancedEvaluation φ t v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop (moduleTensorInner φ u v) t) := by
  revert v
  refine moduleTensor_induction φ u ?_ ?_ ?_
  · intro v
    simp [CStarModule.inner_zero_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := E) (fibreRepresentation φ t))]
  · intro x y v
    refine moduleTensor_induction φ v ?_ ?_ ?_
    · simp [CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := E) (fibreRepresentation φ t))]
    · intro x' y'
      rw [balancedEvaluation_mk, balancedEvaluation_mk, interiorModuleTensorInner_mk_mk,
        moduleTensorInner_mk_mk]
      unfold moduleTensorPureInner
      rw [fibreRepresentation_mk, hilbertModuleFibre_inner_mk]
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right (A := Cᵐᵒᵖ)
          (E := InteriorModuleTensor (E := E) (fibreRepresentation φ t)),
        MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := E) (fibreRepresentation φ t)),
      MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hu, hv]

def evaluation : InteriorModuleTensor (E := E) φ →L[ℂ]
    InteriorModuleTensor (E := E) (fibreRepresentation φ t) :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM φ t
    (balancedEvaluation φ t) (balancedEvaluation_inner φ t)

omit [T2Space X] in
@[simp] theorem evaluation_mk (x : E) (y : M) :
    evaluation φ t (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk (fibreRepresentation φ t) x (hilbertModuleFibreMk (B := C) t y) :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM_mk _ _ _ _ x y

omit [T2Space X] in
theorem evaluation_inner (u v : InteriorModuleTensor (E := E) φ) :
    ⟪evaluation φ t u, evaluation φ t v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪u, v⟫_(C(X, C)ᵐᵒᵖ) t) :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM_inner _ _ _ _ u v

omit [T2Space X] in
theorem evaluation_norm_le (u : InteriorModuleTensor (E := E) φ) : ‖evaluation φ t u‖ ≤ ‖u‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) (evaluation φ t u),
    evaluation_inner]
  change Real.sqrt ‖MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ) t‖ ≤ ‖u‖
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := C(X, C)ᵐᵒᵖ) u]
  exact Real.sqrt_le_sqrt ((MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ)).norm_coe_le_norm t)

def fibreIsometry : HilbertModuleFibre C (InteriorModuleTensor (E := E) φ) t →ₗᵢ[ℂ]
    InteriorModuleTensor (E := E) (fibreRepresentation φ t) :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry t (evaluation φ t) (evaluation_inner φ t)

omit [T2Space X] in
@[simp] theorem fibreIsometry_mk (u : InteriorModuleTensor (E := E) φ) :
    fibreIsometry φ t (hilbertModuleFibreMk (B := C) t u) = evaluation φ t u :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry_mk _ _ _ u

theorem fibreIsometry_surjective : Function.Surjective (fibreIsometry (E := E) φ t) := by
  let R := (fibreIsometry (E := E) φ t).toLinearMap.range
  have hR : IsClosed (R : Set (InteriorModuleTensor (E := E) (fibreRepresentation φ t))) :=
    (fibreIsometry φ t).isometry.isUniformInducing.isComplete_range.isClosed
  have hspan : Submodule.span ℂ (Set.range fun p : E × HilbertModuleFibre C M t =>
      interiorModuleTensorMk (fibreRepresentation φ t) p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    obtain ⟨z, rfl⟩ := hilbertModuleFibreMk_surjective (B := C) (M := M) t y
    refine ⟨hilbertModuleFibreMk (B := C) t (interiorModuleTensorMk φ x z), ?_⟩
    change fibreIsometry φ t
      (hilbertModuleFibreMk (B := C) t (interiorModuleTensorMk φ x z)) =
        interiorModuleTensorMk (fibreRepresentation φ t) x (hilbertModuleFibreMk (B := C) t z)
    rw [fibreIsometry_mk, evaluation_mk]
  intro z
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense (fibreRepresentation φ t) z)

def hilbertEquiv : HilbertModuleEquiv C
    (HilbertModuleFibre C (InteriorModuleTensor (E := E) φ) t)
    (InteriorModuleTensor (E := E) (fibreRepresentation φ t)) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (fibreIsometry φ t)
    (fibreIsometry_surjective φ t)
  inner_map := GradedMatrixMoritaFibreEvaluation.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (u : InteriorModuleTensor (E := E) φ) :
    hilbertEquiv φ t (hilbertModuleFibreMk (B := C) t u) = evaluation φ t u :=
  fibreIsometry_mk φ t u

@[simp] theorem hilbertEquiv_tensor_mk (x : E) (y : M) :
    hilbertEquiv φ t (hilbertModuleFibreMk (B := C) t (interiorModuleTensorMk φ x y)) =
      interiorModuleTensorMk (fibreRepresentation φ t) x (hilbertModuleFibreMk (B := C) t y) := by
  rw [hilbertEquiv_mk, evaluation_mk]

end BC4lean.KKTheory.GradedMatrixMoritaSecondFibreTensor
