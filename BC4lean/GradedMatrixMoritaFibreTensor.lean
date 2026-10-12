import BC4lean.GradedMatrixMoritaSectionRepresentation
import BC4lean.GradedMatrixMoritaFibreEvaluation

/-! # Actual evaluation of an interior tensor on sections

The map x ⊗ s ↦ fibreMk_t(x) ⊗ s(t) is constructed on the balanced
tensor, proves the entire evaluated coefficient pairing, descends through
the tensor null space and extends contractively. Its induced fibre map
is an isometry. The actual fibre quotient theorem and constant sections
put all pure target tensors in its range, proving it is onto.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaFibreTensor
open scoped InnerProductSpace

variable {B C X E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul C(X, B)ᵐᵒᵖ E]
  [CStarModule C(X, B)ᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (t : X)

abbrev SectionsTensor := InteriorModuleTensor (E := E)
  (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)
abbrev EvaluatedTensor := InteriorModuleTensor (E := HilbertModuleFibre B E t) φ

def bilinear : E →ₗ[ℂ] C(X, F) →ₗ[ℂ] EvaluatedTensor (E := E) φ t where
  toFun x := (interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x)).comp
    (continuousSectionEvaluation (E := F) t).toLinearMap
  map_add' x y := by
    ext s
    change interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t (x + y)) (s t) =
      interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x) (s t) +
        interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t y) (s t)
    rw [(hilbertModuleFibreMk (B := B) (M := E) t).map_add x y]
    exact LinearMap.congr_fun ((interiorModuleTensorMk φ).map_add _ _) (s t)
  map_smul' z x := by ext s; simp

theorem bilinear_balance {B C X E F : Type*}
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul C(X, B)ᵐᵒᵖ E]
    [CStarModule C(X, B)ᵐᵒᵖ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
    [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (t : X)
    (b : C(X, B)) (x : E) (s : C(X, F)) :
    bilinear φ t (MulOpposite.op b • x) s = bilinear φ t x
      (GradedMatrixMoritaSectionRepresentation.leftAction φ b s) := by
  change interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t (MulOpposite.op b • x)) (s t) =
    interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x) (φ (b t) (s t))
  rw [hilbertModuleFibreMk_op_smul, interiorModuleTensorMk_balance, MulOpposite.unop_op]

def balancedEvaluation : BalancedModuleTensor (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) →ₗ[ℂ]
      EvaluatedTensor (E := E) φ t :=
  moduleTensorLift _ (bilinear φ t) (bilinear_balance φ t)

@[simp] theorem balancedEvaluation_mk (x : E) (s : C(X, F)) :
    balancedEvaluation φ t (moduleTensorMk _ x s) =
      interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x) (s t) := rfl

/-- The pairing identity holds for the entire balanced tensor, not only pure tensors. -/
theorem balancedEvaluation_inner (u v : BalancedModuleTensor (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)) :
    ⟪balancedEvaluation φ t u, balancedEvaluation φ t v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop
        (moduleTensorInner (E := E) (F := C(X, F))
          (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) u v) t) := by
  revert v
  refine moduleTensor_induction (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) u ?_ ?_ ?_
  · intro v
    simp [CStarModule.inner_zero_left (A := Cᵐᵒᵖ)
      (E := EvaluatedTensor (E := E) φ t)]
  · intro x s v
    refine moduleTensor_induction (E := E)
      (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) v ?_ ?_ ?_
    · simp [CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := EvaluatedTensor (E := E) φ t)]
    · intro y r
      rw [balancedEvaluation_mk, balancedEvaluation_mk, interiorModuleTensorInner_mk_mk,
        moduleTensorInner_mk_mk]
      unfold moduleTensorPureInner
      rw [hilbertModuleFibre_inner_mk]
      rfl
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right (A := Cᵐᵒᵖ)
          (E := EvaluatedTensor (E := E) φ t),
        MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left (A := Cᵐᵒᵖ)
        (E := EvaluatedTensor (E := E) φ t),
      MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hu, hv]

def preEvaluation : PreHilbertModuleTensor (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) →ₗ[ℂ]
      EvaluatedTensor (E := E) φ t :=
  (moduleTensorNull _).liftQ (balancedEvaluation φ t) (by
    intro u hu
    apply (CStarModule.inner_self (A := Cᵐᵒᵖ)).mp
    rw [balancedEvaluation_inner, (mem_moduleTensorNull_iff _ u).mp hu]
    rfl)

theorem preEvaluation_inner (u v : PreHilbertModuleTensor (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)) :
    ⟪preEvaluation φ t u, preEvaluation φ t v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪u, v⟫_(C(X, C)ᵐᵒᵖ) t) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact balancedEvaluation_inner φ t u v

theorem preEvaluation_norm_le (u : PreHilbertModuleTensor (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)) :
    ‖preEvaluation φ t u‖ ≤ ‖u‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)
    (E := EvaluatedTensor (E := E) φ t) (preEvaluation φ t u), preEvaluation_inner]
  change Real.sqrt ‖MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ) t‖ ≤ ‖u‖
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := C(X, C)ᵐᵒᵖ)
    (E := PreHilbertModuleTensor (E := E)
      (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)) u]
  exact Real.sqrt_le_sqrt ((MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ)).norm_coe_le_norm t)

def preEvaluationCLM : PreHilbertModuleTensor (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) →L[ℂ]
      EvaluatedTensor (E := E) φ t :=
  (preEvaluation φ t).mkContinuous 1
    (fun u => by simpa only [one_mul] using preEvaluation_norm_le φ t u)

def evaluation : SectionsTensor (X := X) (E := E) φ →L[ℂ] EvaluatedTensor (E := E) φ t :=
  (preEvaluationCLM φ t).fromCompletion

@[simp] theorem evaluation_coe (u : PreHilbertModuleTensor (E := E)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)) :
    evaluation φ t (moduleTensorToCompletion _ u) = preEvaluation φ t u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

@[simp] theorem evaluation_mk (x : E) (s : C(X, F)) :
    evaluation φ t (interiorModuleTensorMk _ x s) =
      interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x) (s t) :=
  evaluation_coe φ t (preModuleTensorMk _ x s)

theorem evaluation_inner (u v : SectionsTensor (X := X) (E := E) φ) :
    ⟪evaluation φ t u, evaluation φ t v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪u, v⟫_(C(X, C)ᵐᵒᵖ) t) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp =>
    have hi : Continuous (fun p : SectionsTensor (X := X) (E := E) φ ×
        SectionsTensor (X := X) (E := E) φ => ⟪p.1, p.2⟫_(C(X, C)ᵐᵒᵖ)) :=
      CStarModule.continuous_inner (A := C(X, C)ᵐᵒᵖ)
        (E := SectionsTensor (X := X) (E := E) φ)
    have he : Continuous (fun a : C(X, C)ᵐᵒᵖ =>
        MulOpposite.op ((MulOpposite.unop a) t)) := by fun_prop
    exact isClosed_eq
      ((CStarModule.continuous_inner (A := Cᵐᵒᵖ)
        (E := EvaluatedTensor (E := E) φ t)).comp
        (((evaluation φ t).continuous.comp continuous_fst).prodMk
          ((evaluation φ t).continuous.comp continuous_snd))) (he.comp hi)
  | ih u v =>
    change ⟪evaluation φ t (moduleTensorToCompletion _ u),
      evaluation φ t (moduleTensorToCompletion _ v)⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop
        ⟪moduleTensorToCompletion _ u, moduleTensorToCompletion _ v⟫_(C(X, C)ᵐᵒᵖ) t)
    rw [evaluation_coe, evaluation_coe]
    change ⟪preEvaluation φ t u, preEvaluation φ t v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop
        ⟪hilbertModuleToCompletion u, hilbertModuleToCompletion v⟫_(C(X, C)ᵐᵒᵖ) t)
    rw [hilbertModuleToCompletion_inner]
    exact preEvaluation_inner φ t u v

theorem evaluation_norm_le (u : SectionsTensor (X := X) (E := E) φ) : ‖evaluation φ t u‖ ≤ ‖u‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)
    (E := EvaluatedTensor (E := E) φ t) (evaluation φ t u), evaluation_inner]
  change Real.sqrt ‖MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ) t‖ ≤ ‖u‖
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := C(X, C)ᵐᵒᵖ)
    (E := SectionsTensor (X := X) (E := E) φ) u]
  exact Real.sqrt_le_sqrt ((MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ)).norm_coe_le_norm t)

def fibreIsometry : HilbertModuleFibre C (SectionsTensor (X := X) (E := E) φ) t →ₗᵢ[ℂ]
    EvaluatedTensor (E := E) φ t :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry t (evaluation φ t) (evaluation_inner φ t)

@[simp] theorem fibreIsometry_mk (u : SectionsTensor (X := X) (E := E) φ) :
    fibreIsometry φ t (hilbertModuleFibreMk (B := C) t u) = evaluation φ t u :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry_mk _ _ _ u

/-- Onto-ness uses the actual quotient surjectivity and actual pure tensor density. -/
theorem fibreIsometry_surjective : Function.Surjective (fibreIsometry (E := E) φ t) := by
  let R := (fibreIsometry (E := E) φ t).toLinearMap.range
  have hR : IsClosed (R : Set (EvaluatedTensor (E := E) φ t)) :=
    (fibreIsometry φ t).isometry.isUniformInducing.isComplete_range.isClosed
  have hspan : Submodule.span ℂ (Set.range fun p : HilbertModuleFibre B E t × F =>
      interiorModuleTensorMk φ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    obtain ⟨z, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := E) t x
    refine ⟨hilbertModuleFibreMk (B := C) t
      (interiorModuleTensorMk _ z (ContinuousMap.const X y)), ?_⟩
    change fibreIsometry φ t (hilbertModuleFibreMk (B := C) t
      (interiorModuleTensorMk
        (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) z
          (ContinuousMap.const X y))) =
        interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t z) y
    rw [fibreIsometry_mk, evaluation_mk]
    rfl
  intro z
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense φ z)

/-- Evaluation commutes with the actual completed interior tensor. -/
def hilbertEquiv : HilbertModuleEquiv C
    (HilbertModuleFibre C (SectionsTensor (X := X) (E := E) φ) t) (EvaluatedTensor (E := E) φ t) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (fibreIsometry φ t)
    (fibreIsometry_surjective φ t)
  inner_map := GradedMatrixMoritaFibreEvaluation.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (u : SectionsTensor (X := X) (E := E) φ) :
    hilbertEquiv φ t (hilbertModuleFibreMk (B := C) t u) = evaluation φ t u :=
  fibreIsometry_mk φ t u

@[simp] theorem hilbertEquiv_tensor_mk (x : E) (s : C(X, F)) :
    hilbertEquiv φ t (hilbertModuleFibreMk (B := C) t (interiorModuleTensorMk _ x s)) =
      interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x) (s t) := by
  rw [hilbertEquiv_mk, evaluation_mk]

end BC4lean.KKTheory.GradedMatrixMoritaFibreTensor
