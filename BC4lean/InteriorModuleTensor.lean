import BC4lean.PreHilbertModuleTensor
import BC4lean.HilbertModuleCompletion

/-! # The actual completed interior Hilbert-module tensor

The interior tensor is the genuine norm completion of the constructed
separated pre-Hilbert tensor. The generic Hilbert-module completion theorem
provides its extended coefficient inner product and action. Elementary tensors
have their expected pairing, balancing law and norm bound, and their complex
span is dense in this actual complete module.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open UniformSpace

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The actual interior Hilbert-module tensor, constructed by norm completion. -/
abbrev InteriorModuleTensor (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :=
  Completion (PreHilbertModuleTensor (E := E) φ)

/-- The canonical dense isometric embedding of the separated tensor. -/
def moduleTensorToCompletion (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    PreHilbertModuleTensor (E := E) φ →ₗᵢ[ℂ] InteriorModuleTensor (E := E) φ :=
  hilbertModuleToCompletion

/-- The canonical bilinear elementary tensor in the actual completed module. -/
def interiorModuleTensorMk (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    E →ₗ[ℂ] F →ₗ[ℂ] InteriorModuleTensor (E := E) φ :=
  (preModuleTensorMk φ).compr₂ (moduleTensorToCompletion φ).toLinearMap

@[simp] theorem interiorModuleTensorMk_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (y : F) :
    interiorModuleTensorMk φ x y = moduleTensorToCompletion φ (preModuleTensorMk φ x y) := rfl

/-- The constructed interior tensor is an actual complete Hilbert C-module. -/
theorem interiorModuleTensor_complete
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    CompleteSpace (InteriorModuleTensor (E := E) φ) := inferInstance

/-- The completed elementary tensors retain the expected coefficient pairing. -/
@[simp] theorem interiorModuleTensorInner_mk_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y y' : F) :
    ⟪interiorModuleTensorMk φ x y, interiorModuleTensorMk φ x' y'⟫_(Cᵐᵒᵖ) =
      moduleTensorPureInner φ x y x' y' := by
  exact hilbertModuleToCompletion_inner (preModuleTensorMk φ x y) (preModuleTensorMk φ x' y')

/-- Actual coefficient balancing in the completed interior tensor. -/
theorem interiorModuleTensorMk_balance
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (x : E) (y : F) :
    interiorModuleTensorMk φ (MulOpposite.op b • x) y =
      interiorModuleTensorMk φ x (φ b y) :=
  congrArg (moduleTensorToCompletion φ) (preModuleTensorMk_balance φ b x y)

/-- The completed tensor retains the elementary cross-norm bound. -/
theorem interiorModuleTensorMk_norm_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (y : F) :
    ‖interiorModuleTensorMk φ x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [interiorModuleTensorMk_apply, (moduleTensorToCompletion φ).norm_map]
  exact preModuleTensorMk_norm_le φ x y

/-- The actual right coefficient action on completed elementary tensors. -/
@[simp] theorem interiorModuleTensor_smul_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) (x : E) (y : F) :
    a • interiorModuleTensorMk φ x y = interiorModuleTensorMk φ x (a • y) := by
  exact (hilbertModuleToCompletion_op_smul a (preModuleTensorMk φ x y)).symm

/-- The complex span of actual completed elementary tensors is dense. -/
theorem interiorModuleTensor_span_dense
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    Dense ((Submodule.span ℂ
      (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2)) :
        Set (InteriorModuleTensor (E := E) φ)) := by
  apply (hilbertModuleToCompletion_denseRange
    (E := PreHilbertModuleTensor (E := E) φ)).mono
  rintro _ ⟨u, rfl⟩
  change moduleTensorToCompletion φ u ∈ Submodule.span ℂ
    (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2)
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · simpa only [map_zero] using (Submodule.span ℂ _).zero_mem
  · intro x y
    exact Submodule.subset_span ⟨(x, y), rfl⟩
  · intro v w hv hw
    simpa only [map_add] using (Submodule.span ℂ _).add_mem hv hw

end BC4lean.KKTheory
