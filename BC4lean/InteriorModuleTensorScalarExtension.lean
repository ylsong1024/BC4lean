import BC4lean.InteriorModuleTensorAssociatorCompatibility
import BC4lean.InteriorModuleTensorSecondFactorIsometry
import BC4lean.StandardModuleTensorEmbedding
import BC4lean.HilbertModuleCoefficientApproximateUnit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Composition of actual extension of Hilbert-module coefficients



For i : B → D and a genuine representation ρ of D on H, the actual completed
map `(x tensor d) tensor y` to `x tensor ρ(d)y` is a coefficient-form unitary
from `(E tensor_i D) tensor_ρ H` to `E tensor_(ρ ∘ i) H`. Both i and ρ may
be degenerate. The standard tensor evaluation D tensor_ρ H → H is used only
as an isometric embedding. Surjectivity of the outer comparison follows from
the intrinsic right-B approximate unit acting strongly on E. In particular no
surjectivity of the standard evaluation onto all of H is claimed or assumed.

The optional named target representation ψ is required only to equal ρ ∘ i
pointwise; this hypothesis identifies two already given coefficient actions,
and supplies neither a norm estimate nor a desired tensor isometry.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorScalarExtension
open Filter
open scoped InnerProductSpace

variable {B D C E H : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]

variable (i : B →⋆ₙₐ[ℂ] D)
  (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
  (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H)
  (hρ : ∀ b, ρ (i b) = ψ b)

/-- The original coefficients act on the genuine standard D-module. -/
def standardRepresentation : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ :=
  standardLeftMul.comp i

abbrev SourceTensor := InteriorModuleTensor
  (E := InteriorModuleTensor (E := E) (standardRepresentation i)) ρ
abbrev TargetTensor := InteriorModuleTensor (E := E) ψ

/-- Actual standard evaluation, with its pairing and right-linearity proofs,
intertwines the represented original coefficients. This is only an embedding. -/
def secondEmbedding : ModuleTensorSecondFactorIsometry
    (InteriorModuleTensorAssociator.rightRepresentation (standardRepresentation i) ρ) ψ where
  second := StandardModuleTensorEmbedding.isometry ρ
  map_op_smul := StandardModuleTensorEmbedding.isometry_map_op_smul ρ
  inner_map := StandardModuleTensorEmbedding.isometry_inner ρ
  intertwines b z := by
    change StandardModuleTensorEmbedding.isometry ρ
        (interiorModuleTensorOperator ρ (standardLeftMul (i b)) z) =
      ψ b (StandardModuleTensorEmbedding.isometry ρ z)
    rw [StandardModuleTensorEmbedding.isometry_intertwines, hρ]

/-- Reassociation followed by the actual second-factor tensor embedding. -/
def isometry : SourceTensor (E := E) i ρ →ₗᵢ[ℂ] TargetTensor (E := E) ψ :=
  ((secondEmbedding i ρ ψ hρ).interiorIsometry (E := E)).comp
    (InteriorModuleTensorAssociator.hilbertEquiv (E := E)
      (standardRepresentation i) ρ).linearIsometryEquiv.toLinearIsometry

@[simp] theorem isometry_triple (x : E) (d : Dᵐᵒᵖ) (y : H) :
    isometry i ρ ψ hρ
      (interiorModuleTensorMk ρ (interiorModuleTensorMk (standardRepresentation i) x d) y) =
        interiorModuleTensorMk ψ x (ρ (MulOpposite.unop d) y) := by
  change (secondEmbedding i ρ ψ hρ).interiorIsometry
      (InteriorModuleTensorAssociator.hilbertEquiv (standardRepresentation i) ρ
        (interiorModuleTensorMk ρ (interiorModuleTensorMk (standardRepresentation i) x d) y)) = _
  rw [InteriorModuleTensorAssociator.hilbertEquiv_triple,
    ModuleTensorSecondFactorIsometry.interiorIsometry_mk]
  change interiorModuleTensorMk ψ x
    (StandardModuleTensorEmbedding.isometry ρ (interiorModuleTensorMk ρ d y)) = _
  rw [StandardModuleTensorEmbedding.isometry_mk]

theorem isometry_inner (u v : SourceTensor (E := E) i ρ) :
    ⟪isometry i ρ ψ hρ u, isometry i ρ ψ hρ v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) := by
  change ⟪(secondEmbedding i ρ ψ hρ).interiorIsometry
      (InteriorModuleTensorAssociator.hilbertEquiv (standardRepresentation i) ρ u),
    (secondEmbedding i ρ ψ hρ).interiorIsometry
      (InteriorModuleTensorAssociator.hilbertEquiv (standardRepresentation i) ρ v)⟫_(Cᵐᵒᵖ) = _
  rw [ModuleTensorSecondFactorIsometry.interiorIsometry_inner,
    HilbertModuleEquiv.inner_map]

/-- Fixed second-factor elementary tensors depend continuously on their first
vector, with the actual cross-norm bound. -/
def pureCLM (y : H) : E →L[ℂ] TargetTensor (E := E) ψ :=
  ({ toFun := fun x => interiorModuleTensorMk ψ x y
     map_add' := fun x z => by simp
     map_smul' := fun a x => by simp } : E →ₗ[ℂ] TargetTensor (E := E) ψ).mkContinuous ‖y‖
    (fun x => by
      change ‖interiorModuleTensorMk ψ x y‖ ≤ ‖y‖ * ‖x‖
      simpa only [mul_comm] using interiorModuleTensorMk_norm_le ψ x y)

/-- A coefficient-smoothed elementary target vector is an actual image. -/
theorem pure_coefficient_mem_range (x : E) (b : Bᵐᵒᵖ) (y : H) :
    interiorModuleTensorMk ψ (b • x) y ∈ Set.range (isometry (E := E) i ρ ψ hρ) := by
  refine ⟨interiorModuleTensorMk ρ
    (interiorModuleTensorMk (standardRepresentation i) x (MulOpposite.op (i (MulOpposite.unop b)))) y, ?_⟩
  rw [isometry_triple, MulOpposite.unop_op, hρ]
  simpa only [MulOpposite.op_unop] using
    (interiorModuleTensorMk_balance ψ (MulOpposite.unop b) x y).symm

/-- The right-module coefficient AU proves onto-ness of the outer comparison,
without making the degenerate standard evaluation onto H. -/
theorem isometry_surjective :
    Function.Surjective (isometry (E := E) i ρ ψ hρ) := by
  let R : Submodule ℂ (TargetTensor (E := E) ψ) :=
    (isometry (E := E) i ρ ψ hρ).toLinearMap.range
  have hR : IsClosed (R : Set (TargetTensor (E := E) ψ)) :=
    (isometry (E := E) i ρ ψ hρ).isometry.isUniformInducing.isComplete_range.isClosed
  have hpure (x : E) (y : H) : interiorModuleTensorMk ψ x y ∈ R := by
    apply hR.mem_of_tendsto
      (((pureCLM (E := E) ψ y).continuous.tendsto x).comp
        (tendsto_coefficient_approximateUnit_smul (D := Bᵐᵒᵖ) x))
    exact Filter.Eventually.of_forall fun b => pure_coefficient_mem_range i ρ ψ hρ x b y
  have hspan : Submodule.span ℂ
      (Set.range fun p : E × H => interiorModuleTensorMk ψ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,y⟩,rfl⟩
    exact hpure x y
  intro u
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense ψ u)

/-- The actual coefficient-form unitary for composition of coefficient extension. -/
def hilbertEquiv : HilbertModuleEquiv C (SourceTensor (E := E) i ρ)
    (TargetTensor (E := E) ψ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry i ρ ψ hρ)
    (isometry_surjective i ρ ψ hρ)
  inner_map := isometry_inner i ρ ψ hρ

@[simp] theorem hilbertEquiv_triple (x : E) (d : Dᵐᵒᵖ) (y : H) :
    hilbertEquiv i ρ ψ hρ
      (interiorModuleTensorMk ρ (interiorModuleTensorMk (standardRepresentation i) x d) y) =
        interiorModuleTensorMk ψ x (ρ (MulOpposite.unop d) y) :=
  isometry_triple i ρ ψ hρ x d y

/-- Actual twice-amplified first-factor operators are intertwined by the unitary. -/
theorem hilbertEquiv_operator (T : AdjointableMap B E E)
    (u : SourceTensor (E := E) i ρ) :
    hilbertEquiv i ρ ψ hρ
      (interiorModuleTensorOperator ρ
        (interiorModuleTensorOperator (standardRepresentation i) T) u) =
      interiorModuleTensorOperator ψ T (hilbertEquiv i ρ ψ hρ u) := by
  change (secondEmbedding i ρ ψ hρ).interiorIsometry
      (InteriorModuleTensorAssociator.hilbertEquiv (standardRepresentation i) ρ
        (interiorModuleTensorOperator ρ
          (interiorModuleTensorOperator (standardRepresentation i) T) u)) = _
  rw [InteriorModuleTensorAssociator.hilbertEquiv_operator_intertwine,
    ModuleTensorSecondFactorIsometry.interiorIsometry_operator]
  rfl

end BC4lean.KKTheory.InteriorModuleTensorScalarExtension
