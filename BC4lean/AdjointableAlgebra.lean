import BC4lean.AdjointableOperator

/-! # Algebra and operator norm of adjointable maps

The norm on adjointable maps is the operator norm of the underlying continuous
linear map. Endomorphisms form a complex normed star algebra, without any
completeness assumption on the module.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

namespace AdjointableMap

instance instZero : Zero (AdjointableMap B E F) := ⟨zero⟩
instance instAdd : Add (AdjointableMap B E F) := ⟨add⟩
instance instNeg : Neg (AdjointableMap B E F) := ⟨fun T => T.smul (-1)⟩

instance instAddCommGroup : AddCommGroup (AdjointableMap B E F) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc S T U := by ext x; exact add_assoc (S x) (T x) (U x)
  zero_add T := by ext x; exact zero_add (T x)
  add_zero T := by ext x; exact add_zero (T x)
  neg_add_cancel T := by
    ext x
    change (-1 : ℂ) • T x + T x = 0
    simp
  add_comm S T := by ext x; exact add_comm (S x) (T x)

instance instSMul : SMul ℂ (AdjointableMap B E F) := ⟨smul⟩

@[simp] theorem toCLM_zero : (0 : AdjointableMap B E F).toCLM = 0 := rfl
@[simp] theorem toCLM_add (S T : AdjointableMap B E F) :
    (S + T).toCLM = S.toCLM + T.toCLM := rfl
@[simp] theorem toCLM_smul (c : ℂ) (T : AdjointableMap B E F) :
    (c • T).toCLM = c • T.toCLM := rfl
@[simp] theorem toCLM_neg (T : AdjointableMap B E F) : (-T).toCLM = -T.toCLM := by
  change (-1 : ℂ) • T.toCLM = -T.toCLM
  simp
@[simp] theorem toCLM_sub (S T : AdjointableMap B E F) :
    (S - T).toCLM = S.toCLM - T.toCLM := by
  simp [sub_eq_add_neg]

@[simp] theorem coe_zero_apply (x : E) : (0 : AdjointableMap B E F) x = 0 := rfl
@[simp] theorem coe_add_apply (S T : AdjointableMap B E F) (x : E) :
    (S + T) x = S x + T x := rfl
@[simp] theorem coe_smul_apply (c : ℂ) (T : AdjointableMap B E F) (x : E) :
    (c • T) x = c • T x := rfl
@[simp] theorem coe_neg_apply (T : AdjointableMap B E F) (x : E) : (-T) x = -T x := by
  exact congrArg (fun f : E →L[ℂ] F => f x) (toCLM_neg T)
@[simp] theorem coe_sub_apply (S T : AdjointableMap B E F) (x : E) :
    (S - T) x = S x - T x := by simp [sub_eq_add_neg]

@[simp] theorem adjointCLM_zero : (0 : AdjointableMap B E F).adjointCLM = 0 := rfl
@[simp] theorem adjointCLM_add (S T : AdjointableMap B E F) :
    (S + T).adjointCLM = S.adjointCLM + T.adjointCLM := rfl
@[simp] theorem adjointCLM_smul (c : ℂ) (T : AdjointableMap B E F) :
    (c • T).adjointCLM = star c • T.adjointCLM := rfl
@[simp] theorem adjointCLM_neg (T : AdjointableMap B E F) :
    (-T).adjointCLM = -T.adjointCLM := by
  change star (-1 : ℂ) • T.adjointCLM = -T.adjointCLM
  simp
@[simp] theorem adjointCLM_sub (S T : AdjointableMap B E F) :
    (S - T).adjointCLM = S.adjointCLM - T.adjointCLM := by
  simp [sub_eq_add_neg]

/-- Forgetting the adjoint is injective. -/
theorem toCLM_injective : Function.Injective (toCLM : AdjointableMap B E F → E →L[ℂ] F) := by
  intro S T h
  apply ext
  intro x
  exact congrArg (fun f : E →L[ℂ] F => f x) h

/-- The additive map forgetting the adjoint. -/
def toCLMAddHom : AdjointableMap B E F →+ (E →L[ℂ] F) where
  toFun := toCLM
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℂ (AdjointableMap B E F) :=
  Function.Injective.module ℂ toCLMAddHom toCLM_injective toCLM_smul

/-- The complex-linear map forgetting the adjoint. -/
def toCLMLinearMap : AdjointableMap B E F →ₗ[ℂ] (E →L[ℂ] F) where
  toFun := toCLM
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance instNormedAddCommGroup : NormedAddCommGroup (AdjointableMap B E F) :=
  NormedAddCommGroup.induced _ _ toCLMAddHom toCLM_injective

instance instNormedSpace : NormedSpace ℂ (AdjointableMap B E F) :=
  NormedSpace.induced ℂ _ _ toCLMLinearMap

/-- The adjointable-map norm is exactly the underlying operator norm. -/
@[simp] theorem norm_def (T : AdjointableMap B E F) : ‖T‖ = ‖T.toCLM‖ := rfl

/-- The underlying operator map is an isometry. -/
theorem toCLM_isometry : Isometry (toCLM : AdjointableMap B E F → E →L[ℂ] F) := by
  apply AddMonoidHomClass.isometry_of_norm toCLMAddHom
  exact fun T => (norm_def T).symm

/-- The continuous complex-linear map forgetting the adjoint. -/
def toCLMContinuousLinearMap : AdjointableMap B E F →L[ℂ] (E →L[ℂ] F) :=
  { toCLMLinearMap with cont := toCLM_isometry.continuous }

@[simp] theorem toCLMContinuousLinearMap_apply (T : AdjointableMap B E F) :
    toCLMContinuousLinearMap T = T.toCLM := rfl

/-- Submultiplicativity of the operator norm for composition. -/
theorem norm_comp_le (S : AdjointableMap B F G) (T : AdjointableMap B E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le S.toCLM T.toCLM

instance instOne : One (AdjointableMap B E E) := ⟨id⟩
instance instMul : Mul (AdjointableMap B E E) := ⟨comp⟩

@[simp] theorem toCLM_one : (1 : AdjointableMap B E E).toCLM = 1 := rfl
@[simp] theorem toCLM_mul (S T : AdjointableMap B E E) :
    (S * T).toCLM = S.toCLM * T.toCLM := rfl
@[simp] theorem one_apply (x : E) : (1 : AdjointableMap B E E) x = x := rfl
@[simp] theorem mul_apply (S T : AdjointableMap B E E) (x : E) :
    (S * T) x = S (T x) := rfl

instance instRing : Ring (AdjointableMap B E E) where
  one := 1
  mul := (· * ·)
  mul_assoc S T U := by ext x; rfl
  one_mul T := id_comp T
  mul_one T := comp_id T
  left_distrib S T U := by ext x; exact S.toCLM.map_add (T x) (U x)
  right_distrib S T U := by ext x; rfl
  zero_mul T := by ext x; rfl
  mul_zero T := by ext x; exact T.toCLM.map_zero

/-- Endomorphisms with the operator norm form a normed ring. -/
instance instNormedRing : NormedRing (AdjointableMap B E E) where
  __ := instNormedAddCommGroup
  __ := instRing
  norm_mul_le := norm_comp_le

instance instAlgebra : Algebra ℂ (AdjointableMap B E E) :=
  Algebra.ofModule
    (fun c S T => by ext x; rfl)
    (fun c S T => by ext x; exact S.toCLM.map_smul c (T x))

instance instNormedAlgebra : NormedAlgebra ℂ (AdjointableMap B E E) where
  norm_smul_le c T := norm_smul_le c T.toCLM

instance instStar : Star (AdjointableMap B E E) := ⟨adjoint⟩

@[simp] theorem star_eq_adjoint (T : AdjointableMap B E E) : star T = T.adjoint := rfl

instance instStarRing : StarRing (AdjointableMap B E E) where
  star_involutive := adjoint_adjoint
  star_mul := adjoint_comp
  star_add := adjoint_add

instance instStarModule : StarModule ℂ (AdjointableMap B E E) where
  star_smul := adjoint_smul

/-- Forgetting the adjoint as a complex algebra homomorphism. -/
def toCLMAlgHom : AdjointableMap B E E →ₐ[ℂ] (E →L[ℂ] E) where
  toFun := toCLM
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    change (c • (1 : AdjointableMap B E E)).toCLM = algebraMap ℂ (E →L[ℂ] E) c
    simp [Algebra.algebraMap_eq_smul_one]

end AdjointableMap
end BC4lean.KKTheory
