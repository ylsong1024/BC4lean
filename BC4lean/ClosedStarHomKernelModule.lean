import BC4lean.StandardModuleOperator
import BC4lean.StandardHilbertModuleActions
import BC4lean.HilbertModuleCountableGenerationSeparable
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # The actual Hilbert module of a closed star-homomorphism kernel

The carrier is the closed kernel inside the standard right module. Its norm
and coefficient inner product are inherited. It need not be complemented.
Left multiplication is restricted by the two-sided kernel law; no compact
restriction theorem for arbitrary closed submodules is used.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {D C : Type*} [CStarAlgebra D] [CStarAlgebra C]
  [PartialOrder D] [StarOrderedRing D]

def starHomKernelSubmodule (χ : D →⋆ₐ[ℂ] C) : Submodule ℂ Dᵐᵒᵖ where
  carrier := {x | χ (MulOpposite.unop x) = 0}
  zero_mem' := map_zero χ
  add_mem' hx hy := by
    change χ (MulOpposite.unop _ + MulOpposite.unop _) = 0
    rw [map_add, hx, hy, add_zero]
  smul_mem' c x hx := by
    change χ (c • MulOpposite.unop x) = 0
    rw [map_smul, hx, smul_zero]

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] theorem mem_starHomKernelSubmodule (χ : D →⋆ₐ[ℂ] C) (x : Dᵐᵒᵖ) :
    x ∈ starHomKernelSubmodule χ ↔ χ (MulOpposite.unop x) = 0 := Iff.rfl

omit [PartialOrder D] [StarOrderedRing D] in
theorem starHomKernelSubmodule_isClosed (χ : D →⋆ₐ[ℂ] C) :
    IsClosed (starHomKernelSubmodule χ : Set Dᵐᵒᵖ) := by
  have hχ : Continuous χ :=
    AddMonoidHomClass.continuous_of_bound χ 1 (fun a => by
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le χ a)
  exact isClosed_eq (hχ.comp MulOpposite.continuous_unop) continuous_const

def StarHomKernelModule (χ : D →⋆ₐ[ℂ] C) := starHomKernelSubmodule χ

namespace StarHomKernelModule
variable (χ : D →⋆ₐ[ℂ] C)

instance instNormedAddCommGroup : NormedAddCommGroup (StarHomKernelModule χ) :=
  inferInstanceAs (NormedAddCommGroup (starHomKernelSubmodule χ))
instance instNormedSpace : NormedSpace ℂ (StarHomKernelModule χ) :=
  inferInstanceAs (NormedSpace ℂ (starHomKernelSubmodule χ))
instance instCompleteSpace : CompleteSpace (StarHomKernelModule χ) :=
  (starHomKernelSubmodule_isClosed χ).isComplete.completeSpace_coe

instance instSMul : SMul Dᵐᵒᵖ (StarHomKernelModule χ) where
  smul b x := ⟨b • (x : Dᵐᵒᵖ), by
    change χ (MulOpposite.unop (x : Dᵐᵒᵖ) * MulOpposite.unop b) = 0
    rw [map_mul, x.property, zero_mul]⟩

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] theorem coe_op_smul (b : Dᵐᵒᵖ) (x : StarHomKernelModule χ) :
    ((b • x : StarHomKernelModule χ) : Dᵐᵒᵖ) = b • (x : Dᵐᵒᵖ) := rfl

instance instCStarModule : CStarModule Dᵐᵒᵖ (StarHomKernelModule χ) where
  inner x y := ⟪(x : Dᵐᵒᵖ), (y : Dᵐᵒᵖ)⟫_(Dᵐᵒᵖ)
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    rw [CStarModule.inner_self]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner x y := CStarModule.star_inner (x : Dᵐᵒᵖ) (y : Dᵐᵒᵖ)
  norm_eq_sqrt_norm_inner_self x :=
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Dᵐᵒᵖ) (x : Dᵐᵒᵖ)

@[simp] theorem inner_coe (x y : StarHomKernelModule χ) :
    ⟪x, y⟫_(Dᵐᵒᵖ) = ⟪(x : Dᵐᵒᵖ), (y : Dᵐᵒᵖ)⟫_(Dᵐᵒᵖ) := rfl
omit [PartialOrder D] [StarOrderedRing D] in
@[simp] theorem norm_coe (x : StarHomKernelModule χ) : ‖(x : Dᵐᵒᵖ)‖ = ‖x‖ := rfl

end StarHomKernelModule

/-- Separability supplies genuine countable generators for the closed kernel. -/
theorem starHomKernelModule_countablyGenerated [TopologicalSpace.SeparableSpace D]
    (χ : D →⋆ₐ[ℂ] C) : IsCountablyGeneratedModule D (StarHomKernelModule χ) := by
  let : TopologicalSpace.SeparableSpace Dᵐᵒᵖ :=
    MulOpposite.op_surjective.denseRange.separableSpace MulOpposite.continuous_op
  let : TopologicalSpace.SeparableSpace (StarHomKernelModule χ) := inferInstance
  exact isCountablyGeneratedModule_of_separableSpace

/-- Every left multiplier preserves the actual two-sided kernel. -/
def starHomKernelLeftMulCLM (χ : D →⋆ₐ[ℂ] C) (a : D) :
    StarHomKernelModule χ →L[ℂ] StarHomKernelModule χ :=
  ((standardLeftMulCLM a).comp (starHomKernelSubmodule χ).subtypeL).codRestrict
    (starHomKernelSubmodule χ) (fun x => by
      change χ (a * MulOpposite.unop (x : Dᵐᵒᵖ)) = 0
      rw [map_mul, x.property, mul_zero])

def starHomKernelLeftMulMap (χ : D →⋆ₐ[ℂ] C) (a : D) :
    AdjointableMap D (StarHomKernelModule χ) (StarHomKernelModule χ) where
  toCLM := starHomKernelLeftMulCLM χ a
  adjointCLM := starHomKernelLeftMulCLM χ (star a)
  adjoint_identity x y := (standardLeftMulMap a).adjoint_identity
    (x : Dᵐᵒᵖ) (y : Dᵐᵒᵖ)

@[simp] theorem starHomKernelLeftMulMap_coe (χ : D →⋆ₐ[ℂ] C) (a : D)
    (x : StarHomKernelModule χ) :
    (starHomKernelLeftMulMap χ a x : Dᵐᵒᵖ) = MulOpposite.op (a * MulOpposite.unop (x : Dᵐᵒᵖ)) := rfl

def starHomKernelLeftMul (χ : D →⋆ₐ[ℂ] C) :
    D →⋆ₙₐ[ℂ] AdjointableMap D (StarHomKernelModule χ) (StarHomKernelModule χ) where
  toFun := starHomKernelLeftMulMap χ
  map_zero' := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    change MulOpposite.op (0 * MulOpposite.unop (x : Dᵐᵒᵖ)) = (0 : Dᵐᵒᵖ)
    simp only [zero_mul, MulOpposite.op_zero]
  map_add' a b := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    change MulOpposite.op ((a + b) * MulOpposite.unop (x : Dᵐᵒᵖ)) = _
    simp only [add_mul, MulOpposite.op_add]
    rfl
  map_mul' a b := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    exact congrArg MulOpposite.op (mul_assoc a b (MulOpposite.unop (x : Dᵐᵒᵖ)))
  map_smul' c a := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    change MulOpposite.op ((c • a) * MulOpposite.unop (x : Dᵐᵒᵖ)) = _
    simp only [smul_mul_assoc, MulOpposite.op_smul]
    rfl
  map_star' a := by
    apply AdjointableMap.ext
    intro x
    rfl

@[simp] theorem starHomKernelLeftMul_apply (χ : D →⋆ₐ[ℂ] C) (a : D)
    (x : StarHomKernelModule χ) :
    (starHomKernelLeftMul χ a x : Dᵐᵒᵖ) = MulOpposite.op (a * MulOpposite.unop (x : Dᵐᵒᵖ)) := rfl

theorem norm_starHomKernelLeftMul_le (χ : D →⋆ₐ[ℂ] C) (a : D) :
    ‖starHomKernelLeftMul χ a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖a * MulOpposite.unop (x : Dᵐᵒᵖ)‖ ≤ ‖a‖ * ‖MulOpposite.unop (x : Dᵐᵒᵖ)‖
  exact norm_mul_le _ _

def starHomKernelLeftMulContinuous (χ : D →⋆ₐ[ℂ] C) :
    D →L[ℂ] AdjointableMap D (StarHomKernelModule χ) (StarHomKernelModule χ) :=
  ({ toFun := starHomKernelLeftMul χ
     map_add' := map_add (starHomKernelLeftMul χ)
     map_smul' := map_smul (starHomKernelLeftMul χ) } :
    D →ₗ[ℂ] AdjointableMap D (StarHomKernelModule χ) (StarHomKernelModule χ)).mkContinuous
    1 (fun a => by
      change ‖starHomKernelLeftMul χ a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using norm_starHomKernelLeftMul_le χ a)

/-- Rank ones on the kernel are actual left multiplications by xy*, with
both vectors in the genuine kernel. -/
theorem starHomKernelRankOne_eq_leftMul (χ : D →⋆ₐ[ℂ] C)
    (x y : StarHomKernelModule χ) :
    moduleRankOne (B := D) x y =
      starHomKernelLeftMul χ (MulOpposite.unop (x : Dᵐᵒᵖ) * star (MulOpposite.unop (y : Dᵐᵒᵖ))) := by
  apply AdjointableMap.ext
  intro z
  apply Subtype.ext
  exact congrArg (fun T : AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ => T (z : Dᵐᵒᵖ))
    (standard_moduleRankOne_eq_leftMul (x : Dᵐᵒᵖ) (y : Dᵐᵒᵖ))

/-- A coefficient automorphism preserving the quotient restricts to a genuine
semilinear isometry of the kernel; complementation is unnecessary. -/
def starHomKernelIsometryEquiv (χ : D →⋆ₐ[ℂ] C) (e : D ≃⋆ₐ[ℂ] D)
    (hχ : ∀ a, χ (e a) = χ a) : StarHomKernelModule χ ≃ₗᵢ[ℂ] StarHomKernelModule χ where
  toFun x := ⟨opStarAlgEquiv e (x : Dᵐᵒᵖ), by
    change χ (e (MulOpposite.unop (x : Dᵐᵒᵖ))) = 0
    rw [hχ, x.property]⟩
  invFun x := ⟨opStarAlgEquiv e.symm (x : Dᵐᵒᵖ), by
    have h := hχ (e.symm (MulOpposite.unop (x : Dᵐᵒᵖ)))
    rw [e.apply_symm_apply, x.property] at h
    exact h.symm⟩
  left_inv x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact e.symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact e.apply_symm_apply _
  map_add' x y := by apply Subtype.ext; exact map_add (opStarAlgEquiv e) _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul (opStarAlgEquiv e) c _
  norm_map' x := StarAlgEquiv.norm_map (opStarAlgEquiv e) (x : Dᵐᵒᵖ)

@[simp] theorem starHomKernelIsometryEquiv_coe (χ : D →⋆ₐ[ℂ] C)
    (e : D ≃⋆ₐ[ℂ] D) (hχ : ∀ a, χ (e a) = χ a) (x : StarHomKernelModule χ) :
    (starHomKernelIsometryEquiv χ e hχ x : Dᵐᵒᵖ) = opStarAlgEquiv e (x : Dᵐᵒᵖ) := rfl

end BC4lean.KKTheory
