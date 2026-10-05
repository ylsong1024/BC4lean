import BC4lean.HilbertCStarModule
import BC4lean.CountablyGeneratedModule
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Completion of a right Hilbert C⋆-module

The norm completion carries the genuine coefficient-valued inner product. The
right coefficient action is the completion of its bounded complex-linear map;
the inner product is the dense extension of the original additive bilinear
map. Continuity of that extension and closed-set induction prove every module
law. No completeness of the original module, or unit in the coefficient
algebra, is required.
-/

noncomputable section
namespace BC4lean.KKTheory

open UniformSpace
open scoped InnerProductSpace
open CStarModule

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

private theorem coefficient_smul_complex (a : Bᵐᵒᵖ) (c : ℂ) (x : E) :
    a • (c • x) = c • (a • x) := by
  apply module_inner_ext_right (B := B)
  intro y
  simp only [inner_op_smul_right, inner_smul_right_complex, mul_smul_comm]

/-- The coefficient action as its actual bounded complex-linear operator. -/
def completionCoefficientAction (a : Bᵐᵒᵖ) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => a • x
      map_add' := module_smul_add a
      map_smul' := fun c x => coefficient_smul_complex a c x }
    ‖a‖ (module_norm_smul_le a)

@[simp] theorem completionCoefficientAction_apply (a : Bᵐᵒᵖ) (x : E) :
    completionCoefficientAction a x = a • x := rfl

/-- Extend the right coefficient action to the actual norm completion. -/
instance completionModuleSMul : SMul Bᵐᵒᵖ (Completion E) where
  smul a x := (completionCoefficientAction (E := E) a).completion x

@[simp] theorem completion_op_smul_coe (a : Bᵐᵒᵖ) (x : E) :
    a • (x : Completion E) = ((a • x : E) : Completion E) :=
  (completionCoefficientAction a).completion_apply_coe x

instance completionModuleUniformContinuousConstSMul :
    UniformContinuousConstSMul Bᵐᵒᵖ (Completion E) where
  uniformContinuous_const_smul a := (completionCoefficientAction a).completion.uniformContinuous

@[fun_prop] theorem continuous_completion_op_smul (a : Bᵐᵒᵖ) :
    Continuous (fun x : Completion E => a • x) :=
  (completionCoefficientAction a).completion.continuous

variable [StarOrderedRing B]

/-- The dense extension of the original coefficient-valued inner product. -/
def completionInner (x y : Completion E) : Bᵐᵒᵖ :=
  (Completion.isDenseInducing_coe.prodMap Completion.isDenseInducing_coe).extend
    (fun p : E × E => ⟪p.1, p.2⟫_(Bᵐᵒᵖ)) (x, y)

instance completionModuleInner : Inner Bᵐᵒᵖ (Completion E) where
  inner := completionInner

@[simp] theorem completionInner_coe (x y : E) :
    ⟪(x : Completion E), (y : Completion E)⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) :=
  (Completion.isDenseInducing_coe.prodMap Completion.isDenseInducing_coe).extend_eq
    CStarModule.continuous_inner (x, y)

@[simp] theorem completionInner_apply_coe (x y : E) :
    completionInner (B := B) (x : Completion E) (y : Completion E) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := completionInner_coe x y

/-- Additive bilinear dense extension supplies joint continuity. -/
@[fun_prop] theorem continuous_completionInner :
    Continuous (fun p : Completion E × Completion E => ⟪p.1, p.2⟫_(Bᵐᵒᵖ)) := by
  let inner' : E →+ E →+ Bᵐᵒᵖ :=
    { toFun := fun x => (CStarModule.innerₛₗ (A := Bᵐᵒᵖ) x).toAddMonoidHom
      map_zero' := by ext x; exact CStarModule.inner_zero_left
      map_add' := fun x y => by ext z; exact CStarModule.inner_add_left }
  have h : Continuous (fun p : E × E => inner' p.1 p.2) :=
    CStarModule.continuous_inner
  change Continuous
    (((Completion.isDenseInducing_toCompl E).prodMap
      (Completion.isDenseInducing_toCompl E)).extend fun p : E × E => inner' p.1 p.2)
  exact (Completion.isDenseInducing_toCompl E).extend_Z_bilin
    (Completion.isDenseInducing_toCompl E) h

@[fun_prop] theorem continuous_completionInner_comp {X : Type*} [TopologicalSpace X]
    {f g : X → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => ⟪f x, g x⟫_(Bᵐᵒᵖ)) :=
  continuous_completionInner.comp (hf.prodMk hg)

@[fun_prop] theorem continuous_completionInner_fn :
    Continuous (fun p : Completion E × Completion E => completionInner (B := B) p.1 p.2) :=
  continuous_completionInner

@[fun_prop] theorem continuous_completionInner_apply {X : Type*} [TopologicalSpace X]
    {f g : X → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => completionInner (B := B) (f x) (g x)) :=
  continuous_completionInner_fn.comp (hf.prodMk hg)

/-- The inherited completion norm is precisely the Hilbert-module norm. -/
theorem completion_norm_eq_sqrt_inner (x : Completion E) :
    ‖x‖ = Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    simpa only [Completion.norm_coe, completionInner_coe] using
      (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x)

private theorem completion_inner_self_nonneg (x : Completion E) :
    0 ≤ ⟪x, x⟫_(Bᵐᵒᵖ) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (by fun_prop)
  | ih x =>
    simpa only [completionInner_coe] using
      (CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (x := x))

/-- The actual completed coefficient-valued Hilbert-module structure. -/
instance completionCStarModule : CStarModule Bᵐᵒᵖ (Completion E) where
  inner := completionInner
  inner_add_right {x y z} := by
    induction x, y, z using Completion.induction_on₃ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y z =>
      simp only [← Completion.coe_add, completionInner_apply_coe, CStarModule.inner_add_right]
  inner_self_nonneg := completion_inner_self_nonneg _
  inner_self {x} := by
    constructor
    · intro h
      apply norm_eq_zero.mp
      rw [completion_norm_eq_sqrt_inner (B := B)]
      change Real.sqrt ‖completionInner (B := B) x x‖ = 0
      rw [h, norm_zero, Real.sqrt_zero]
    · intro h
      subst x
      have h := completionInner_apply_coe (B := B) (0 : E) 0
      simpa only [Completion.coe_zero, CStarModule.inner_zero_left] using h
  inner_op_smul_right {a x y} := by
    induction x, y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq
        (continuous_completionInner_apply continuous_fst
          ((continuous_completion_op_smul a).comp continuous_snd))
        (continuous_const.mul continuous_completionInner_fn)
    | ih x y =>
      simp only [completion_op_smul_coe, completionInner_apply_coe,
        CStarModule.inner_op_smul_right]
  inner_smul_right_complex {z x y} := by
    induction x, y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq
        (continuous_completionInner_apply continuous_fst (continuous_snd.const_smul z))
        (continuous_completionInner_fn.const_smul z)
    | ih x y =>
      simp only [← Completion.coe_smul z y, completionInner_apply_coe,
        CStarModule.inner_smul_right_complex]
  star_inner x y := by
    induction x, y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq continuous_completionInner_fn.star
        (continuous_completionInner_apply continuous_snd continuous_fst)
    | ih x y =>
      simp only [completionInner_apply_coe, CStarModule.star_inner]
  norm_eq_sqrt_norm_inner_self := completion_norm_eq_sqrt_inner

/-- The original module embeds isometrically with dense range in its completion. -/
def hilbertModuleToCompletion : E →ₗᵢ[ℂ] Completion E := Completion.toComplₗᵢ

@[simp] theorem hilbertModuleToCompletion_apply (x : E) :
    hilbertModuleToCompletion x = (x : Completion E) := rfl

theorem hilbertModuleToCompletion_denseRange :
    DenseRange (hilbertModuleToCompletion (E := E)) :=
  Completion.denseRange_coe

omit [StarOrderedRing B] in
@[simp] theorem hilbertModuleToCompletion_op_smul (a : Bᵐᵒᵖ) (x : E) :
    hilbertModuleToCompletion (a • x) = a • hilbertModuleToCompletion x :=
  (completion_op_smul_coe a x).symm

@[simp] theorem hilbertModuleToCompletion_inner (x y : E) :
    ⟪hilbertModuleToCompletion x, hilbertModuleToCompletion y⟫_(Bᵐᵒᵖ) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := completionInner_coe x y

/-- Dense coefficient generation survives the actual Hilbert-module completion. -/
theorem IsCountablyGeneratedModule.completion (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B (Completion E) := by
  obtain ⟨ξ, hξ⟩ := hE
  refine ⟨fun n => hilbertModuleToCompletion (ξ n), ?_⟩
  have hm : ∀ x ∈ moduleGeneratingSpan (B := B) ξ,
      hilbertModuleToCompletion x ∈
        moduleGeneratingSpan (B := B) (fun n => hilbertModuleToCompletion (ξ n)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      rw [hilbertModuleToCompletion_op_smul]
      exact smul_mem_moduleGeneratingSpan _ n b
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c hx
  exact ((hilbertModuleToCompletion_denseRange (E := E)).dense_image
    hilbertModuleToCompletion.continuous hξ).mono (by
      rintro y ⟨x, hx, rfl⟩
      exact hm x hx)

end BC4lean.KKTheory
