import BC4lean.HilbertModuleEquiv
import BC4lean.HilbertModuleCountableGenerationSeparable
import Mathlib.Analysis.Normed.Module.Shrink
import Mathlib.Logic.Small.Basic
import Mathlib.Topology.MetricSpace.Kuratowski
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! # Actual small models of separable Hilbert modules

The Kuratowski embedding into a real sequence space proves that a separable
metric space has a model in every chosen universe. Mathlib transfers the
normed complex vector space to that model. The actual right coefficient
action and entire coefficient-valued form are transported along the chosen
equivalence. Its down/up maps are whole Hilbert-module unitaries, preserving
completeness and countable generation. No smallness premise is needed for a
countably generated module over separable coefficients.
-/

noncomputable section
universe uB uE v
namespace BC4lean.KKTheory
open scoped InnerProductSpace

theorem smallOfSeparableMetric (E : Type uE) [MetricSpace E]
    [TopologicalSpace.SeparableSpace E] : Small.{v} E :=
  small_of_injective (kuratowskiEmbedding.isometry E).injective

def shrinkLinearIsometryEquiv {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [Small.{v} E] : Shrink.{v} E ≃ₗᵢ[ℂ] E :=
  { toLinearEquiv := (equivShrink E).symm.linearEquiv ℂ
    norm_map' _ := rfl }

instance shrinkCompleteSpace {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [Small.{v} E] [CompleteSpace E] :
    CompleteSpace (Shrink.{v} E) :=
  (shrinkLinearIsometryEquiv (E := E)).toIsometryEquiv.completeSpace

variable {B : Type uB} {E : Type uE}
  [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

theorem IsCountablyGeneratedModule.small [TopologicalSpace.SeparableSpace B]
    (h : IsCountablyGeneratedModule B E) : Small.{v} E := by
  let : TopologicalSpace.SeparableSpace E := h.separableSpace
  exact smallOfSeparableMetric E

variable [Small.{v} E]

instance shrinkHilbertModuleOpSMul : SMul Bᵐᵒᵖ (Shrink.{v} E) :=
  (equivShrink E).symm.smul Bᵐᵒᵖ

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem shrinkHilbertModule_op_smul_down (b : Bᵐᵒᵖ) (x : Shrink.{v} E) :
    (equivShrink E).symm (b • x) = b • (equivShrink E).symm x :=
  (equivShrink E).symm.apply_symm_apply _

instance shrinkHilbertModuleCStarModule : CStarModule Bᵐᵒᵖ (Shrink.{v} E) where
  inner x y := ⟪(equivShrink E).symm x, (equivShrink E).symm y⟫_(Bᵐᵒᵖ)
  inner_add_right := by
    intro x y z
    change ⟪(equivShrink E).symm x,
      (equivShrink E).symm ((equivShrink E)
        ((equivShrink E).symm y + (equivShrink E).symm z))⟫_(Bᵐᵒᵖ) = _
    rw [Equiv.symm_apply_apply, CStarModule.inner_add_right]
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro h
      have hx := (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp h
      apply (equivShrink E).symm.injective
      exact hx.trans ((shrinkLinearIsometryEquiv (E := E)).map_zero).symm
    · intro h
      rw [h]
      change ⟪(equivShrink E).symm ((equivShrink E) 0),
        (equivShrink E).symm ((equivShrink E) 0)⟫_(Bᵐᵒᵖ) = 0
      rw [Equiv.symm_apply_apply, CStarModule.inner_zero_left]
  inner_op_smul_right := by
    intro b x y
    rw [shrinkHilbertModule_op_smul_down, CStarModule.inner_op_smul_right]
  inner_smul_right_complex := by
    intro z x y
    change ⟪(equivShrink E).symm x,
      (equivShrink E).symm ((equivShrink E)
        (z • (equivShrink E).symm y))⟫_(Bᵐᵒᵖ) = _
    rw [Equiv.symm_apply_apply, CStarModule.inner_smul_right_complex]
  star_inner x y := CStarModule.star_inner _ _
  norm_eq_sqrt_norm_inner_self x :=
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) ((equivShrink E).symm x)

def hilbertModuleShrinkDown : HilbertModuleEquiv B (Shrink.{v} E) E where
  linearIsometryEquiv := shrinkLinearIsometryEquiv
  inner_map _ _ := rfl

def hilbertModuleShrinkUp : HilbertModuleEquiv B E (Shrink.{v} E) :=
  (hilbertModuleShrinkDown (B := B) (E := E)).symm

@[simp] theorem hilbertModuleShrinkDown_apply (x : Shrink.{v} E) :
    hilbertModuleShrinkDown (B := B) x = (equivShrink E).symm x := rfl

@[simp] theorem hilbertModuleShrinkUp_apply (x : E) :
    hilbertModuleShrinkUp (B := B) x = equivShrink E x := rfl

theorem IsCountablyGeneratedModule.shrink (h : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B (Shrink.{v} E) :=
  h.map_linearIsometryEquiv
    (hilbertModuleShrinkUp (B := B) (E := E)).linearIsometryEquiv id
    (hilbertModuleShrinkUp (B := B) (E := E)).map_op_smul

end BC4lean.KKTheory
