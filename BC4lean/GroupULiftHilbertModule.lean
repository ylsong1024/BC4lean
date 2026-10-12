import BC4lean.HilbertModuleEquiv
import BC4lean.CountablyGeneratedModule
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! # Genuine Hilbert modules across a universe lift

Mathlib supplies the normed additive group, complex normed space and
completeness on ULift. The coefficient action is its actual lifted action;
the whole coefficient-valued form is pulled back by down. The resulting
down/up maps are genuine module unitaries across universes and preserve
countable coefficient generation.
-/

noncomputable section
universe uB uE v
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B : Type uB} {E : Type uE}
  [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

instance uliftCStarModule : CStarModule Bᵐᵒᵖ (ULift.{v} E) where
  inner x y := ⟪x.down, y.down⟫_(Bᵐᵒᵖ)
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro h
      apply ULift.ext
      exact (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp h
    · intro h
      rw [h]
      exact CStarModule.inner_zero_left
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner x y := CStarModule.star_inner x.down y.down
  norm_eq_sqrt_norm_inner_self x :=
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x.down

@[simp] theorem uliftModule_inner (x y : ULift.{v} E) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = ⟪x.down, y.down⟫_(Bᵐᵒᵖ) := rfl

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem uliftModule_op_smul_down (b : Bᵐᵒᵖ) (x : ULift.{v} E) :
    (b • x).down = b • x.down := rfl

def hilbertModuleULiftDown : HilbertModuleEquiv B (ULift.{v} E) E where
  linearIsometryEquiv := LinearIsometryEquiv.ulift ℂ E
  inner_map _ _ := rfl

def hilbertModuleULiftUp : HilbertModuleEquiv B E (ULift.{v} E) :=
  (hilbertModuleULiftDown (B := B) (E := E)).symm

@[simp] theorem hilbertModuleULiftDown_apply (x : ULift.{v} E) :
    hilbertModuleULiftDown (B := B) x = x.down := rfl

@[simp] theorem hilbertModuleULiftUp_apply (x : E) :
    hilbertModuleULiftUp (B := B) x = (ULift.up x : ULift.{v} E) := rfl

theorem IsCountablyGeneratedModule.ulift (h : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B (ULift.{v} E) :=
  h.map_linearIsometryEquiv
    (hilbertModuleULiftUp (B := B) (E := E)).linearIsometryEquiv id
    (hilbertModuleULiftUp (B := B) (E := E)).map_op_smul

theorem isCountablyGeneratedModule_ulift_iff :
    IsCountablyGeneratedModule B (ULift.{v} E) ↔ IsCountablyGeneratedModule B E := by
  constructor
  · intro h
    exact h.map_linearIsometryEquiv
      (hilbertModuleULiftDown (B := B) (E := E)).linearIsometryEquiv id
      (hilbertModuleULiftDown (B := B) (E := E)).map_op_smul
  · exact IsCountablyGeneratedModule.ulift

end BC4lean.KKTheory
