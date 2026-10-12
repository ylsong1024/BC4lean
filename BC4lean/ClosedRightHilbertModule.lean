import BC4lean.StandardModuleOperator
import BC4lean.HilbertModuleCountableGenerationSeparable
import BC4lean.StandardHilbertModuleActions
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # Closed right submodules of the standard Hilbert module

A closed complex subspace stable under right multiplication inherits the
actual coefficient inner product and norm. It is a Hilbert module even when
it is not a star algebra or an adjointably complemented subspace. Only left
multipliers preserving the subspace together with their adjoints are restricted.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {C : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A closed right subspace; no star closure or projection is part of the data. -/
structure ClosedRightModuleSubspace (C : Type*) [NonUnitalCStarAlgebra C] where
  submodule : Submodule ℂ Cᵐᵒᵖ
  isClosed : IsClosed (submodule : Set Cᵐᵒᵖ)
  op_smul_mem : ∀ (b x : Cᵐᵒᵖ), x ∈ submodule → b • x ∈ submodule

def ClosedRightHilbertModule (S : ClosedRightModuleSubspace C) := S.submodule

namespace ClosedRightHilbertModule
variable (S : ClosedRightModuleSubspace C)

instance instNormedAddCommGroup : NormedAddCommGroup (ClosedRightHilbertModule S) :=
  inferInstanceAs (NormedAddCommGroup S.submodule)
instance instNormedSpace : NormedSpace ℂ (ClosedRightHilbertModule S) :=
  inferInstanceAs (NormedSpace ℂ S.submodule)
instance instCompleteSpace : CompleteSpace (ClosedRightHilbertModule S) :=
  S.isClosed.isComplete.completeSpace_coe

instance instSMul : SMul Cᵐᵒᵖ (ClosedRightHilbertModule S) where
  smul b x := ⟨b • (x : Cᵐᵒᵖ), S.op_smul_mem b x x.property⟩

omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem coe_op_smul (b : Cᵐᵒᵖ) (x : ClosedRightHilbertModule S) :
    ((b • x : ClosedRightHilbertModule S) : Cᵐᵒᵖ) = b • (x : Cᵐᵒᵖ) := rfl

instance instCStarModule : CStarModule Cᵐᵒᵖ (ClosedRightHilbertModule S) where
  inner x y := ⟪(x : Cᵐᵒᵖ), (y : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ)
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro h
      apply Subtype.ext
      exact (CStarModule.inner_self (A := Cᵐᵒᵖ)).mp h
    · intro h
      rw [h]
      exact CStarModule.inner_zero_left
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner x y := CStarModule.star_inner (x : Cᵐᵒᵖ) (y : Cᵐᵒᵖ)
  norm_eq_sqrt_norm_inner_self x :=
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) (x : Cᵐᵒᵖ)

@[simp] theorem inner_coe (x y : ClosedRightHilbertModule S) :
    ⟪x, y⟫_(Cᵐᵒᵖ) = ⟪(x : Cᵐᵒᵖ), (y : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ) := rfl
omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem norm_coe (x : ClosedRightHilbertModule S) : ‖(x : Cᵐᵒᵖ)‖ = ‖x‖ := rfl

/-- Inclusion is a form-preserving isometry; adjointability is not asserted. -/
def inclusion : ClosedRightHilbertModule S →ₗᵢ[ℂ] Cᵐᵒᵖ where
  toLinearMap := S.submodule.subtype
  norm_map' _ := rfl

omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem inclusion_apply (x : ClosedRightHilbertModule S) :
    inclusion S x = (x : Cᵐᵒᵖ) := rfl

theorem countablyGenerated [TopologicalSpace.SeparableSpace C] :
    IsCountablyGeneratedModule C (ClosedRightHilbertModule S) := by
  let : TopologicalSpace.SeparableSpace Cᵐᵒᵖ :=
    MulOpposite.op_surjective.denseRange.separableSpace MulOpposite.continuous_op
  let : TopologicalSpace.SeparableSpace (ClosedRightHilbertModule S) := inferInstance
  exact isCountablyGeneratedModule_of_separableSpace

/-- Restriction of a genuine left multiplier which preserves the closed subspace. -/
def leftMulCLM (a : C)
    (ha : ∀ x ∈ S.submodule, standardLeftMulCLM a x ∈ S.submodule) :
    ClosedRightHilbertModule S →L[ℂ] ClosedRightHilbertModule S :=
  ((standardLeftMulCLM a).comp S.submodule.subtypeL).codRestrict S.submodule
    (fun x => ha x x.property)

omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem leftMulCLM_coe (a : C)
    (ha : ∀ x ∈ S.submodule, standardLeftMulCLM a x ∈ S.submodule)
    (x : ClosedRightHilbertModule S) :
    (leftMulCLM S a ha x : Cᵐᵒᵖ) =
      MulOpposite.op (a * MulOpposite.unop (x : Cᵐᵒᵖ)) := rfl

section Representation
variable {B : Type*} [NonUnitalCStarAlgebra B]
  (f : B →⋆ₙₐ[ℂ] C)
  (hf : ∀ b x, x ∈ S.submodule → standardLeftMulCLM (f b) x ∈ S.submodule)

/-- Both actual preservation laws follow from the star-homomorphism family. -/
def representationMap (b : B) :
    AdjointableMap C (ClosedRightHilbertModule S) (ClosedRightHilbertModule S) where
  toCLM := leftMulCLM S (f b) (hf b)
  adjointCLM := leftMulCLM S (f (star b)) (hf (star b))
  adjoint_identity x y := by
    change ⟪standardLeftMulCLM (f b) (x : Cᵐᵒᵖ), (y : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ) =
      ⟪(x : Cᵐᵒᵖ), standardLeftMulCLM (f (star b)) (y : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ)
    rw [map_star]
    exact (standardLeftMulMap (f b)).adjoint_identity
      (x : Cᵐᵒᵖ) (y : Cᵐᵒᵖ)

@[simp] theorem representationMap_coe (b : B) (x : ClosedRightHilbertModule S) :
    (representationMap S f hf b x : Cᵐᵒᵖ) =
      MulOpposite.op (f b * MulOpposite.unop (x : Cᵐᵒᵖ)) := rfl

def representation :
    B →⋆ₙₐ[ℂ] AdjointableMap C (ClosedRightHilbertModule S) (ClosedRightHilbertModule S) where
  toFun := representationMap S f hf
  map_zero' := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    change MulOpposite.op (f 0 * MulOpposite.unop (x : Cᵐᵒᵖ)) = (0 : Cᵐᵒᵖ)
    simp only [map_zero, zero_mul, MulOpposite.op_zero]
  map_add' a b := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    change MulOpposite.op (f (a + b) * MulOpposite.unop (x : Cᵐᵒᵖ)) =
      MulOpposite.op (f a * MulOpposite.unop (x : Cᵐᵒᵖ)) +
        MulOpposite.op (f b * MulOpposite.unop (x : Cᵐᵒᵖ))
    simp only [map_add, add_mul, MulOpposite.op_add]
  map_mul' a b := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    change MulOpposite.op (f (a * b) * MulOpposite.unop (x : Cᵐᵒᵖ)) =
      MulOpposite.op (f a * (f b * MulOpposite.unop (x : Cᵐᵒᵖ)))
    rw [map_mul, mul_assoc]
  map_smul' z a := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    change MulOpposite.op (f (z • a) * MulOpposite.unop (x : Cᵐᵒᵖ)) =
      z • MulOpposite.op (f a * MulOpposite.unop (x : Cᵐᵒᵖ))
    simp only [map_smul, smul_mul_assoc, MulOpposite.op_smul]
  map_star' _ := by apply AdjointableMap.ext; intro x; rfl

@[simp] theorem representation_coe (b : B) (x : ClosedRightHilbertModule S) :
    (representation S f hf b x : Cᵐᵒᵖ) =
      MulOpposite.op (f b * MulOpposite.unop (x : Cᵐᵒᵖ)) := rfl

theorem norm_representation_le (b : B) : ‖representation S f hf b‖ ≤ ‖f b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖f b * MulOpposite.unop (x : Cᵐᵒᵖ)‖ ≤
    ‖f b‖ * ‖MulOpposite.unop (x : Cᵐᵒᵖ)‖
  exact norm_mul_le _ _

end Representation
end ClosedRightHilbertModule
end BC4lean.KKTheory
