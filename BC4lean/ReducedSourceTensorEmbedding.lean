import BC4lean.ReducedCrossedHilbertModule
import BC4lean.IndexedHilbertModuleTensor
import BC4lean.IndexedHilbertModuleIsometry
import BC4lean.StandardModuleTensorEmbedding
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Canonical source tensor embedding into the actual indexed E-module



The actual regular coefficient module H_A has the same finite coefficient
form, radical quotient, and completion as IndexedHilbertModule.Module A Aop Γ.
The specialization is definitionally the same: both finite inner fields are
the sum of the original standard-module pairings, and the other form fields
are proofs. The tensor-distribution unitary followed by the coordinatewise
standard-factor pairing isometry therefore gives the canonical embedding
H_A ⊗_π E → indexed_Γ E, with no nondegeneracy assumption on π.

The localization preimage is the actual finite sum of elementary tensors.
Its image formula supplies a concrete input for a later approximate-unit
norm estimate; no estimate or approximate-unit conclusion is assumed here.
-/

noncomputable section
namespace BC4lean.KKTheory.ReducedSourceTensorEmbedding
open scoped InnerProductSpace

variable {Γ A B E : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)

local instance : DecidableEq Γ := Classical.decEq Γ

/-- Distribute the actual regular-module tensor into the indexed standard-factor tensors. -/
def coordinates : HilbertModuleEquiv B
    (InteriorModuleTensor (E := ReducedCrossedHilbertModule A Γ) π)
    (IndexedHilbertModule.Module B (InteriorModuleTensor (E := Aᵐᵒᵖ) π) Γ) :=
  IndexedHilbertModule.Tensor.equiv (E := Aᵐᵒᵖ) (I := Γ) π

/-- Collapse each actual standard-factor tensor a ⊗ x to π(a)x, isometrically. -/
def coordinateCollapse :
    IndexedHilbertModule.Module B (InteriorModuleTensor (E := Aᵐᵒᵖ) π) Γ →ₗᵢ[ℂ]
      IndexedHilbertModule.Module B E Γ :=
  IndexedHilbertModule.Isometry.lift (I := Γ)
    (StandardModuleTensorEmbedding.isometry π)
    (StandardModuleTensorEmbedding.isometry_inner π)

/-- The actual canonical source embedding; π may be degenerate. -/
def canonical : InteriorModuleTensor (E := ReducedCrossedHilbertModule A Γ) π →ₗᵢ[ℂ]
    IndexedHilbertModule.Module B E Γ :=
  (coordinateCollapse (Γ := Γ) π).comp
    (coordinates (Γ := Γ) π).linearIsometryEquiv.toLinearIsometry

theorem canonical_inner
    (u v : InteriorModuleTensor (E := ReducedCrossedHilbertModule A Γ) π) :
    ⟪canonical π u, canonical π v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) := by
  change ⟪coordinateCollapse π (coordinates π u),
    coordinateCollapse π (coordinates π v)⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ)
  rw [coordinateCollapse, IndexedHilbertModule.Isometry.lift_inner]
  exact (coordinates π).inner_map u v

/-- An elementary regular coordinate is sent to its actual represented coordinate. -/
@[simp] theorem canonical_mk_inclusion (t : Γ) (a : Aᵐᵒᵖ) (x : E) :
    canonical π
      (interiorModuleTensorMk π (reducedCrossedInclusion (B := A) t a) x) =
      IndexedHilbertModule.inclusion (B := B) t (π (MulOpposite.unop a) x) := by
  change IndexedHilbertModule.Isometry.lift (I := Γ)
      (StandardModuleTensorEmbedding.isometry π)
      (StandardModuleTensorEmbedding.isometry_inner π)
      (IndexedHilbertModule.Tensor.equiv (E := Aᵐᵒᵖ) (I := Γ) π
        (interiorModuleTensorMk π (IndexedHilbertModule.inclusion (B := A) t a) x)) = _
  rw [IndexedHilbertModule.Tensor.equiv_mk_inclusion,
    IndexedHilbertModule.Isometry.lift_inclusion,
    StandardModuleTensorEmbedding.isometry_mk]

/-- The actual finite vector with entries π(f_t)x, as a linear map in f. -/
def finiteImage (x : E) : ReducedCrossedVectors A Γ →ₗ[ℂ]
    IndexedHilbertModule.Vectors E Γ :=
  Finsupp.mapRange.linearMap ((StandardModuleTensorEmbedding.bilinear π).flip x)

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteImage_apply (x : E) (f : ReducedCrossedVectors A Γ) (t : Γ) :
    finiteImage π x f t = π (MulOpposite.unop (f t)) x := rfl

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteImage_single (x : E) (t : Γ) (a : Aᵐᵒᵖ) :
    finiteImage π x (Finsupp.single t a) =
      Finsupp.single t (π (MulOpposite.unop a) x) :=
  Finsupp.mapRange_single (hf := map_zero ((StandardModuleTensorEmbedding.bilinear π).flip x))

/-- The canonical embedding has the actual coordinate formula on every finite vector. -/
@[simp] theorem canonical_mk_finite (f : ReducedCrossedVectors A Γ) (x : E) :
    canonical π (interiorModuleTensorMk π (reducedCrossedMk f) x) =
      IndexedHilbertModule.mk (B := B) (finiteImage π x f) := by
  let L : ReducedCrossedVectors A Γ →ₗ[ℂ] IndexedHilbertModule.Module B E Γ :=
    (canonical π).toLinearMap.comp
      (((interiorModuleTensorMk (E := ReducedCrossedHilbertModule A Γ) π).flip x).comp
        (reducedCrossedMk (B := A) (Γ := Γ)))
  let R : ReducedCrossedVectors A Γ →ₗ[ℂ] IndexedHilbertModule.Module B E Γ :=
    (IndexedHilbertModule.mk (B := B)).comp (finiteImage π x)
  change L f = R f
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f h hf hh => rw [map_add, map_add, hf, hh]
  | single t a =>
    change canonical π
      (interiorModuleTensorMk π (reducedCrossedMk (Finsupp.single t a)) x) =
        IndexedHilbertModule.mk (B := B) (finiteImage π x (Finsupp.single t a))
    rw [← reducedCrossedInclusion_apply, canonical_mk_inclusion,
      finiteImage_single, IndexedHilbertModule.inclusion_apply]

/-- A finite localization preimage, linear in the E-valued finite vector. -/
def localizePreimageLinear (e : A) : IndexedHilbertModule.Vectors E Γ →ₗ[ℂ]
    InteriorModuleTensor (E := ReducedCrossedHilbertModule A Γ) π :=
  Finsupp.lsum ℂ (fun t => interiorModuleTensorMk π
    (reducedCrossedInclusion (B := A) t (MulOpposite.op e)))

/-- The concrete finite sum used before passing an approximate unit to its limit. -/
def localizePreimage (e : A) (ξ : IndexedHilbertModule.Vectors E Γ) :
    InteriorModuleTensor (E := ReducedCrossedHilbertModule A Γ) π :=
  localizePreimageLinear π e ξ

theorem localizePreimage_eq_sum (e : A) (ξ : IndexedHilbertModule.Vectors E Γ) :
    localizePreimage π e ξ = ∑ t ∈ ξ.support,
      interiorModuleTensorMk π
        (reducedCrossedInclusion (B := A) t (MulOpposite.op e)) (ξ t) := rfl

@[simp] theorem localizePreimage_single (e : A) (t : Γ) (x : E) :
    localizePreimage π e (Finsupp.single t x) =
      interiorModuleTensorMk π
        (reducedCrossedInclusion (B := A) t (MulOpposite.op e)) x :=
  Finsupp.lsum_single _ _ _ _

/-- The represented coefficient acts coordinatewise on the actual finite E-vectors. -/
def localizeVector (e : A) : IndexedHilbertModule.Vectors E Γ →ₗ[ℂ]
    IndexedHilbertModule.Vectors E Γ :=
  Finsupp.mapRange.linearMap (π e).toCLM.toLinearMap

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem localizeVector_apply (e : A) (ξ : IndexedHilbertModule.Vectors E Γ) (t : Γ) :
    localizeVector π e ξ t = π e (ξ t) := rfl

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem localizeVector_single (e : A) (t : Γ) (x : E) :
    localizeVector π e (Finsupp.single t x) = Finsupp.single t (π e x) :=
  Finsupp.mapRange_single (hf := map_zero (π e).toCLM.toLinearMap)

/-- The concrete localization preimage maps to the coordinatewise represented localization. -/
@[simp] theorem canonical_localizePreimage (e : A) (ξ : IndexedHilbertModule.Vectors E Γ) :
    canonical π (localizePreimage π e ξ) =
      IndexedHilbertModule.mk (B := B) (localizeVector π e ξ) := by
  let L : IndexedHilbertModule.Vectors E Γ →ₗ[ℂ] IndexedHilbertModule.Module B E Γ :=
    (canonical π).toLinearMap.comp (localizePreimageLinear π e)
  let R : IndexedHilbertModule.Vectors E Γ →ₗ[ℂ] IndexedHilbertModule.Module B E Γ :=
    (IndexedHilbertModule.mk (B := B)).comp (localizeVector π e)
  change L ξ = R ξ
  induction ξ using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη]
  | single t x =>
    change canonical π (localizePreimage π e (Finsupp.single t x)) =
      IndexedHilbertModule.mk (B := B) (localizeVector π e (Finsupp.single t x))
    rw [localizePreimage_single, canonical_mk_inclusion, MulOpposite.unop_op,
      localizeVector_single, IndexedHilbertModule.inclusion_apply]

end BC4lean.KKTheory.ReducedSourceTensorEmbedding
