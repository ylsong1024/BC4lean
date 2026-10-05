import BC4lean.L2Group
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! # Creation maps in the actual scalar tensor-product model

For B = E = ℂ and the scalar representation on a complex Hilbert space H,
the interior tensor product is the scalar Hilbert-space tensor product ℂ ⊗ H.
Mathlib supplies this actual tensor product and its isometric identification
with H. The creation map at ξ sends η to ξ ⊗ η; its bounded adjoint sends
a ⊗ η to (star ξ * a) • η.

The creation map at 1 on ℓ²(ℕ) is not compact: under the isometric scalar
tensor identification it is the identity on an infinite-dimensional space.
This verifies the diagnostic for the compactness assertion printed immediately
before Definition 3.10 in Echterhoff, arXiv:1703.10912v2, Section 3.3.
The correct general starting assertion is adjointability. The theorems below
use Mathlib's complex Hilbert-space compactness predicate, not a newly assumed
interior tensor product or a general Hilbert C⋆-module compactness theorem.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped TensorProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual creation map in the scalar tensor-product model. -/
def scalarCreationMap (ξ : ℂ) : H →L[ℂ] ℂ ⊗[ℂ] H :=
  TensorProduct.mkL ℂ ℂ H ξ

@[simp] theorem scalarCreationMap_apply (ξ : ℂ) (η : H) :
    scalarCreationMap ξ η = ξ ⊗ₜ[ℂ] η := rfl

/-- Scalar tensoring identifies a creation map with scalar multiplication. -/
@[simp] theorem scalarCreationMap_under_lid (ξ : ℂ) (η : H) :
    TensorProduct.lidIsometry ℂ H (scalarCreationMap ξ η) = ξ • η := by
  simp [scalarCreationMap_apply]

/-- The same identification as an equality of continuous linear maps. -/
@[simp] theorem scalarCreationMap_lid_comp (ξ : ℂ) :
    (TensorProduct.lidIsometry ℂ H).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (scalarCreationMap ξ) = ξ • ContinuousLinearMap.id ℂ H := by
  ext η
  simp

/-- The creation map has the expected operator-norm bound. -/
theorem scalarCreationMap_norm_le (ξ : ℂ) :
    ‖scalarCreationMap (H := H) ξ‖ ≤ ‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro η
  simp

/-- A bounded adjoint, constructed using the scalar tensor identification. -/
def scalarCreationAdjoint (ξ : ℂ) : (ℂ ⊗[ℂ] H) →L[ℂ] H :=
  star ξ • (TensorProduct.lidIsometry ℂ H).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem scalarCreationAdjoint_apply (ξ : ℂ) (z : ℂ ⊗[ℂ] H) :
    scalarCreationAdjoint ξ z = star ξ • TensorProduct.lidIsometry ℂ H z := rfl

@[simp] theorem scalarCreationAdjoint_tmul (ξ a : ℂ) (η : H) :
    scalarCreationAdjoint ξ (a ⊗ₜ[ℂ] η) = (star ξ * a) • η := by
  simp [scalarCreationAdjoint_apply, smul_smul]

/-- The creation map is adjointable, with the explicitly constructed bounded adjoint. -/
theorem scalarCreationMap_adjoint_identity (ξ : ℂ) (η : H) (z : ℂ ⊗[ℂ] H) :
    inner ℂ (scalarCreationMap ξ η) z = inner ℂ η (scalarCreationAdjoint ξ z) := by
  rw [← (TensorProduct.lidIsometry ℂ H).inner_map_map]
  simp [inner_smul_left, inner_smul_right]

/-- The bounded adjoint is uniquely characterized by the inner-product identity. -/
theorem scalarCreationAdjoint_unique (ξ : ℂ) (S : (ℂ ⊗[ℂ] H) →L[ℂ] H)
    (hS : ∀ η z, inner ℂ (scalarCreationMap ξ η) z = inner ℂ η (S z)) :
    S = scalarCreationAdjoint ξ := by
  ext z
  apply ext_inner_left ℂ
  intro η
  rw [← hS, scalarCreationMap_adjoint_identity]

/-- The scalar tensor product is complete whenever H is complete. -/
instance scalarTensorCompleteSpace [CompleteSpace H] : CompleteSpace (ℂ ⊗[ℂ] H) :=
  (TensorProduct.lidIsometry ℂ H).toIsometryEquiv.completeSpace

/-- Agreement with Mathlib's Hilbert-space adjoint on complete spaces. -/
@[simp] theorem scalarCreationMap_adjoint [CompleteSpace H] (ξ : ℂ) :
    (scalarCreationMap (H := H) ξ).adjoint = scalarCreationAdjoint ξ := by
  apply scalarCreationAdjoint_unique
  intro η z
  exact (ContinuousLinearMap.adjoint_inner_right _ η z).symm

/-- The adjoint followed by a creation map is the scalar representation of the inner product. -/
theorem scalarCreationAdjoint_comp_creation (ξ ζ : ℂ) :
    (scalarCreationAdjoint (H := H) ξ).comp (scalarCreationMap ζ) =
      (star ξ * ζ) • ContinuousLinearMap.id ℂ H := by
  ext η
  simp [smul_smul]

/-- The delta vectors make ℓ²(ℕ) infinite-dimensional over ℂ. -/
theorem l2Nat_not_finiteDimensional : ¬ FiniteDimensional ℂ (BC4lean.L2Group ℕ) := by
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite
    (BC4lean.L2Group.delta : ℕ → BC4lean.L2Group ℕ)
    (BC4lean.L2Group.delta_orthonormal.linearIndependent)

/-- The continuous linear identity on ℓ²(ℕ) is not compact. -/
theorem l2Nat_identity_not_compact :
    ¬ IsCompactOperator (ContinuousLinearMap.id ℂ (BC4lean.L2Group ℕ)) := by
  intro h
  apply l2Nat_not_finiteDimensional
  exact (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).mp h

/-- A verified counterexample to automatic compactness of creation maps. -/
theorem scalarCreationMap_one_not_compact :
    ¬ IsCompactOperator (scalarCreationMap (H := BC4lean.L2Group ℕ) 1) := by
  intro h
  apply l2Nat_identity_not_compact
  have hc : IsCompactOperator
      ((TensorProduct.lidIsometry ℂ (BC4lean.L2Group ℕ)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (scalarCreationMap 1)) :=
    h.clm_comp (TensorProduct.lidIsometry ℂ (BC4lean.L2Group ℕ)).toContinuousLinearEquiv.toContinuousLinearMap
  simpa only [scalarCreationMap_lid_comp, one_smul] using hc

end BC4lean.KKTheory
