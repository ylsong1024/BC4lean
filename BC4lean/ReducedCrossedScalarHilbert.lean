import BC4lean.ReducedCrossedHilbertModule
import BC4lean.L2Group
import BC4lean.ScalarHilbertModule
import BC4lean.HilbertModuleEquiv
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # The scalar regular Hilbert module is the existing group Hilbert space

The finite coefficient vector map sends a coefficient at `g` to that scalar
times the actual delta vector in `L2Group Γ`. Equality of the coefficient inner
products proves its norm equality. The two dense finite-vector embeddings then
give a genuine completed linear isometry equivalence and Hilbert-module unitary.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace ComplexOrder ScalarHilbertModule

variable {Γ : Type*}

/-- The finite scalar vector, interpreted in the existing group Hilbert space. -/
def reducedCrossedScalarFinite : ReducedCrossedVectors ℂ Γ →ₗ[ℂ] L2Group Γ :=
  Finsupp.lsum ℂ fun i =>
    (LinearMap.toSpanSingleton ℂ (L2Group Γ) (L2Group.delta i)).comp
      (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap

@[simp] theorem reducedCrossedScalarFinite_single (i : Γ) (z : ℂᵐᵒᵖ) :
    reducedCrossedScalarFinite (Finsupp.single i z) =
      MulOpposite.unop z • L2Group.delta i := by
  simp [reducedCrossedScalarFinite, Finsupp.lsum_single]

/-- The finite scalar interpretation retains every coefficient. -/
@[simp] theorem reducedCrossedScalarFinite_apply (x : ReducedCrossedVectors ℂ Γ)
    (i : Γ) : reducedCrossedScalarFinite x i = MulOpposite.unop (x i) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single j z =>
    by_cases h : i = j
    · subst i
      simp
    · simp [L2Group.delta_apply, h]

/-- The finite interpretation preserves the actual coefficient-valued pairing. -/
theorem reducedCrossedScalarFinite_inner (x y : ReducedCrossedVectors ℂ Γ) :
    inner ℂ (reducedCrossedScalarFinite x) (reducedCrossedScalarFinite y) =
      MulOpposite.unop (reducedCrossedFiniteInner x y) := by
  classical
  change inner ℂ (x.sum fun i z => MulOpposite.unop z • L2Group.delta i)
    (reducedCrossedScalarFinite y) = _
  rw [Finsupp.sum_inner]
  change (∑ i ∈ x.support,
    inner ℂ (MulOpposite.unop (x i) • L2Group.delta i) (reducedCrossedScalarFinite y)) =
      MulOpposite.unop (∑ i ∈ x.support, ⟪x i, y i⟫_(ℂᵐᵒᵖ))
  rw [Finset.unop_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.inner_smul_left, L2Group.inner_delta, reducedCrossedScalarFinite_apply]
  rfl

/-- The two finite embeddings have the same norm, derived from their pairings. -/
theorem reducedCrossedScalarFinite_norm (x : ReducedCrossedVectors ℂ Γ) :
    ‖reducedCrossedScalarFinite x‖ = ‖reducedCrossedMk x‖ := by
  calc
    ‖reducedCrossedScalarFinite x‖ =
        Real.sqrt ‖inner ℂ (reducedCrossedScalarFinite x)
          (reducedCrossedScalarFinite x)‖ := by
      simpa only [ScalarHilbertModule.inner_eq_op, MulOpposite.norm_op] using
        CStarModule.norm_eq_sqrt_norm_inner_self (A := ℂᵐᵒᵖ)
          (reducedCrossedScalarFinite x)
    _ = Real.sqrt ‖reducedCrossedFiniteInner x x‖ := by
      rw [reducedCrossedScalarFinite_inner, MulOpposite.norm_unop]
    _ = ‖reducedCrossedMk x‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℂᵐᵒᵖ)
        (reducedCrossedMk x), reducedCrossedMk_inner]

/-- Delta vectors are finite scalar vectors, so the scalar interpretation is dense. -/
theorem reducedCrossedScalarFinite_denseRange :
    DenseRange (reducedCrossedScalarFinite (Γ := Γ)) := by
  have hsub : (Submodule.span ℂ (Set.range (L2Group.delta : Γ → L2Group Γ)) :
      Set (L2Group Γ)) ⊆ Set.range reducedCrossedScalarFinite := by
    change Submodule.span ℂ _ ≤ reducedCrossedScalarFinite.range
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Finsupp.single i (MulOpposite.op (1 : ℂ)), by simp⟩
  intro ξ
  have hmem : ξ ∈
      (Submodule.span ℂ (Set.range (L2Group.delta : Γ → L2Group Γ))).topologicalClosure := by
    rw [L2Group.delta_dense_span]
    trivial
  exact closure_mono hsub hmem

/-- The actual scalar regular Hilbert module is isometrically the existing ℓ²(Γ). -/
def reducedCrossedScalarEquiv : ReducedCrossedHilbertModule ℂ Γ ≃ₗᵢ[ℂ] L2Group Γ :=
  (LinearEquiv.refl ℂ (ReducedCrossedVectors ℂ Γ)).extendOfIsometry
    reducedCrossedMk reducedCrossedScalarFinite reducedCrossedMk_denseRange
    reducedCrossedScalarFinite_denseRange reducedCrossedScalarFinite_norm

@[simp] theorem reducedCrossedScalarEquiv_mk (x : ReducedCrossedVectors ℂ Γ) :
    reducedCrossedScalarEquiv (reducedCrossedMk x) = reducedCrossedScalarFinite x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- The scalar isometry preserves the full opposite-valued Hilbert-module pairing. -/
theorem reducedCrossedScalarEquiv_inner (x y : ReducedCrossedHilbertModule ℂ Γ) :
    ⟪reducedCrossedScalarEquiv x, reducedCrossedScalarEquiv y⟫_(ℂᵐᵒᵖ) =
      ⟪x, y⟫_(ℂᵐᵒᵖ) := by
  refine reducedCrossedMk_denseRange.induction_on x ?_ ?_
  · exact isClosed_eq
      (CStarModule.continuous_inner.comp
        (reducedCrossedScalarEquiv.continuous.prodMk continuous_const))
      (CStarModule.continuous_inner.comp (continuous_id.prodMk continuous_const))
  · intro a
    refine reducedCrossedMk_denseRange.induction_on y ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk reducedCrossedScalarEquiv.continuous))
        (CStarModule.continuous_inner.comp (continuous_const.prodMk continuous_id))
    · intro b
      rw [reducedCrossedScalarEquiv_mk, reducedCrossedScalarEquiv_mk,
        ScalarHilbertModule.inner_eq_op, reducedCrossedScalarFinite_inner,
        MulOpposite.op_unop, reducedCrossedMk_inner]

/-- The completed scalar comparison as a genuine Hilbert-module unitary. -/
def reducedCrossedScalarHilbertEquiv :
    HilbertModuleEquiv ℂ (ReducedCrossedHilbertModule ℂ Γ) (L2Group Γ) where
  linearIsometryEquiv := reducedCrossedScalarEquiv
  inner_map := reducedCrossedScalarEquiv_inner

@[simp] theorem reducedCrossedScalarHilbertEquiv_mk (x : ReducedCrossedVectors ℂ Γ) :
    reducedCrossedScalarHilbertEquiv (reducedCrossedMk x) = reducedCrossedScalarFinite x :=
  reducedCrossedScalarEquiv_mk x

/-- Scalar-module adjointable maps on ℓ² are exactly its bounded Hilbert-space maps. -/
def scalarL2AdjointableEquiv :
    AdjointableMap ℂ (L2Group Γ) (L2Group Γ) ≃⋆ₐ[ℂ]
      (L2Group Γ →L[ℂ] L2Group Γ) where
  toFun := AdjointableMap.toCLM
  invFun := ScalarHilbertModule.ofContinuousLinearMap
  left_inv T := AdjointableMap.toCLM_injective rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' T := by
    change T.adjointCLM = star T.toCLM
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    exact congrArg MulOpposite.unop (T.adjoint.adjoint_identity x y)

/-- Conjugating by the actual scalar module unitary identifies the operator algebras. -/
def reducedCrossedScalarOperatorEquiv :
    AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ) ≃⋆ₐ[ℂ]
      (L2Group Γ →L[ℂ] L2Group Γ) :=
  reducedCrossedScalarHilbertEquiv.transportStarAlgEquiv.trans scalarL2AdjointableEquiv

@[simp] theorem reducedCrossedScalarOperatorEquiv_apply
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ)) (x : ReducedCrossedHilbertModule ℂ Γ) :
    reducedCrossedScalarOperatorEquiv T (reducedCrossedScalarHilbertEquiv x) =
      reducedCrossedScalarHilbertEquiv (T x) := by
  change reducedCrossedScalarHilbertEquiv
    (T (reducedCrossedScalarHilbertEquiv.symm (reducedCrossedScalarHilbertEquiv x))) = _
  rw [HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
