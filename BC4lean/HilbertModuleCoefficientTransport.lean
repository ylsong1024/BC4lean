import BC4lean.OppositeStarAlgEquivBetween
import BC4lean.HilbertModuleEquiv
import BC4lean.CountablyGeneratedModule
import BC4lean.EquivariantHilbertModule
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Transport along an actual coefficient star equivalence

The coefficient algebra may change. The module retains its actual complex
space and norm; its right action uses the inverse coefficient equivalence and
its inner product uses the forward equivalence. Thus this is a semilinear
change of coefficients, including nonunital algebras. Adjointable maps retain
their bounded maps and norms. Actual rank ones, their finite spans, and their
norm closure are transported, proving compactness without assuming it.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B C M N : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M] [CStarModule Bᵐᵒᵖ M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N]

/-- A separate carrier for a genuine change of coefficient algebra. -/
def CoefficientChangedModule (_e : B ≃⋆ₐ[ℂ] C) (M : Type*) := M

instance coefficientChangedNormedAddCommGroup (e : B ≃⋆ₐ[ℂ] C) :
    NormedAddCommGroup (CoefficientChangedModule e M) := inferInstanceAs (NormedAddCommGroup M)

instance coefficientChangedNormedSpace (e : B ≃⋆ₐ[ℂ] C) :
    NormedSpace ℂ (CoefficientChangedModule e M) := inferInstanceAs (NormedSpace ℂ M)

/-- Typed conversion to the original module, retaining its coefficient data. -/
def coefficientChangedToOriginal (e : B ≃⋆ₐ[ℂ] C)
    (x : CoefficientChangedModule e M) : M := x

/-- Typed conversion from the original module to the changed carrier. -/
def coefficientChangedOfOriginal (e : B ≃⋆ₐ[ℂ] C)
    (x : M) : CoefficientChangedModule e M := x

instance coefficientChangedSMul (e : B ≃⋆ₐ[ℂ] C) :
    SMul Cᵐᵒᵖ (CoefficientChangedModule e M) where
  smul a x := coefficientChangedOfOriginal (M := M) e
    (opStarAlgEquivBetween e.symm a • coefficientChangedToOriginal (M := M) e x)

/-- Only the coefficient structure changes: this is the identity on vectors. -/
def coefficientChangedLinearIsometry (e : B ≃⋆ₐ[ℂ] C) :
    M ≃ₗᵢ[ℂ] CoefficientChangedModule e M where
  toFun := coefficientChangedOfOriginal (M := M) e
  invFun := coefficientChangedToOriginal (M := M) e
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem coefficientChanged_op_apply_symm_apply (e : B ≃⋆ₐ[ℂ] C) (a : Cᵐᵒᵖ) :
    opStarAlgEquivBetween e (opStarAlgEquivBetween e.symm a) = a := by
  apply MulOpposite.unop_injective
  exact e.apply_symm_apply _

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem coefficientChanged_op_symm_apply_apply (e : B ≃⋆ₐ[ℂ] C) (a : Bᵐᵒᵖ) :
    opStarAlgEquivBetween e.symm (opStarAlgEquivBetween e a) = a := by
  apply MulOpposite.unop_injective
  exact e.symm_apply_apply _

instance coefficientChangedCStarModule (e : B ≃⋆ₐ[ℂ] C) :
    CStarModule Cᵐᵒᵖ (CoefficientChangedModule e M) where
  inner x y := opStarAlgEquivBetween e
    ⟪coefficientChangedToOriginal (M := M) e x,
      coefficientChangedToOriginal (M := M) e y⟫_(Bᵐᵒᵖ)
  inner_add_right := by
    intro x y z
    change opStarAlgEquivBetween e
      ⟪coefficientChangedToOriginal (M := M) e x,
        coefficientChangedToOriginal (M := M) e y +
          coefficientChangedToOriginal (M := M) e z⟫_(Bᵐᵒᵖ) = _
    rw [CStarModule.inner_add_right, map_add]
  inner_self_nonneg := by
    intro x
    exact map_nonneg (opStarAlgEquivBetween e)
      (CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ)
        (x := coefficientChangedToOriginal (M := M) e x))
  inner_self := by
    intro x
    change opStarAlgEquivBetween e
      ⟪coefficientChangedToOriginal (M := M) e x,
        coefficientChangedToOriginal (M := M) e x⟫_(Bᵐᵒᵖ) = 0 ↔
      coefficientChangedToOriginal (M := M) e x = 0
    constructor
    · intro hx
      have hz :
          ⟪coefficientChangedToOriginal (M := M) e x,
            coefficientChangedToOriginal (M := M) e x⟫_(Bᵐᵒᵖ) = 0 :=
        (opStarAlgEquivBetween e).injective
          (hx.trans (map_zero (opStarAlgEquivBetween e)).symm)
      exact (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp hz
    · intro hx
      exact (congrArg (opStarAlgEquivBetween e)
        ((CStarModule.inner_self (A := Bᵐᵒᵖ)).mpr hx)).trans
          (map_zero (opStarAlgEquivBetween e))
  inner_op_smul_right := by
    intro a x y
    change opStarAlgEquivBetween e
      ⟪coefficientChangedToOriginal (M := M) e x,
        opStarAlgEquivBetween e.symm a •
          coefficientChangedToOriginal (M := M) e y⟫_(Bᵐᵒᵖ) = _
    rw [CStarModule.inner_op_smul_right, map_mul, coefficientChanged_op_apply_symm_apply]
  inner_smul_right_complex := by
    intro c x y
    change opStarAlgEquivBetween e
      ⟪coefficientChangedToOriginal (M := M) e x,
        c • coefficientChangedToOriginal (M := M) e y⟫_(Bᵐᵒᵖ) = _
    rw [CStarModule.inner_smul_right_complex, map_smul]
  star_inner x y := by
    change star (opStarAlgEquivBetween e
      ⟪coefficientChangedToOriginal (M := M) e x,
        coefficientChangedToOriginal (M := M) e y⟫_(Bᵐᵒᵖ)) = _
    rw [← map_star, CStarModule.star_inner]
  norm_eq_sqrt_norm_inner_self x := by
    change ‖coefficientChangedToOriginal (M := M) e x‖ = Real.sqrt
      ‖opStarAlgEquivBetween e
        ⟪coefficientChangedToOriginal (M := M) e x,
          coefficientChangedToOriginal (M := M) e x⟫_(Bᵐᵒᵖ)‖
    rw [StarAlgEquiv.norm_map]
    exact CStarModule.norm_eq_sqrt_norm_inner_self _

@[simp] theorem coefficientChanged_inner (e : B ≃⋆ₐ[ℂ] C)
    (x y : CoefficientChangedModule e M) :
    ⟪x, y⟫_(Cᵐᵒᵖ) = opStarAlgEquivBetween e
      ⟪coefficientChangedToOriginal (M := M) e x,
        coefficientChangedToOriginal (M := M) e y⟫_(Bᵐᵒᵖ) := rfl

instance coefficientChangedCompleteSpace (e : B ≃⋆ₐ[ℂ] C) [CompleteSpace M] :
    CompleteSpace (CoefficientChangedModule e M) := inferInstanceAs (CompleteSpace M)

omit [StarOrderedRing B] [StarOrderedRing C] in
/-- Dense coefficient spans transport even when the two coefficient types
are different. Only the actual semilinearity law is needed. -/
theorem IsCountablyGeneratedModule.map_coefficientLinearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
    (hM : IsCountablyGeneratedModule B M) (u : M ≃ₗᵢ[ℂ] F)
    (ρ : Bᵐᵒᵖ → Cᵐᵒᵖ) (hu : ∀ b x, u (b • x) = ρ b • u x) :
    IsCountablyGeneratedModule C F := by
  obtain ⟨ξ, hξ⟩ := hM
  refine ⟨fun n => u (ξ n), ?_⟩
  have hm : ∀ x ∈ moduleGeneratingSpan (B := B) ξ,
      u x ∈ moduleGeneratingSpan (B := C) (fun n => u (ξ n)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      rw [hu]
      exact smul_mem_moduleGeneratingSpan _ n (ρ b)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hd : DenseRange u := by
    rw [DenseRange, u.surjective.range_eq]
    exact dense_univ
  exact (hd.dense_image u.continuous hξ).mono (by
    rintro y ⟨x, hx, rfl⟩
    exact hm x hx)

theorem IsCountablyGeneratedModule.coefficientChanged (e : B ≃⋆ₐ[ℂ] C)
    (hM : IsCountablyGeneratedModule B M) :
    IsCountablyGeneratedModule C (CoefficientChangedModule e M) := by
  apply hM.map_coefficientLinearIsometryEquiv (coefficientChangedLinearIsometry (M := M) e)
    (opStarAlgEquivBetween e)
  intro a x
  change coefficientChangedOfOriginal (M := M) e (a • x) =
    coefficientChangedOfOriginal (M := M) e
      (opStarAlgEquivBetween e.symm (opStarAlgEquivBetween e a) • x)
  rw [coefficientChanged_op_symm_apply_apply]

/-- Transport preserves both bounded members of the actual adjoint pair. -/
def coefficientChangedOperator (e : B ≃⋆ₐ[ℂ] C) (T : AdjointableMap B M N) :
    AdjointableMap C (CoefficientChangedModule e M) (CoefficientChangedModule e N) where
  toCLM := T.toCLM
  adjointCLM := T.adjointCLM
  adjoint_identity x y := by
    change opStarAlgEquivBetween e
      ⟪T.toCLM (coefficientChangedToOriginal (M := M) e x),
        coefficientChangedToOriginal (M := N) e y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquivBetween e
        ⟪coefficientChangedToOriginal (M := M) e x,
          T.adjointCLM (coefficientChangedToOriginal (M := N) e y)⟫_(Bᵐᵒᵖ)
    exact congrArg (opStarAlgEquivBetween e)
      (T.adjoint_identity (coefficientChangedToOriginal (M := M) e x)
        (coefficientChangedToOriginal (M := N) e y))

@[simp] theorem coefficientChangedOperator_apply (e : B ≃⋆ₐ[ℂ] C)
    (T : AdjointableMap B M N) (x : CoefficientChangedModule e M) :
    coefficientChangedOperator e T x = T (coefficientChangedToOriginal (M := M) e x) := rfl

@[simp] theorem coefficientChangedOperator_norm (e : B ≃⋆ₐ[ℂ] C)
    (T : AdjointableMap B M N) : ‖coefficientChangedOperator e T‖ = ‖T‖ := rfl

@[simp] theorem coefficientChangedOperator_zero (e : B ≃⋆ₐ[ℂ] C) :
    coefficientChangedOperator e (0 : AdjointableMap B M N) = 0 := by ext x; rfl

@[simp] theorem coefficientChangedOperator_add (e : B ≃⋆ₐ[ℂ] C)
    (S T : AdjointableMap B M N) :
    coefficientChangedOperator e (S + T) = coefficientChangedOperator e S + coefficientChangedOperator e T := by
  ext x; rfl

@[simp] theorem coefficientChangedOperator_sub (e : B ≃⋆ₐ[ℂ] C)
    (S T : AdjointableMap B M N) :
    coefficientChangedOperator e (S - T) = coefficientChangedOperator e S - coefficientChangedOperator e T := by
  ext x; rfl

@[simp] theorem coefficientChangedOperator_smul (e : B ≃⋆ₐ[ℂ] C)
    (c : ℂ) (T : AdjointableMap B M N) :
    coefficientChangedOperator e (c • T) = c • coefficientChangedOperator e T := by ext x; rfl

@[simp] theorem coefficientChangedOperator_adjoint (e : B ≃⋆ₐ[ℂ] C)
    (T : AdjointableMap B M N) :
    coefficientChangedOperator e T.adjoint = (coefficientChangedOperator e T).adjoint := rfl

@[simp] theorem coefficientChangedOperator_mul (e : B ≃⋆ₐ[ℂ] C)
    (S T : AdjointableMap B M M) :
    coefficientChangedOperator e (S * T) = coefficientChangedOperator e S * coefficientChangedOperator e T := by
  ext x; rfl

@[simp] theorem coefficientChangedOperator_one (e : B ≃⋆ₐ[ℂ] C) :
    coefficientChangedOperator e (1 : AdjointableMap B M M) = 1 := by ext x; rfl

@[simp] theorem coefficientChangedOperator_star (e : B ≃⋆ₐ[ℂ] C)
    (T : AdjointableMap B M M) :
    coefficientChangedOperator e (star T) = star (coefficientChangedOperator e T) := rfl

def coefficientChangedOperatorLinearIsometry (e : B ≃⋆ₐ[ℂ] C) :
    AdjointableMap B M N →ₗᵢ[ℂ]
      AdjointableMap C (CoefficientChangedModule e M) (CoefficientChangedModule e N) where
  toFun := coefficientChangedOperator e
  map_add' := coefficientChangedOperator_add e
  map_smul' := coefficientChangedOperator_smul e
  norm_map' := coefficientChangedOperator_norm e

/-- The actual rank-one formula; the forward and inverse coefficients cancel. -/
@[simp] theorem coefficientChangedOperator_rankOne (e : B ≃⋆ₐ[ℂ] C) (x : N) (y : M) :
    coefficientChangedOperator e (moduleRankOne (B := B) x y) =
      moduleRankOne (B := C) (coefficientChangedLinearIsometry e x)
        (coefficientChangedLinearIsometry e y) := by
  ext z
  change coefficientChangedOfOriginal (M := N) e
      (⟪y, coefficientChangedToOriginal (M := M) e z⟫_(Bᵐᵒᵖ) • x) =
    coefficientChangedOfOriginal (M := N) e
      (opStarAlgEquivBetween e.symm
        (opStarAlgEquivBetween e
          ⟪y, coefficientChangedToOriginal (M := M) e z⟫_(Bᵐᵒᵖ)) • x)
  rw [coefficientChanged_op_symm_apply_apply]

theorem IsModuleCompact.coefficientChanged (e : B ≃⋆ₐ[ℂ] C)
    {T : AdjointableMap B M N} (hT : IsModuleCompact T) :
    IsModuleCompact (coefficientChangedOperator e T) := by
  let f := coefficientChangedOperatorLinearIsometry (M := M) (N := N) e
  let S := (moduleCompact C (CoefficientChangedModule e M)
    (CoefficientChangedModule e N)).comap f.toLinearMap
  have hS : IsClosed (S : Set (AdjointableMap B M N)) :=
    moduleCompact_isClosed.preimage f.continuous
  have hθ (x : N) (y : M) : moduleRankOne (B := B) x y ∈ S := by
    change coefficientChangedOperator e (moduleRankOne (B := B) x y) ∈
      moduleCompact C (CoefficientChangedModule e M) (CoefficientChangedModule e N)
    rw [coefficientChangedOperator_rankOne]
    exact moduleRankOne_mem_moduleCompact _ _
  exact moduleCompact_le_of_isClosed S hS hθ hT

def coefficientChangedOperatorHom (e : B ≃⋆ₐ[ℂ] C) :
    AdjointableMap B M M →⋆ₙₐ[ℂ]
      AdjointableMap C (CoefficientChangedModule e M) (CoefficientChangedModule e M) where
  toFun := coefficientChangedOperator e
  map_zero' := coefficientChangedOperator_zero e
  map_add' := coefficientChangedOperator_add e
  map_mul' := coefficientChangedOperator_mul e
  map_smul' := coefficientChangedOperator_smul e
  map_star' := coefficientChangedOperator_star e

end BC4lean.KKTheory
