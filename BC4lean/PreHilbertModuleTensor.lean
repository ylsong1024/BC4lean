import BC4lean.ModuleTensorRadical

/-! # The actual separated pre-Hilbert interior tensor

We quotient the constructed balanced tensor by its proved null kernel.
The coefficient-valued form and right action descend to this quotient, and
the norm is the square root of the coefficient inner-square norm. Mathlib's
Hilbert-module norm theorem constructs the normed-space structure from these
proved laws. Neither positivity nor a tensor norm is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The balanced tensor after quotienting by its actual null space. -/
abbrev PreHilbertModuleTensor (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :=
  BalancedModuleTensor (E := E) φ ⧸ moduleTensorNull φ

/-- The elementary map to the separated pre-Hilbert tensor. -/
def preModuleTensorMk (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    E →ₗ[ℂ] F →ₗ[ℂ] PreHilbertModuleTensor (E := E) φ :=
  (moduleTensorMk φ).compr₂ (moduleTensorNull φ).mkQ

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- The original form vanishes on the null space in its first variable. -/
theorem moduleTensorInner_null_left
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) {u : BalancedModuleTensor (E := E) φ}
    (hu : u ∈ moduleTensorNull φ) (v : BalancedModuleTensor (E := E) φ) :
    moduleTensorInner φ u v = 0 := congrArg (fun f => f v) hu

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- Hermitian symmetry also annihilates the null space in the second variable. -/
theorem moduleTensorInner_null_right
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (u : BalancedModuleTensor (E := E) φ)
    {v : BalancedModuleTensor (E := E) φ} (hv : v ∈ moduleTensorNull φ) :
    moduleTensorInner φ u v = 0 := by
  apply star_injective
  rw [moduleTensorInner_star, moduleTensorInner_null_left φ hv, star_zero]

/-- Descend the form through the null quotient in the second variable. -/
def preModuleTensorInnerRightLift (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    BalancedModuleTensor (E := E) φ →ₗ⋆[ℂ]
      PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] Cᵐᵒᵖ where
  toFun u := (moduleTensorNull φ).liftQ (moduleTensorInner φ u) (by
    intro v hv
    exact moduleTensorInner_null_right φ u hv)
  map_add' u v := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro w
    change moduleTensorInner φ (u + v) w =
      moduleTensorInner φ u w + moduleTensorInner φ v w
    rw [map_add, LinearMap.add_apply]
  map_smul' c u := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro v
    change moduleTensorInner φ (c • u) v = star c • moduleTensorInner φ u v
    rw [map_smulₛₗ, LinearMap.smul_apply]
    rfl

/-- The descended coefficient-valued form on the null quotient. -/
def preModuleTensorInner (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    PreHilbertModuleTensor (E := E) φ →ₗ⋆[ℂ]
      PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] Cᵐᵒᵖ :=
  (moduleTensorNull φ).liftQ (preModuleTensorInnerRightLift φ) (by
    intro u hu
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro v
    exact moduleTensorInner_null_left φ hu v)

/-- The proved null submodule is invariant under the explicit coefficient map. -/
theorem moduleTensorNull_action_invariant
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) :
    moduleTensorNull (E := E) φ ≤
      (moduleTensorNull (E := E) φ).comap (moduleTensorActionLinear (E := E) φ a) := by
  intro u hu
  change moduleTensorActionLinear (E := E) φ a u ∈ moduleTensorNull (E := E) φ
  have h := moduleTensorNull_smul_mem φ a hu
  have haction : a • u = moduleTensorActionLinear (E := E) φ a u := rfl
  rw [haction] at h
  exact h

/-- Descend the actual fixed-coefficient action through the invariant null space. -/
def preModuleTensorActionLinear (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) :
    PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] PreHilbertModuleTensor (E := E) φ :=
  (moduleTensorNull (E := E) φ).mapQ (moduleTensorNull (E := E) φ)
    (moduleTensorActionLinear (E := E) φ a) (moduleTensorNull_action_invariant φ a)

instance preModuleTensorSMul (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    SMul Cᵐᵒᵖ (PreHilbertModuleTensor (E := E) φ) where
  smul a u := preModuleTensorActionLinear φ a u

/-- The actual pre-Hilbert tensor norm is determined by its descended inner square. -/
instance preModuleTensorNorm (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    Norm (PreHilbertModuleTensor (E := E) φ) where
  norm u := Real.sqrt ‖preModuleTensorInner φ u u‖

/-- All Hilbert-module laws on the separated tensor are proved from the
constructed form, its actual positivity, and the null-kernel equivalence. -/
instance preModuleTensorCStarModule (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    CStarModule Cᵐᵒᵖ (PreHilbertModuleTensor (E := E) φ) where
  inner := fun u v => preModuleTensorInner φ u v
  inner_add_right {x y z} := (preModuleTensorInner φ x).map_add y z
  inner_smul_right_complex {z x y} := (preModuleTensorInner φ x).map_smul z y
  inner_self_nonneg {u} := by
    induction u using Submodule.Quotient.induction_on with
    | H u => exact moduleTensorInner_self_nonneg φ u
  inner_self {u} := by
    induction u using Submodule.Quotient.induction_on with
    | H u =>
      exact (mem_moduleTensorNull_iff φ u).symm.trans (Submodule.Quotient.mk_eq_zero _).symm
  inner_op_smul_right {a u v} := by
    induction u using Submodule.Quotient.induction_on with
    | H u =>
      induction v using Submodule.Quotient.induction_on with
      | H v => exact moduleTensorInner_op_smul_right φ a u v
  star_inner u v := by
    induction u using Submodule.Quotient.induction_on with
    | H u =>
      induction v using Submodule.Quotient.induction_on with
      | H v => exact moduleTensorInner_star φ u v
  norm_eq_sqrt_norm_inner_self _ := rfl

/-- The normed additive group is constructed from the proved Hilbert-module laws. -/
instance preModuleTensorNormedAddCommGroup (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    NormedAddCommGroup (PreHilbertModuleTensor (E := E) φ) :=
  CStarModule.normedAddCommGroup Cᵐᵒᵖ

/-- The actual Hilbert norm also supplies the complex normed-space structure. -/
instance preModuleTensorNormedSpace (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    NormedSpace ℂ (PreHilbertModuleTensor (E := E) φ) :=
  .ofCore (CStarModule.normedSpaceCore Cᵐᵒᵖ)

@[simp] theorem preModuleTensorInner_mkQ_mkQ
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u v : BalancedModuleTensor (E := E) φ) :
    ⟪(moduleTensorNull φ).mkQ u, (moduleTensorNull φ).mkQ v⟫_(Cᵐᵒᵖ) =
      moduleTensorInner φ u v := rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- Balancing remains an actual equality after separation. -/
theorem preModuleTensorMk_balance
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (b : B) (x : E) (y : F) :
    preModuleTensorMk φ (MulOpposite.op b • x) y = preModuleTensorMk φ x (φ b y) :=
  congrArg (moduleTensorNull φ).mkQ (moduleTensorMk_balance φ b x y)

@[simp] theorem preModuleTensor_smul_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (a : Cᵐᵒᵖ) (x : E) (y : F) :
    a • preModuleTensorMk φ x y = preModuleTensorMk φ x (a • y) := rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- Elementary tensors generate the entire actual separated tensor. -/
@[elab_as_elim] theorem preModuleTensor_induction
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    {p : PreHilbertModuleTensor (E := E) φ → Prop} (u : PreHilbertModuleTensor (E := E) φ)
    (h0 : p 0) (hθ : ∀ x y, p (preModuleTensorMk φ x y))
    (hadd : ∀ u v, p u → p v → p (u + v)) : p u := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    refine moduleTensor_induction φ u ?_ ?_ ?_
    · exact h0
    · exact hθ
    · intro v w hv hw
      exact hadd _ _ hv hw

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- The complex span of elementary tensors equals the actual pre-Hilbert tensor. -/
theorem preModuleTensor_span_eq_top (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    Submodule.span ℂ (Set.range fun p : E × F => preModuleTensorMk φ p.1 p.2) = ⊤ := by
  apply top_unique
  intro u _
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · exact (Submodule.span ℂ _).zero_mem
  · intro x y
    exact Submodule.subset_span ⟨(x, y), rfl⟩
  · intro v w hv hw
    exact (Submodule.span ℂ _).add_mem hv hw

@[simp] theorem preModuleTensorInner_mk_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x x' : E) (y y' : F) :
    ⟪preModuleTensorMk φ x y, preModuleTensorMk φ x' y'⟫_(Cᵐᵒᵖ) =
      moduleTensorPureInner φ x y x' y' := rfl

/-- The actual separated tensor norm satisfies the elementary cross-norm bound. -/
theorem preModuleTensorMk_norm_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (y : F) :
    ‖preModuleTensorMk φ x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 2 ≠ 0)).mp
  rw [norm_sq_eq (Cᵐᵒᵖ), preModuleTensorInner_mk_mk]
  calc
    ‖moduleTensorPureInner φ x y x y‖ ≤ ‖x‖ * ‖y‖ * ‖x‖ * ‖y‖ :=
      moduleTensorPureInner_norm_le φ x x y y
    _ = (‖x‖ * ‖y‖) ^ 2 := by ring

end BC4lean.KKTheory
