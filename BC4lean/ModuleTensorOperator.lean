import BC4lean.InteriorModuleTensor
import BC4lean.AdjointableCompletion

/-! # Actual bounded first-factor tensor operators

Coefficient-linear adjointable operators act on the ordinary balanced tensor,
respect the proved radical, and extend to its actual completion. Boundedness
is proved from the positive operator norm defect, using the genuine positive
star cone and the already constructed tensor inner product.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- Apply an actual coefficient-linear operator in the first balanced factor. -/
def balancedModuleTensorOperator (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (T : AdjointableMap B E E) :
    BalancedModuleTensor (E := E) φ →ₗ[ℂ] BalancedModuleTensor (E := E) φ :=
  moduleTensorLift φ ((moduleTensorMk φ).comp T.toCLM.toLinearMap) (by
    intro b x y
    change moduleTensorMk φ (T (MulOpposite.op b • x)) y = moduleTensorMk φ (T x) (φ b y)
    rw [T.map_op_smul, moduleTensorMk_balance])

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem balancedModuleTensorOperator_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) (x : E) (y : F) :
    balancedModuleTensorOperator φ T (moduleTensorMk φ x y) = moduleTensorMk φ (T x) y := rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- The exact first-factor adjoint identity on the actual balancing quotient. -/
theorem balancedModuleTensorOperator_inner
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E)
    (u v : BalancedModuleTensor (E := E) φ) :
    moduleTensorInner φ (balancedModuleTensorOperator φ T u) v =
      moduleTensorInner φ u (balancedModuleTensorOperator φ T.adjoint v) := by
  revert v
  refine moduleTensor_induction φ u ?_ ?_ ?_
  · intro v
    simp
  · intro x y v
    refine moduleTensor_induction φ v ?_ ?_ ?_
    · simp
    · intro z w
      simp only [balancedModuleTensorOperator_mk, moduleTensorInner_mk_mk, moduleTensorPureInner]
      rw [T.adjoint_identity]
      rfl
    · intro v w hv hw
      simp only [map_add, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- The genuine radical is invariant under first-factor adjointable operators. -/
theorem balancedModuleTensorOperator_null
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E)
    {u : BalancedModuleTensor (E := E) φ} (hu : u ∈ moduleTensorNull φ) :
    balancedModuleTensorOperator φ T u ∈ moduleTensorNull φ := by
  apply LinearMap.ext
  intro v
  rw [balancedModuleTensorOperator_inner]
  exact moduleTensorInner_null_left φ hu _

/-- The actual first-factor action on the separated pre-Hilbert tensor. -/
def preModuleTensorOperatorLinear (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (T : AdjointableMap B E E) :
    PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] PreHilbertModuleTensor (E := E) φ :=
  (moduleTensorNull φ).mapQ (moduleTensorNull φ) (balancedModuleTensorOperator φ T)
    (fun _ hu => balancedModuleTensorOperator_null φ T hu)

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem preModuleTensorOperatorLinear_mkQ
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E)
    (u : BalancedModuleTensor (E := E) φ) :
    preModuleTensorOperatorLinear φ T ((moduleTensorNull φ).mkQ u) =
      (moduleTensorNull φ).mkQ (balancedModuleTensorOperator φ T u) := rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem preModuleTensorOperatorLinear_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) (x : E) (y : F) :
    preModuleTensorOperatorLinear φ T (preModuleTensorMk φ x y) = preModuleTensorMk φ (T x) y := rfl

/-- The exact adjoint identity descends through the proved radical. -/
theorem preModuleTensorOperatorLinear_inner
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E)
    (u v : PreHilbertModuleTensor (E := E) φ) :
    ⟪preModuleTensorOperatorLinear φ T u, v⟫_(Cᵐᵒᵖ) =
      ⟪u, preModuleTensorOperatorLinear φ T.adjoint v⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact balancedModuleTensorOperator_inner φ T u v

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- Additivity of the actual separated first-factor operator. -/
theorem preModuleTensorOperatorLinear_add
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (S T : AdjointableMap B E E) :
    preModuleTensorOperatorLinear φ (S + T) =
      preModuleTensorOperatorLinear φ S + preModuleTensorOperatorLinear φ T := by
  apply LinearMap.ext
  intro u
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · simp
  · intro x y
    simp only [preModuleTensorOperatorLinear_mk, AdjointableMap.coe_add_apply,
      map_add, LinearMap.add_apply]
  · intro u v hu hv
    simp only [map_add, LinearMap.add_apply, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem preModuleTensorOperatorLinear_zero
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    preModuleTensorOperatorLinear φ (0 : AdjointableMap B E E) = 0 := by
  apply LinearMap.ext
  intro u
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · simp
  · intro x y
    simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- First-factor multiplication agrees with actual composition. -/
theorem preModuleTensorOperatorLinear_mul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (S T : AdjointableMap B E E) :
    preModuleTensorOperatorLinear φ (S * T) =
      (preModuleTensorOperatorLinear φ S).comp (preModuleTensorOperatorLinear φ T) := by
  apply LinearMap.ext
  intro u
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · simp
  · intro x y
    rfl
  · intro u v hu hv
    simp only [map_add, LinearMap.comp_apply, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem preModuleTensorOperatorLinear_one
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    preModuleTensorOperatorLinear φ (1 : AdjointableMap B E E) = LinearMap.id := by
  apply LinearMap.ext
  intro u
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · simp
  · intro x y
    rfl
  · intro u v hu hv
    simp only [map_add, LinearMap.id_apply, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- Compatibility with actual complex scalar multiplication of operators. -/
theorem preModuleTensorOperatorLinear_smul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (c : ℂ) (T : AdjointableMap B E E) :
    preModuleTensorOperatorLinear φ (c • T) = c • preModuleTensorOperatorLinear φ T := by
  apply LinearMap.ext
  intro u
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · simp
  · intro x y
    simp only [preModuleTensorOperatorLinear_mk, AdjointableMap.coe_smul_apply,
      map_smul, LinearMap.smul_apply]
  · intro u v hu hv
    simp only [map_add, LinearMap.smul_apply, hu, hv]

local instance : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- The actual tensor pairing is positive on the genuine first-factor operator cone. -/
theorem preModuleTensorOperatorLinear_inner_nonneg
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (S : AdjointableMap B E E) (hS : 0 ≤ S)
    (u : PreHilbertModuleTensor (E := E) φ) :
    0 ≤ ⟪u, preModuleTensorOperatorLinear φ S u⟫_(Cᵐᵒᵖ) := by
  rw [StarOrderedRing.nonneg_iff] at hS
  induction hS using AddSubmonoid.closure_induction with
  | mem S hS =>
    obtain ⟨R, rfl⟩ := hS
    rw [preModuleTensorOperatorLinear_mul, LinearMap.comp_apply]
    rw [AdjointableMap.star_eq_adjoint]
    rw [← preModuleTensorOperatorLinear_inner φ R]
    exact CStarModule.inner_self_nonneg
  | zero => simp
  | add S T hS hT ihS ihT =>
    simpa only [preModuleTensorOperatorLinear_add, LinearMap.add_apply,
      CStarModule.inner_add_right] using add_nonneg ihS ihT

/-- The positive norm defect gives the exact coefficient-order bound. -/
theorem preModuleTensorOperatorLinear_inner_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E)
    (u : PreHilbertModuleTensor (E := E) φ) :
    ⟪preModuleTensorOperatorLinear φ T u, preModuleTensorOperatorLinear φ T u⟫_(Cᵐᵒᵖ) ≤
      (‖T‖ ^ 2 : ℝ) • ⟪u, u⟫_(Cᵐᵒᵖ) := by
  have hD : 0 ≤ algebraMap ℝ (AdjointableMap B E E) (‖T‖ ^ 2) - star T * T :=
    sub_nonneg.mpr CStarAlgebra.star_mul_le_algebraMap_norm_sq
  have h := preModuleTensorOperatorLinear_inner_nonneg φ _ hD u
  have hreal : algebraMap ℝ (AdjointableMap B E E) (‖T‖ ^ 2) =
      ((‖T‖ ^ 2 : ℝ) : ℂ) • (1 : AdjointableMap B E E) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  have hsub : preModuleTensorOperatorLinear φ
      (algebraMap ℝ (AdjointableMap B E E) (‖T‖ ^ 2) - star T * T) =
      ((‖T‖ ^ 2 : ℝ) : ℂ) • LinearMap.id -
        (preModuleTensorOperatorLinear φ T.adjoint).comp (preModuleTensorOperatorLinear φ T) := by
    rw [sub_eq_add_neg, preModuleTensorOperatorLinear_add, hreal,
      preModuleTensorOperatorLinear_smul, preModuleTensorOperatorLinear_one,
      ← neg_one_smul ℂ (star T * T), preModuleTensorOperatorLinear_smul,
      preModuleTensorOperatorLinear_mul]
    apply LinearMap.ext
    intro v
    simp [AdjointableMap.star_eq_adjoint, LinearMap.neg_apply, sub_eq_add_neg]
  rw [hsub, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply, CStarModule.inner_sub_right, CStarModule.inner_smul_right_complex,
    ← preModuleTensorOperatorLinear_inner φ T] at h
  exact sub_nonneg.mp h

/-- Genuine boundedness of the first-factor operator for the constructed tensor norm. -/
theorem preModuleTensorOperatorLinear_norm_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E)
    (u : PreHilbertModuleTensor (E := E) φ) :
    ‖preModuleTensorOperatorLinear φ T u‖ ≤ ‖T‖ * ‖u‖ := by
  have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (CStarModule.inner_self_nonneg (x := preModuleTensorOperatorLinear φ T u))
    (preModuleTensorOperatorLinear_inner_le φ T u)
  rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _),
    ← CStarModule.norm_sq_eq Cᵐᵒᵖ, ← CStarModule.norm_sq_eq Cᵐᵒᵖ] at h
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 2 ≠ 0)).mp
  simpa only [mul_pow] using h

/-- The bounded adjoint pair on the actual separated tensor. -/
def preModuleTensorOperator (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (T : AdjointableMap B E E) :
    AdjointableMap C (PreHilbertModuleTensor (E := E) φ) (PreHilbertModuleTensor (E := E) φ) where
  toCLM := (preModuleTensorOperatorLinear φ T).mkContinuous ‖T‖
    (preModuleTensorOperatorLinear_norm_le φ T)
  adjointCLM := (preModuleTensorOperatorLinear φ T.adjoint).mkContinuous ‖T.adjoint‖
    (preModuleTensorOperatorLinear_norm_le φ T.adjoint)
  adjoint_identity := preModuleTensorOperatorLinear_inner φ T

/-- The actual separated first-factor action is a complex star-algebra map. -/
def preModuleTensorOperatorHom (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    AdjointableMap B E E →⋆ₐ[ℂ]
      AdjointableMap C (PreHilbertModuleTensor (E := E) φ) (PreHilbertModuleTensor (E := E) φ) where
  toFun := preModuleTensorOperator φ
  map_zero' := by
    apply AdjointableMap.ext
    intro u
    exact congrArg (fun f => f u) (preModuleTensorOperatorLinear_zero φ)
  map_one' := by
    apply AdjointableMap.ext
    intro u
    exact congrArg (fun f => f u) (preModuleTensorOperatorLinear_one φ)
  map_add' S T := by
    apply AdjointableMap.ext
    intro u
    exact congrArg (fun f => f u) (preModuleTensorOperatorLinear_add φ S T)
  map_mul' S T := by
    apply AdjointableMap.ext
    intro u
    exact congrArg (fun f => f u) (preModuleTensorOperatorLinear_mul φ S T)
  commutes' c := by
    apply AdjointableMap.ext
    intro u
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change preModuleTensorOperatorLinear φ (c • (1 : AdjointableMap B E E)) u = c • u
    rw [preModuleTensorOperatorLinear_smul, preModuleTensorOperatorLinear_one]
    rfl
  map_star' _ := by
    apply AdjointableMap.ext
    intro u
    rfl

/-- The actual completed first-factor operator T ⊗ 1. -/
def interiorModuleTensorOperator (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (T : AdjointableMap B E E) :
    AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) :=
  (preModuleTensorOperator φ T).completion

@[simp] theorem interiorModuleTensorOperator_mk
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) (x : E) (y : F) :
    interiorModuleTensorOperator φ T (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk φ (T x) y := by
  exact (preModuleTensorOperator φ T).completion_apply_coe (preModuleTensorMk φ x y)

/-- The actual tensor operator obeys the original operator norm bound. -/
theorem interiorModuleTensorOperator_norm_le
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) :
    ‖interiorModuleTensorOperator φ T‖ ≤ ‖T‖ := by
  rw [interiorModuleTensorOperator, AdjointableMap.norm_completion, AdjointableMap.norm_def]
  exact ((preModuleTensorOperatorLinear φ T).mkContinuous ‖T‖
    (preModuleTensorOperatorLinear_norm_le φ T)).opNorm_le_bound (norm_nonneg _)
      (preModuleTensorOperatorLinear_norm_le φ T)

/-- The actual bounded completed tensor representation T ↦ T ⊗ 1. -/
def interiorModuleTensorOperatorHom (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    AdjointableMap B E E →⋆ₐ[ℂ]
      AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) :=
  AdjointableMap.completionHom.comp (preModuleTensorOperatorHom φ)

@[simp] theorem interiorModuleTensorOperatorHom_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) :
    interiorModuleTensorOperatorHom φ T = interiorModuleTensorOperator φ T := rfl

/-- The completed first-factor operator has the actual tensor of the adjoint. -/
@[simp] theorem interiorModuleTensorOperator_adjoint
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) :
    (interiorModuleTensorOperator φ T).adjoint =
      interiorModuleTensorOperator φ T.adjoint := by
  exact (map_star (interiorModuleTensorOperatorHom φ) T).symm

/-- Tensoring the first factor respects actual operator composition. -/
theorem interiorModuleTensorOperator_mul
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (S T : AdjointableMap B E E) :
    interiorModuleTensorOperator φ (S * T) =
      interiorModuleTensorOperator φ S * interiorModuleTensorOperator φ T :=
  map_mul (interiorModuleTensorOperatorHom φ) S T

end BC4lean.KKTheory
