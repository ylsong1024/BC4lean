import BC4lean.ModuleTensorCompact
import BC4lean.HilbertModuleSum

/-! # Actual rectangular first-factor tensor maps

An adjointable map between different first modules acts through balancing,
the null quotient and completion. Its norm bound is obtained from the genuine
endomorphism tensor theorem on a finite Hilbert-module direct sum, whose
coordinate tensor inclusions preserve the actual inner product. No tensor of
a compact map is asserted compact.
-/

noncomputable section
namespace BC4lean.KKTheory.RectangularInteriorModuleTensorOperator
open scoped InnerProductSpace

variable {B C E E' E'' F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] [SMul Bᵐᵒᵖ E''] [CStarModule Bᵐᵒᵖ E'']
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace E'] [CompleteSpace E''] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

def balanced (T : AdjointableMap B E E') :
    BalancedModuleTensor (E := E) φ →ₗ[ℂ] BalancedModuleTensor (E := E') φ :=
  moduleTensorLift φ ((moduleTensorMk (E := E') φ).comp T.toCLM.toLinearMap) (by
    intro b x y
    change moduleTensorMk φ (T (MulOpposite.op b • x)) y = moduleTensorMk φ (T x) (φ b y)
    rw [T.map_op_smul, moduleTensorMk_balance])

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] in
@[simp] theorem balanced_mk (T : AdjointableMap B E E') (x : E) (y : F) :
    balanced φ T (moduleTensorMk φ x y) = moduleTensorMk φ (T x) y := rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] in
theorem balanced_inner (T : AdjointableMap B E E')
    (u : BalancedModuleTensor (E := E) φ) (v : BalancedModuleTensor (E := E') φ) :
    moduleTensorInner φ (balanced φ T u) v = moduleTensorInner φ u (balanced φ T.adjoint v) := by
  revert v
  refine moduleTensor_induction φ u ?_ ?_ ?_
  · intro v
    simp
  · intro x y v
    refine moduleTensor_induction φ v ?_ ?_ ?_
    · simp
    · intro z w
      simp only [balanced_mk, moduleTensorInner_mk_mk, moduleTensorPureInner]
      rw [T.adjoint_identity]
      rfl
    · intro v w hv hw
      simp only [map_add, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] in
theorem balanced_null (T : AdjointableMap B E E')
    {u : BalancedModuleTensor (E := E) φ} (hu : u ∈ moduleTensorNull φ) :
    balanced φ T u ∈ moduleTensorNull (E := E') φ := by
  apply LinearMap.ext
  intro v
  rw [balanced_inner]
  exact moduleTensorInner_null_left φ hu _

def preLinear (T : AdjointableMap B E E') :
    PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] PreHilbertModuleTensor (E := E') φ :=
  (moduleTensorNull (E := E) φ).mapQ (moduleTensorNull (E := E') φ)
    (balanced φ T) (fun _ hu => balanced_null φ T hu)

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] in
@[simp] theorem preLinear_mk (T : AdjointableMap B E E') (x : E) (y : F) :
    preLinear φ T (preModuleTensorMk φ x y) = preModuleTensorMk φ (T x) y := rfl

theorem preLinear_inner (T : AdjointableMap B E E')
    (u : PreHilbertModuleTensor (E := E) φ) (v : PreHilbertModuleTensor (E := E') φ) :
    ⟪preLinear φ T u, v⟫_(Cᵐᵒᵖ) = ⟪u, preLinear φ T.adjoint v⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact balanced_inner φ T u v

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace E'] [CompleteSpace E''] [CompleteSpace F] in
theorem preLinear_comp (T : AdjointableMap B E E') (S : AdjointableMap B E' E'') :
    preLinear φ (S.comp T) = (preLinear φ S).comp (preLinear φ T) := by
  apply LinearMap.ext
  intro u
  refine preModuleTensor_induction φ u ?_ ?_ ?_
  · simp
  · intro x y
    rfl
  · intro u v hu hv
    simp only [map_add, LinearMap.comp_apply, hu, hv]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
theorem preLinear_endo (T : AdjointableMap B E E) :
    preLinear φ T = preModuleTensorOperatorLinear φ T := rfl

theorem preLinear_inl_norm (u : PreHilbertModuleTensor (E := E) φ) :
    ‖preLinear φ (sumInl (B := B) (E := E) (F := E')) u‖ = ‖u‖ := by
  have hi : ⟪preLinear φ (sumInl (B := B) (E := E) (F := E')) u,
      preLinear φ (sumInl (B := B) (E := E) (F := E')) u⟫_(Cᵐᵒᵖ) = ⟪u, u⟫_(Cᵐᵒᵖ) := by
    rw [preLinear_inner, sumInl_adjoint, ← LinearMap.comp_apply,
      ← preLinear_comp, sumFst_comp_inl, preLinear_endo]
    change ⟪u, preModuleTensorOperatorLinear φ (1 : AdjointableMap B E E) u⟫_(Cᵐᵒᵖ) = ⟪u, u⟫_(Cᵐᵒᵖ)
    rw [preModuleTensorOperatorLinear_one]
    rfl
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), hi]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) u).symm

theorem preLinear_inr_norm (u : PreHilbertModuleTensor (E := E') φ) :
    ‖preLinear φ (sumInr (B := B) (E := E) (F := E')) u‖ = ‖u‖ := by
  have hi : ⟪preLinear φ (sumInr (B := B) (E := E) (F := E')) u,
      preLinear φ (sumInr (B := B) (E := E) (F := E')) u⟫_(Cᵐᵒᵖ) = ⟪u, u⟫_(Cᵐᵒᵖ) := by
    rw [preLinear_inner, sumInr_adjoint, ← LinearMap.comp_apply,
      ← preLinear_comp, sumSnd_comp_inr, preLinear_endo]
    change ⟪u, preModuleTensorOperatorLinear φ (1 : AdjointableMap B E' E') u⟫_(Cᵐᵒᵖ) = ⟪u, u⟫_(Cᵐᵒᵖ)
    rw [preModuleTensorOperatorLinear_one]
    rfl
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), hi]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) u).symm

/-- The actual direct-sum corner bound proves rectangular boundedness. -/
theorem preLinear_norm_le (T : AdjointableMap B E E')
    (u : PreHilbertModuleTensor (E := E) φ) : ‖preLinear φ T u‖ ≤ ‖T‖ * ‖u‖ := by
  let : CompleteSpace (HilbertModuleSum B E E') := hilbertModuleSum_complete
  let L : AdjointableMap B (HilbertModuleSum B E E') (HilbertModuleSum B E E') :=
    ((sumInr (B := B) (E := E) (F := E')).comp T).comp sumFst
  have hL : L.comp (sumInl (B := B) (E := E) (F := E')) =
      (sumInr (B := B) (E := E) (F := E')).comp T := by
    apply AdjointableMap.ext
    intro x
    rfl
  have heq : preModuleTensorOperatorLinear φ L
      (preLinear φ (sumInl (B := B) (E := E) (F := E')) u) =
      preLinear φ (sumInr (B := B) (E := E) (F := E')) (preLinear φ T u) := by
    rw [← preLinear_endo, ← LinearMap.comp_apply, ← preLinear_comp, hL, preLinear_comp]
    rfl
  have hnorm : ‖L‖ ≤ ‖T‖ := by
    calc
      ‖L‖ ≤ ‖(sumInr (B := B) (E := E) (F := E')).comp T‖ * ‖sumFst (B := B) (E := E) (F := E')‖ :=
        AdjointableMap.norm_comp_le _ _
      _ ≤ (1 * ‖T‖) * 1 := mul_le_mul
        ((AdjointableMap.norm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right norm_sumInr_le (norm_nonneg T)))
        norm_sumFst_le (norm_nonneg _) (by positivity)
      _ = ‖T‖ := by ring
  calc
    ‖preLinear φ T u‖ = ‖preModuleTensorOperatorLinear φ L
        (preLinear φ (sumInl (B := B) (E := E) (F := E')) u)‖ := by
      rw [heq, preLinear_inr_norm]
    _ ≤ ‖L‖ * ‖preLinear φ (sumInl (B := B) (E := E) (F := E')) u‖ :=
      preModuleTensorOperatorLinear_norm_le φ L _
    _ ≤ ‖T‖ * ‖u‖ := by
      rw [preLinear_inl_norm]
      exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

def pre (T : AdjointableMap B E E') :
    AdjointableMap C (PreHilbertModuleTensor (E := E) φ) (PreHilbertModuleTensor (E := E') φ) where
  toCLM := (preLinear φ T).mkContinuous ‖T‖ (preLinear_norm_le φ T)
  adjointCLM := (preLinear φ T.adjoint).mkContinuous ‖T.adjoint‖ (preLinear_norm_le φ T.adjoint)
  adjoint_identity := preLinear_inner φ T

def tensor (T : AdjointableMap B E E') :
    AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E') φ) :=
  (pre φ T).completion

@[simp] theorem tensor_mk (T : AdjointableMap B E E') (x : E) (y : F) :
    tensor φ T (interiorModuleTensorMk φ x y) = interiorModuleTensorMk φ (T x) y :=
  (pre φ T).completion_apply_coe (preModuleTensorMk φ x y)

theorem tensor_norm_le (T : AdjointableMap B E E') : ‖tensor φ T‖ ≤ ‖T‖ := by
  rw [tensor, AdjointableMap.norm_completion, AdjointableMap.norm_def]
  exact ((preLinear φ T).mkContinuous ‖T‖ (preLinear_norm_le φ T)).opNorm_le_bound
    (norm_nonneg _) (preLinear_norm_le φ T)

@[simp] theorem tensor_adjoint (T : AdjointableMap B E E') :
    (tensor φ T).adjoint = tensor φ T.adjoint := rfl

theorem tensor_comp (T : AdjointableMap B E E') (S : AdjointableMap B E' E'') :
    tensor φ (S.comp T) = (tensor φ S).comp (tensor φ T) := by
  apply AdjointableMap.toCLM_injective
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
  intro x y
  simp only [tensor_mk, AdjointableMap.comp_apply]

theorem tensor_rankOne (x : E') (y : E) :
    tensor φ (moduleRankOne (B := B) x y) =
      (moduleCreationMap φ x).comp (moduleCreationMap φ y).adjoint := by
  apply AdjointableMap.toCLM_injective
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
  intro z w
  simp only [tensor_mk, moduleRankOne_apply, AdjointableMap.comp_apply]
  change interiorModuleTensorMk φ (⟪y, z⟫_(Bᵐᵒᵖ) • x) w =
    moduleCreationMap φ x ((moduleCreationMap φ y).adjoint
      (preModuleTensorMk φ z w : InteriorModuleTensor (E := E) φ))
  rw [moduleCreationMap_adjoint_mk]
  change interiorModuleTensorMk φ (⟪y, z⟫_(Bᵐᵒᵖ) • x) w =
    interiorModuleTensorMk φ x (φ (MulOpposite.unop ⟪y, z⟫_(Bᵐᵒᵖ)) w)
  exact interiorModuleTensorMk_balance φ (MulOpposite.unop ⟪y, z⟫_(Bᵐᵒᵖ)) x w

theorem tensor_endo (T : AdjointableMap B E E) :
    tensor φ T = interiorModuleTensorOperator φ T := rfl

theorem tensor_add (T S : AdjointableMap B E E') :
    tensor φ (T + S) = tensor φ T + tensor φ S := by
  apply AdjointableMap.toCLM_injective
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
  intro x y
  simp only [tensor_mk, AdjointableMap.coe_add_apply, map_add, LinearMap.add_apply]

theorem tensor_smul (a : ℂ) (T : AdjointableMap B E E') :
    tensor φ (a • T) = a • tensor φ T := by
  apply AdjointableMap.toCLM_injective
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
  intro x y
  simp only [tensor_mk, AdjointableMap.coe_smul_apply, map_smul, LinearMap.smul_apply]

def tensorCLM : AdjointableMap B E E' →L[ℂ]
    AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E') φ) :=
  LinearMap.mkContinuous
    { toFun := tensor φ
      map_add' := tensor_add φ
      map_smul' := tensor_smul φ }
    1 (fun T => by
      change ‖tensor φ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact tensor_norm_le φ T)

@[simp] theorem tensorCLM_apply (T : AdjointableMap B E E') :
    tensorCLM φ T = tensor φ T := rfl

theorem tensor_sub (T S : AdjointableMap B E E') :
    tensor φ (T - S) = tensor φ T - tensor φ S :=
  map_sub (tensorCLM φ) T S

theorem tensor_neg (T : AdjointableMap B E E') : tensor φ (-T) = -tensor φ T :=
  map_neg (tensorCLM φ) T

end BC4lean.KKTheory.RectangularInteriorModuleTensorOperator
