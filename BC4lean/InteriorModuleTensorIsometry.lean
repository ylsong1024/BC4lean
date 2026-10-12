import BC4lean.InteriorModuleTensor
import BC4lean.GradedHilbertModule

/-! # Compatible factor isometries on the actual interior tensor

A pair of factor isometries descends through coefficient balancing when the
second factor intertwines the left representation with the coefficient
automorphism of the first factor. Its inner-product transport then preserves
the actual null quotient and its norm. We extend the resulting isometry to
the genuine completion. No tensor isometry or tensor inner-product law is
assumed in the input data.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open UniformSpace

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- Genuine compatible data on the two factors. The coefficient automorphisms
may be nontrivial, and the left representation may be nonunital or degenerate. -/
structure ModuleTensorFactorIsometry (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) where
  coefficientB : B ≃⋆ₐ[ℂ] B
  coefficientC : C ≃⋆ₐ[ℂ] C
  first : E ≃ₗᵢ[ℂ] E
  second : F ≃ₗᵢ[ℂ] F
  first_smul : ∀ a x, first (a • x) = opStarAlgEquiv coefficientB a • first x
  first_inner : ∀ x y,
    ⟪first x, first y⟫_(Bᵐᵒᵖ) = opStarAlgEquiv coefficientB ⟪x, y⟫_(Bᵐᵒᵖ)
  second_inner : ∀ x y,
    ⟪second x, second y⟫_(Cᵐᵒᵖ) = opStarAlgEquiv coefficientC ⟪x, y⟫_(Cᵐᵒᵖ)
  intertwines : ∀ b y, second (φ b y) = φ (coefficientB b) (second y)

namespace ModuleTensorFactorIsometry

variable {φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F}

/-- The inverse factor maps satisfy the inverse compatibility laws. -/
def symm (W : ModuleTensorFactorIsometry (E := E) φ) :
    ModuleTensorFactorIsometry (E := E) φ where
  coefficientB := W.coefficientB.symm
  coefficientC := W.coefficientC.symm
  first := W.first.symm
  second := W.second.symm
  first_smul a x := by
    apply W.first.injective
    rw [W.first_smul]
    simp [opStarAlgEquiv_apply]
  first_inner x y := by
    have h := congrArg (opStarAlgEquiv W.coefficientB.symm)
      (W.first_inner (W.first.symm x) (W.first.symm y))
    simpa only [LinearIsometryEquiv.apply_symm_apply, opStarAlgEquiv_apply,
      MulOpposite.unop_op, StarAlgEquiv.symm_apply_apply,
      MulOpposite.op_unop] using h.symm
  second_inner x y := by
    have h := congrArg (opStarAlgEquiv W.coefficientC.symm)
      (W.second_inner (W.second.symm x) (W.second.symm y))
    simpa only [LinearIsometryEquiv.apply_symm_apply, opStarAlgEquiv_apply,
      MulOpposite.unop_op, StarAlgEquiv.symm_apply_apply,
      MulOpposite.op_unop] using h.symm
  intertwines b y := by
    apply W.second.injective
    simpa using (W.intertwines (W.coefficientB.symm b) (W.second.symm y)).symm

/-- Apply the two genuine factor maps to an elementary balanced tensor. -/
def balancedBilinear (W : ModuleTensorFactorIsometry (E := E) φ) :
    E →ₗ[ℂ] F →ₗ[ℂ] BalancedModuleTensor (E := E) φ where
  toFun x := (moduleTensorMk φ (W.first x)).comp W.second.toLinearEquiv.toLinearMap
  map_add' x y := by ext z; simp
  map_smul' a x := by ext z; simp

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
theorem balancedBilinear_balance (W : ModuleTensorFactorIsometry (E := E) φ)
    (b : B) (x : E) (y : F) :
    W.balancedBilinear (MulOpposite.op b • x) y = W.balancedBilinear x (φ b y) := by
  change moduleTensorMk φ (W.first (MulOpposite.op b • x)) (W.second y) =
    moduleTensorMk φ (W.first x) (W.second (φ b y))
  rw [W.first_smul, W.intertwines]
  exact moduleTensorMk_balance φ (W.coefficientB b) (W.first x) (W.second y)

/-- Descent through the actual coefficient-balancing quotient. -/
def balancedMap (W : ModuleTensorFactorIsometry (E := E) φ) :
    BalancedModuleTensor (E := E) φ →ₗ[ℂ] BalancedModuleTensor (E := E) φ :=
  moduleTensorLift φ W.balancedBilinear W.balancedBilinear_balance

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem balancedMap_mk (W : ModuleTensorFactorIsometry (E := E) φ)
    (x : E) (y : F) :
    W.balancedMap (moduleTensorMk φ x y) = moduleTensorMk φ (W.first x) (W.second y) := rfl

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- On elementary tensors the constructed pairing transports by the actual
second coefficient automorphism. -/
theorem pureInner_map (W : ModuleTensorFactorIsometry (E := E) φ)
    (x x' : E) (y y' : F) :
    moduleTensorPureInner φ (W.first x) (W.second y) (W.first x') (W.second y') =
      opStarAlgEquiv W.coefficientC (moduleTensorPureInner φ x y x' y') := by
  unfold moduleTensorPureInner
  rw [W.first_inner]
  change ⟪W.second y,
      φ (W.coefficientB (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ))) (W.second y')⟫_(Cᵐᵒᵖ) = _
  rw [← W.intertwines, W.second_inner]

omit [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace E] [CompleteSpace F] in
/-- Sesquilinearity proves transport on arbitrary balanced tensors. -/
theorem balancedMap_inner (W : ModuleTensorFactorIsometry (E := E) φ)
    (u v : BalancedModuleTensor (E := E) φ) :
    moduleTensorInner φ (W.balancedMap u) (W.balancedMap v) =
      opStarAlgEquiv W.coefficientC (moduleTensorInner φ u v) := by
  induction u using moduleTensor_induction φ with
  | h0 => simp
  | hθ x y =>
    induction v using moduleTensor_induction φ with
    | h0 => simp
    | hθ x' y' =>
      simpa only [balancedMap_mk, moduleTensorInner_mk_mk] using W.pureInner_map x x' y y'
    | hadd v w hv hw => simp only [map_add, hv, hw]
  | hadd u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]

/-- The actual null kernel is invariant; this follows from the proved inner
transport and the null-square equivalence. -/
theorem balancedMap_null (W : ModuleTensorFactorIsometry (E := E) φ)
    {u : BalancedModuleTensor (E := E) φ} (hu : u ∈ moduleTensorNull φ) :
    W.balancedMap u ∈ moduleTensorNull φ := by
  rw [mem_moduleTensorNull_iff] at hu ⊢
  rw [W.balancedMap_inner, hu, map_zero]

/-- The descended linear map on the actual separated pre-Hilbert tensor. -/
def preMap (W : ModuleTensorFactorIsometry (E := E) φ) :
    PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] PreHilbertModuleTensor (E := E) φ :=
  (moduleTensorNull φ).mapQ (moduleTensorNull φ) W.balancedMap
    (fun _ hu => W.balancedMap_null hu)

@[simp] theorem preMap_mk (W : ModuleTensorFactorIsometry (E := E) φ)
    (x : E) (y : F) :
    W.preMap (preModuleTensorMk φ x y) = preModuleTensorMk φ (W.first x) (W.second y) := rfl

theorem preMap_inner (W : ModuleTensorFactorIsometry (E := E) φ)
    (u v : PreHilbertModuleTensor (E := E) φ) :
    ⟪W.preMap u, W.preMap v⟫_(Cᵐᵒᵖ) = opStarAlgEquiv W.coefficientC ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact W.balancedMap_inner u v

theorem preMap_norm (W : ModuleTensorFactorIsometry (E := E) φ)
    (u : PreHilbertModuleTensor (E := E) φ) : ‖W.preMap u‖ = ‖u‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), W.preMap_inner,
    StarAlgEquiv.norm_map (opStarAlgEquiv W.coefficientC),
    ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)]

/-- Inverses are proved on pure tensors and then on the entire null quotient. -/
theorem symm_preMap_preMap (W : ModuleTensorFactorIsometry (E := E) φ)
    (u : PreHilbertModuleTensor (E := E) φ) : W.symm.preMap (W.preMap u) = u := by
  induction u using preModuleTensor_induction φ with
  | h0 => simp
  | hθ x y => simp [symm]
  | hadd u v hu hv => simp only [map_add, hu, hv]

theorem preMap_symm_preMap (W : ModuleTensorFactorIsometry (E := E) φ)
    (u : PreHilbertModuleTensor (E := E) φ) : W.preMap (W.symm.preMap u) = u := by
  induction u using preModuleTensor_induction φ with
  | h0 => simp
  | hθ x y => simp [symm]
  | hadd u v hu hv => simp only [map_add, hu, hv]

/-- An actual isometry equivalence of the constructed pre-Hilbert tensor. -/
def preIsometry (W : ModuleTensorFactorIsometry (E := E) φ) :
    PreHilbertModuleTensor (E := E) φ ≃ₗᵢ[ℂ] PreHilbertModuleTensor (E := E) φ where
  toFun := W.preMap
  invFun := W.symm.preMap
  left_inv := W.symm_preMap_preMap
  right_inv := W.preMap_symm_preMap
  map_add' := W.preMap.map_add
  map_smul' := W.preMap.map_smul
  norm_map' := W.preMap_norm

/-- Extend the proved pre-Hilbert isometry to the genuine norm completion. -/
def completionMap (W : ModuleTensorFactorIsometry (E := E) φ) :
    InteriorModuleTensor (E := E) φ →L[ℂ] InteriorModuleTensor (E := E) φ :=
  W.preIsometry.toLinearIsometry.toContinuousLinearMap.completion

@[simp] theorem completionMap_coe (W : ModuleTensorFactorIsometry (E := E) φ)
    (u : PreHilbertModuleTensor (E := E) φ) :
    W.completionMap (u : InteriorModuleTensor (E := E) φ) = (W.preMap u : InteriorModuleTensor φ) :=
  ContinuousLinearMap.completion_apply_coe _ u

theorem completionMap_isometry (W : ModuleTensorFactorIsometry (E := E) φ) :
    Isometry W.completionMap := W.preIsometry.isometry.completion_map

theorem symm_completionMap_completionMap (W : ModuleTensorFactorIsometry (E := E) φ)
    (u : InteriorModuleTensor (E := E) φ) : W.symm.completionMap (W.completionMap u) = u := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_id
  | ih u => simp only [completionMap_coe, W.symm_preMap_preMap]

theorem completionMap_symm_completionMap (W : ModuleTensorFactorIsometry (E := E) φ)
    (u : InteriorModuleTensor (E := E) φ) : W.completionMap (W.symm.completionMap u) = u := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_id
  | ih u => simp only [completionMap_coe, W.preMap_symm_preMap]

/-- The actual completed interior-tensor isometry equivalence. -/
def interiorIsometry (W : ModuleTensorFactorIsometry (E := E) φ) :
    InteriorModuleTensor (E := E) φ ≃ₗᵢ[ℂ] InteriorModuleTensor (E := E) φ where
  toFun := W.completionMap
  invFun := W.symm.completionMap
  left_inv := W.symm_completionMap_completionMap
  right_inv := W.completionMap_symm_completionMap
  map_add' := W.completionMap.map_add
  map_smul' := W.completionMap.map_smul
  norm_map' u := by
    change ‖W.completionMap u‖ = ‖u‖
    simpa only [map_zero, dist_zero_right] using W.completionMap_isometry.dist_eq u 0

@[simp] theorem interiorIsometry_mk (W : ModuleTensorFactorIsometry (E := E) φ)
    (x : E) (y : F) :
    W.interiorIsometry (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk φ (W.first x) (W.second y) := by
  exact W.completionMap_coe (preModuleTensorMk φ x y)

/-- The coefficient inner transport survives the actual completion. -/
theorem interiorIsometry_inner (W : ModuleTensorFactorIsometry (E := E) φ)
    (u v : InteriorModuleTensor (E := E) φ) :
    ⟪W.interiorIsometry u, W.interiorIsometry v⟫_(Cᵐᵒᵖ) =
      opStarAlgEquiv W.coefficientC ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u, v using Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (continuous_completionInner_comp
        (W.interiorIsometry.continuous.comp continuous_fst)
        (W.interiorIsometry.continuous.comp continuous_snd))
      ((StarAlgEquiv.isometry (opStarAlgEquiv W.coefficientC)).continuous.comp
        continuous_completionInner)
  | ih u v =>
    change ⟪W.completionMap (u : InteriorModuleTensor φ),
      W.completionMap (v : InteriorModuleTensor φ)⟫_(Cᵐᵒᵖ) = _
    rw [completionMap_coe, completionMap_coe, completionInner_coe, completionInner_coe]
    exact W.preMap_inner u v

/-- Completed linear maps are determined by pure tensors: first on their
actual separated span, then by density of the completion embedding. -/
theorem interiorModuleTensor_clm_ext
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f g : InteriorModuleTensor (E := E) φ →L[ℂ] P}
    (h : ∀ x y, f (interiorModuleTensorMk φ x y) = g (interiorModuleTensorMk φ x y)) :
    f = g := by
  apply ContinuousLinearMap.ext_on (interiorModuleTensor_span_dense φ)
  rintro z ⟨⟨x, y⟩, rfl⟩
  exact h x y

end ModuleTensorFactorIsometry
end BC4lean.KKTheory
