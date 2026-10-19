import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.ModuleCreationMap
import BC4lean.StandardModuleOperator
import BC4lean.InteriorModuleTensorIsometry

/-! # The standard-module tensor acts by a genuine pairing isometry

For an arbitrary, possibly degenerate, representation φ,
the actual completed tensor B ⊗_φ F embeds in F by b ⊗ y ↦ φ(b)y.
No surjectivity or nondegeneracy premise is used.
-/

noncomputable section
namespace BC4lean.KKTheory.StandardModuleTensorEmbedding
open scoped InnerProductSpace

variable {B C F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

def bilinear : Bᵐᵒᵖ →ₗ[ℂ] F →ₗ[ℂ] F where
  toFun b := (φ (MulOpposite.unop b)).toCLM.toLinearMap
  map_add' b c := by
    apply LinearMap.ext
    intro y
    change φ (MulOpposite.unop (b + c)) y = _
    rw [MulOpposite.unop_add, map_add]
    rfl
  map_smul' z b := by
    apply LinearMap.ext
    intro y
    change φ (MulOpposite.unop (z • b)) y = _
    rw [MulOpposite.unop_smul, map_smul]
    rfl

omit [PartialOrder B] [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace F] in
theorem bilinear_balance (b : B) (c : Bᵐᵒᵖ) (y : F) :
    bilinear φ (MulOpposite.op b • c) y = bilinear φ c (φ b y) := by
  change φ (MulOpposite.unop c * b) y = φ (MulOpposite.unop c) (φ b y)
  rw [map_mul]
  rfl

def balancedMap : BalancedModuleTensor (E := Bᵐᵒᵖ) φ →ₗ[ℂ] F :=
  moduleTensorLift φ (bilinear φ) (bilinear_balance φ)

omit [PartialOrder B] [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace F] in
@[simp] theorem balancedMap_mk (b : Bᵐᵒᵖ) (y : F) :
    balancedMap φ (moduleTensorMk φ b y) = φ (MulOpposite.unop b) y := rfl

omit [StarOrderedRing C] [CompleteSpace F] in
theorem balancedMap_inner (u v : BalancedModuleTensor (E := Bᵐᵒᵖ) φ) :
    ⟪balancedMap φ u, balancedMap φ v⟫_(Cᵐᵒᵖ) = moduleTensorInner φ u v := by
  revert v
  refine moduleTensor_induction φ u ?_ ?_ ?_
  · intro v
    simp only [map_zero, LinearMap.zero_apply]
    exact CStarModule.inner_zero_left (A := Cᵐᵒᵖ) (E := F)
  · intro b y v
    refine moduleTensor_induction φ v ?_ ?_ ?_
    · simp only [map_zero]
      exact CStarModule.inner_zero_right (A := Cᵐᵒᵖ) (E := F)
    · intro c z
      rw [balancedMap_mk, balancedMap_mk, moduleTensorInner_mk_mk]
      change ⟪φ (MulOpposite.unop b) y, φ (MulOpposite.unop c) z⟫_(Cᵐᵒᵖ) =
        ⟪y, φ (star (MulOpposite.unop b) * MulOpposite.unop c) z⟫_(Cᵐᵒᵖ)
      rw [map_mul, map_star]
      exact (φ (MulOpposite.unop b)).adjoint_identity y
        (φ (MulOpposite.unop c) z)
    · intro v w hv hw
      simp only [map_add]
      rw [CStarModule.inner_add_right (A := Cᵐᵒᵖ) (E := F), hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply]
    rw [CStarModule.inner_add_left (A := Cᵐᵒᵖ) (E := F), hu w, hv w]

/-- The whole pairing is preserved on the actual completed tensor. -/
def isometry : InteriorModuleTensor (E := Bᵐᵒᵖ) φ →ₗᵢ[ℂ] F :=
  InteriorModuleTensorFormCompletion.completedIsometry φ
    (balancedMap φ) (balancedMap_inner φ)

@[simp] theorem isometry_mk (b : Bᵐᵒᵖ) (y : F) :
    isometry φ (interiorModuleTensorMk φ b y) = φ (MulOpposite.unop b) y :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk φ
    (balancedMap φ) (balancedMap_inner φ) b y

theorem isometry_inner (u v : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    ⟪isometry φ u, isometry φ v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) :=
  InteriorModuleTensorFormCompletion.completedIsometry_inner φ
    (balancedMap φ) (balancedMap_inner φ) u v

/-- The actual pairing embedding respects the right coefficient action.
The proof uses pure-tensor density and the represented operator's original
coefficient linearity; it does not require surjectivity of the embedding. -/
theorem isometry_map_op_smul (a : Cᵐᵒᵖ)
    (u : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    isometry φ (a • u) = a • isometry φ u := by
  have h : (isometry φ).toContinuousLinearMap.comp
      (completionCoefficientAction (B := C)
        (E := InteriorModuleTensor (E := Bᵐᵒᵖ) φ) a) =
      (completionCoefficientAction (B := C) (E := F) a).comp
        (isometry φ).toContinuousLinearMap := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro b y
    change isometry φ (a • interiorModuleTensorMk φ b y) =
      a • isometry φ (interiorModuleTensorMk φ b y)
    rw [interiorModuleTensor_smul_mk, isometry_mk, isometry_mk,
      (φ (MulOpposite.unop b)).map_op_smul]
  exact DFunLike.congr_fun h u

/-- Left multiplication in the standard factor becomes the actual represented
operator after the pairing embedding, including for degenerate φ. -/
theorem isometry_intertwines (b : B)
    (u : InteriorModuleTensor (E := Bᵐᵒᵖ) φ) :
    isometry φ (interiorModuleTensorOperator φ (standardLeftMul b) u) =
      φ b (isometry φ u) := by
  have h : (isometry φ).toContinuousLinearMap.comp
      (interiorModuleTensorOperator φ (standardLeftMul b)).toCLM =
        (φ b).toCLM.comp (isometry φ).toContinuousLinearMap := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro c y
    change isometry φ (interiorModuleTensorOperator φ (standardLeftMul b)
      (interiorModuleTensorMk φ c y)) =
        φ b (isometry φ (interiorModuleTensorMk φ c y))
    rw [interiorModuleTensorOperator_mk, isometry_mk, isometry_mk,
      standardLeftMul_apply, MulOpposite.unop_op, map_mul]
    rfl
  exact DFunLike.congr_fun h u

end BC4lean.KKTheory.StandardModuleTensorEmbedding
