import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.ModuleTensorOperator

/-! # A genuine interior-tensor embedding from a second-factor isometry

An actual coefficient-linear, pairing-preserving second-factor embedding
intertwining the left representations gives an actual isometric embedding
of the completed interior tensors. The map is built on balanced tensors,
its coefficient pairing is proved there, and the proved form isometry is
extended through the actual radical quotient and completion. Neither
surjectivity nor an isometry of tensor products is an input hypothesis.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B C E F G : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- Concrete data on the second factors; no tensor-product conclusion is assumed. -/
structure ModuleTensorSecondFactorIsometry
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C G G) where
  second : F →ₗᵢ[ℂ] G
  map_op_smul : ∀ (a : Cᵐᵒᵖ) (y : F), second (a • y) = a • second y
  inner_map : ∀ y z, ⟪second y, second z⟫_(Cᵐᵒᵖ) = ⟪y, z⟫_(Cᵐᵒᵖ)
  intertwines : ∀ b y, second (φ b y) = ψ b (second y)

namespace ModuleTensorSecondFactorIsometry

variable {φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F}
  {ψ : B →⋆ₙₐ[ℂ] AdjointableMap C G G}

/-- Apply the given embedding to the second elementary factor. -/
def bilinear (W : ModuleTensorSecondFactorIsometry φ ψ) :
    E →ₗ[ℂ] F →ₗ[ℂ] InteriorModuleTensor (E := E) ψ where
  toFun x := (interiorModuleTensorMk ψ x).comp W.second.toLinearMap
  map_add' x y := by ext z; simp
  map_smul' a x := by ext z; simp

omit [CompleteSpace F] in
/-- Intertwining of the left actions proves actual coefficient balancing. -/
theorem bilinear_balance (W : ModuleTensorSecondFactorIsometry φ ψ)
    (b : B) (x : E) (y : F) :
    W.bilinear (MulOpposite.op b • x) y = W.bilinear x (φ b y) := by
  change interiorModuleTensorMk ψ (MulOpposite.op b • x) (W.second y) =
    interiorModuleTensorMk ψ x (W.second (φ b y))
  rw [interiorModuleTensorMk_balance, W.intertwines]

/-- The actual balanced-tensor linear map into the completed target module. -/
def balancedMap (W : ModuleTensorSecondFactorIsometry φ ψ) :
    BalancedModuleTensor (E := E) φ →ₗ[ℂ] InteriorModuleTensor (E := E) ψ :=
  moduleTensorLift φ W.bilinear W.bilinear_balance

omit [CompleteSpace F] in
@[simp] theorem balancedMap_mk (W : ModuleTensorSecondFactorIsometry φ ψ)
    (x : E) (y : F) :
    W.balancedMap (moduleTensorMk φ x y) = interiorModuleTensorMk ψ x (W.second y) := rfl

omit [CompleteSpace F] in
/-- Pairing preservation is proved on arbitrary balanced tensors by sesquilinearity. -/
theorem balancedMap_inner (W : ModuleTensorSecondFactorIsometry φ ψ)
    (u v : BalancedModuleTensor (E := E) φ) :
    ⟪W.balancedMap u, W.balancedMap v⟫_(Cᵐᵒᵖ) = moduleTensorInner φ u v := by
  revert v
  refine moduleTensor_induction φ u ?_ ?_ ?_
  · intro v
    simp only [map_zero, LinearMap.zero_apply]
    exact CStarModule.inner_zero_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := E) ψ)
  · intro x y v
    refine moduleTensor_induction φ v ?_ ?_ ?_
    · simp only [map_zero]
      exact CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := E) ψ)
    · intro x' y'
      rw [balancedMap_mk, balancedMap_mk, interiorModuleTensorInner_mk_mk,
        moduleTensorInner_mk_mk]
      unfold moduleTensorPureInner
      rw [← W.intertwines, W.inner_map]
    · intro v w hv hw
      simp only [map_add]
      rw [CStarModule.inner_add_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := E) ψ), hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply]
    rw [CStarModule.inner_add_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := E) ψ), hu v, hw v]

/-- The genuine isometric embedding of the completed interior tensors. -/
def interiorIsometry (W : ModuleTensorSecondFactorIsometry φ ψ) :
    InteriorModuleTensor (E := E) φ →ₗᵢ[ℂ] InteriorModuleTensor (E := E) ψ :=
  InteriorModuleTensorFormCompletion.completedIsometry φ W.balancedMap W.balancedMap_inner

@[simp] theorem interiorIsometry_mk (W : ModuleTensorSecondFactorIsometry φ ψ)
    (x : E) (y : F) :
    W.interiorIsometry (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk ψ x (W.second y) :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x y

/-- The constructed isometry preserves the whole completed coefficient pairing. -/
theorem interiorIsometry_inner (W : ModuleTensorSecondFactorIsometry φ ψ)
    (u v : InteriorModuleTensor (E := E) φ) :
    ⟪W.interiorIsometry u, W.interiorIsometry v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) :=
  InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _ u v

/-- Right coefficient linearity extends from elementary tensors by their proved density. -/
@[simp] theorem interiorIsometry_map_op_smul (W : ModuleTensorSecondFactorIsometry φ ψ)
    (a : Cᵐᵒᵖ) (u : InteriorModuleTensor (E := E) φ) :
    W.interiorIsometry (a • u) = a • W.interiorIsometry u := by
  let L := (W.interiorIsometry (E := E)).toContinuousLinearMap
  have h : L.comp (completionCoefficientAction (B := C)
      (E := InteriorModuleTensor (E := E) φ) a) =
      (completionCoefficientAction (B := C)
        (E := InteriorModuleTensor (E := E) ψ) a).comp L := by
    apply ContinuousLinearMap.ext_on (interiorModuleTensor_span_dense φ)
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change W.interiorIsometry (a • interiorModuleTensorMk φ x y) =
      a • W.interiorIsometry (interiorModuleTensorMk φ x y)
    rw [interiorModuleTensor_smul_mk, interiorIsometry_mk, interiorIsometry_mk,
      W.map_op_smul, interiorModuleTensor_smul_mk]
  exact DFunLike.congr_fun h u

/-- The embedding intertwines actual first-factor operator amplification. -/
theorem interiorIsometry_operator (W : ModuleTensorSecondFactorIsometry φ ψ)
    (T : AdjointableMap B E E) (u : InteriorModuleTensor (E := E) φ) :
    W.interiorIsometry (interiorModuleTensorOperator φ T u) =
      interiorModuleTensorOperator ψ T (W.interiorIsometry u) := by
  let L := (W.interiorIsometry (E := E)).toContinuousLinearMap
  have h : L.comp (interiorModuleTensorOperator φ T).toCLM =
      (interiorModuleTensorOperator ψ T).toCLM.comp L := by
    apply ContinuousLinearMap.ext_on (interiorModuleTensor_span_dense φ)
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change W.interiorIsometry
        (interiorModuleTensorOperator φ T (interiorModuleTensorMk φ x y)) =
      interiorModuleTensorOperator ψ T (W.interiorIsometry (interiorModuleTensorMk φ x y))
    rw [interiorModuleTensorOperator_mk, interiorIsometry_mk, interiorIsometry_mk,
      interiorModuleTensorOperator_mk]
  exact DFunLike.congr_fun h u

end ModuleTensorSecondFactorIsometry
end BC4lean.KKTheory
