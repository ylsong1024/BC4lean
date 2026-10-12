import BC4lean.ModuleCreationMap
import BC4lean.CStarHomClosedRange

/-! # Composed creation maps on genuine completed interior tensors

For three Hilbert modules the two actual creation maps compose on elementary
first-pair tensors. Balancing, the full adjoint-composition formula and the
rectangular C-star identity give descent and a norm bound on the separated
first tensor. Completeness of the actual rectangular adjointable-map space
then extends this construction to the completed first tensor. No tensor
associator, tensor norm or unitary conclusion is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorAssociator

open UniformSpace
open scoped InnerProductSpace

variable {B C D E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

variable (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)

/-- The actual induced left B-representation on F tensor G. -/
def rightRepresentation : B →⋆ₙₐ[ℂ]
    AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ) :=
  (interiorModuleTensorOperatorHom ψ).toNonUnitalStarAlgHom.comp φ

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem rightRepresentation_mk (b : B) (y : F) (z : G) :
    rightRepresentation φ ψ b (interiorModuleTensorMk ψ y z) =
      interiorModuleTensorMk ψ (φ b y) z :=
  interiorModuleTensorOperator_mk ψ (φ b) y z

abbrev RightTensor := InteriorModuleTensor (E := E) (rightRepresentation φ ψ)
abbrev LeftTensor := InteriorModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ

/-- Composition of the actual two creation adjoint pairs. -/
def pureCreation (x : E) (y : F) :
    AdjointableMap D G (RightTensor (E := E) φ ψ) :=
  (moduleCreationMap (rightRepresentation φ ψ) x).comp (moduleCreationMap ψ y)

/-- This genuine operator-valued map is complex bilinear. -/
def pureCreationBilinear :
    E →ₗ[ℂ] F →ₗ[ℂ] AdjointableMap D G (RightTensor (E := E) φ ψ) where
  toFun x :=
    { toFun := pureCreation φ ψ x
      map_add' y y' := by
        ext z
        simp only [pureCreation, moduleCreationMap_add, AdjointableMap.comp_apply,
          AdjointableMap.coe_add_apply]
        exact (moduleCreationMap (rightRepresentation φ ψ) x).toCLM.map_add _ _
      map_smul' a y := by
        ext z
        simp only [pureCreation, moduleCreationMap_smul, AdjointableMap.comp_apply,
          AdjointableMap.coe_smul_apply]
        exact (moduleCreationMap (rightRepresentation φ ψ) x).toCLM.map_smul a _ }
  map_add' x x' := by
    ext y z
    change pureCreation φ ψ (x + x') y z =
      pureCreation φ ψ x y z + pureCreation φ ψ x' y z
    simp only [pureCreation, moduleCreationMap_add, AdjointableMap.comp_apply,
      AdjointableMap.coe_add_apply]
  map_smul' a x := by
    ext y z
    change pureCreation φ ψ (a • x) y z = a • pureCreation φ ψ x y z
    simp only [pureCreation, moduleCreationMap_smul, AdjointableMap.comp_apply,
      AdjointableMap.coe_smul_apply]

theorem pureCreation_balance (b : B) (x : E) (y : F) :
    pureCreationBilinear φ ψ (MulOpposite.op b • x) y =
      pureCreationBilinear φ ψ x (φ b y) := by
  apply AdjointableMap.ext
  intro z
  change interiorModuleTensorMk (rightRepresentation φ ψ) (MulOpposite.op b • x)
      (interiorModuleTensorMk ψ y z) =
    interiorModuleTensorMk (rightRepresentation φ ψ) x (interiorModuleTensorMk ψ (φ b y) z)
  rw [interiorModuleTensorMk_balance, rightRepresentation_mk]

/-- Both true creation adjoints give the elementary Gram identity. -/
theorem pureCreation_adjoint_comp (x x' : E) (y y' : F) :
    (pureCreation φ ψ x y).adjoint.comp (pureCreation φ ψ x' y') =
      ψ (MulOpposite.unop (moduleTensorPureInner φ x y x' y')) := by
  apply AdjointableMap.ext
  intro z
  simp only [pureCreation, AdjointableMap.adjoint_comp, AdjointableMap.comp_apply]
  rw [← AdjointableMap.comp_apply
    (moduleCreationMap (rightRepresentation φ ψ) x).adjoint
    (moduleCreationMap (rightRepresentation φ ψ) x'),
    moduleCreationMap_adjoint_comp]
  change (moduleCreationMap ψ y).adjoint
      (interiorModuleTensorOperator ψ (φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)))
        (interiorModuleTensorMk ψ y' z)) =
    ψ (MulOpposite.unop ⟪y, φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) y'⟫_(Cᵐᵒᵖ)) z
  rw [interiorModuleTensorOperator_mk]
  exact moduleCreationMap_adjoint_mk ψ y
    (φ (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) y') z

/-- Genuine descent through coefficient balancing. -/
def balancedCreation :
    BalancedModuleTensor (E := E) φ →ₗ[ℂ]
      AdjointableMap D G (RightTensor (E := E) φ ψ) :=
  moduleTensorLift φ (pureCreationBilinear φ ψ) (pureCreation_balance φ ψ)

@[simp] theorem balancedCreation_mk (x : E) (y : F) :
    balancedCreation φ ψ (moduleTensorMk φ x y) = pureCreation φ ψ x y := rfl

/-- The full coefficient pairing holds on arbitrary finite balanced sums. -/
theorem balancedCreation_pair (u v : BalancedModuleTensor (E := E) φ) (z w : G) :
    ⟪balancedCreation φ ψ u z, balancedCreation φ ψ v w⟫_(Dᵐᵒᵖ) =
      ⟪z, ψ (MulOpposite.unop (moduleTensorInner φ u v)) w⟫_(Dᵐᵒᵖ) := by
  induction u using moduleTensor_induction φ with
  | h0 =>
    simp [CStarModule.inner_zero_left
      (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ)]
  | hθ x y =>
    induction v using moduleTensor_induction φ with
    | h0 =>
      simp [CStarModule.inner_zero_right
        (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ)]
    | hθ x' y' =>
      rw [balancedCreation_mk, balancedCreation_mk,
        (pureCreation φ ψ x y).adjoint_identity]
      change ⟪z, ((pureCreation φ ψ x y).adjoint.comp (pureCreation φ ψ x' y')) w⟫_
        (Dᵐᵒᵖ) = _
      rw [pureCreation_adjoint_comp]
      rfl
    | hadd v w' hv hw =>
      simp only [map_add, AdjointableMap.coe_add_apply,
        CStarModule.inner_add_right (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ),
        MulOpposite.unop_add, CStarModule.inner_add_right (A := Dᵐᵒᵖ) (E := G), hv, hw]
  | hadd u v' hu hv =>
    simp only [map_add, LinearMap.add_apply, AdjointableMap.coe_add_apply,
      CStarModule.inner_add_left (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ),
      MulOpposite.unop_add, CStarModule.inner_add_right (A := Dᵐᵒᵖ) (E := G), hu, hv]

theorem balancedCreation_adjoint_comp (u v : BalancedModuleTensor (E := E) φ) :
    (balancedCreation φ ψ u).adjoint.comp (balancedCreation φ ψ v) =
      ψ (MulOpposite.unop (moduleTensorInner φ u v)) := by
  apply AdjointableMap.ext
  intro w
  apply module_inner_ext_right (B := D)
  intro z
  change ⟪z, (balancedCreation φ ψ u).adjointCLM (balancedCreation φ ψ v w)⟫_
    (Dᵐᵒᵖ) = _
  rw [← (balancedCreation φ ψ u).adjoint_identity]
  exact balancedCreation_pair φ ψ u v z w

/-- The actual first tensor radical is annihilated, by the rectangular C-star identity. -/
theorem balancedCreation_null {u : BalancedModuleTensor (E := E) φ}
    (hu : u ∈ moduleTensorNull φ) : balancedCreation φ ψ u = 0 := by
  rw [mem_moduleTensorNull_iff] at hu
  have hsq : ‖balancedCreation φ ψ u‖ ^ 2 = 0 := by
    change ‖(balancedCreation φ ψ u).toCLM‖ ^ 2 = 0
    rw [← AdjointableMap.norm_toCLM_adjoint_comp_self, balancedCreation_adjoint_comp,
      hu, MulOpposite.unop_zero, map_zero]
    simp
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (balancedCreation φ ψ u)])

/-- The actual separated first tensor now maps into the rectangular adjointable space. -/
def preCreation : PreHilbertModuleTensor (E := E) φ →ₗ[ℂ]
    AdjointableMap D G (RightTensor (E := E) φ ψ) :=
  (moduleTensorNull φ).liftQ (balancedCreation φ ψ) (fun _ hu => balancedCreation_null φ ψ hu)

@[simp] theorem preCreation_mk (x : E) (y : F) :
    preCreation φ ψ (preModuleTensorMk φ x y) = pureCreation φ ψ x y := rfl

theorem preCreation_adjoint_comp (u v : PreHilbertModuleTensor (E := E) φ) :
    (preCreation φ ψ u).adjoint.comp (preCreation φ ψ v) =
      ψ (MulOpposite.unop ⟪u, v⟫_(Cᵐᵒᵖ)) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact balancedCreation_adjoint_comp φ ψ u v

/-- The operator-valued extension is bounded by the actual first tensor norm. -/
theorem preCreation_norm_le (u : PreHilbertModuleTensor (E := E) φ) :
    ‖preCreation φ ψ u‖ ≤ ‖u‖ := by
  have hsq : ‖preCreation φ ψ u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    calc
      ‖preCreation φ ψ u‖ ^ 2 =
          ‖((preCreation φ ψ u).adjoint.comp (preCreation φ ψ u)).toCLM‖ :=
        (AdjointableMap.norm_toCLM_adjoint_comp_self _).symm
      _ = ‖ψ (MulOpposite.unop ⟪u, u⟫_(Cᵐᵒᵖ))‖ := by rw [preCreation_adjoint_comp]; rfl
      _ ≤ ‖⟪u, u⟫_(Cᵐᵒᵖ)‖ := by
        simpa only [MulOpposite.norm_unop] using
          NonUnitalStarAlgHom.norm_apply_le ψ (MulOpposite.unop ⟪u, u⟫_(Cᵐᵒᵖ))
      _ = ‖u‖ ^ 2 := (CStarModule.norm_sq_eq (Cᵐᵒᵖ)).symm
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by decide : 2 ≠ 0)).mp hsq

def preCreationCLM : PreHilbertModuleTensor (E := E) φ →L[ℂ]
    AdjointableMap D G (RightTensor (E := E) φ ψ) :=
  (preCreation φ ψ).mkContinuous 1 (fun u => by
    simpa only [one_mul] using preCreation_norm_le φ ψ u)

/-- Completeness of the actual rectangular operator space supplies the extension. -/
def creation : InteriorModuleTensor (E := E) φ →L[ℂ]
    AdjointableMap D G (RightTensor (E := E) φ ψ) :=
  (preCreationCLM φ ψ).fromCompletion

@[simp] theorem creation_coe (u : PreHilbertModuleTensor (E := E) φ) :
    creation φ ψ (u : InteriorModuleTensor φ) = preCreation φ ψ u :=
  ContinuousLinearMap.fromCompletion_apply_coe (preCreationCLM φ ψ) u

@[simp] theorem creation_mk (x : E) (y : F) :
    creation φ ψ (interiorModuleTensorMk φ x y) = pureCreation φ ψ x y :=
  creation_coe φ ψ (preModuleTensorMk φ x y)

/-- The full pairing survives completion of the first tensor factor. -/
theorem creation_pair (u v : InteriorModuleTensor (E := E) φ) (z w : G) :
    ⟪creation φ ψ u z, creation φ ψ v w⟫_(Dᵐᵒᵖ) =
      ⟪z, ψ (MulOpposite.unop ⟪u, v⟫_(Cᵐᵒᵖ)) w⟫_(Dᵐᵒᵖ) := by
  induction u, v using Completion.induction_on₂ with
  | hp =>
    have h₁ : Continuous (fun p : InteriorModuleTensor (E := E) φ ×
        InteriorModuleTensor (E := E) φ => creation φ ψ p.1 z) :=
      (AdjointableMap.toCLMContinuousLinearMap.continuous.comp
        ((creation φ ψ).continuous.comp continuous_fst)).clm_apply continuous_const
    have h₂ : Continuous (fun p : InteriorModuleTensor (E := E) φ ×
        InteriorModuleTensor (E := E) φ => creation φ ψ p.2 w) :=
      (AdjointableMap.toCLMContinuousLinearMap.continuous.comp
        ((creation φ ψ).continuous.comp continuous_snd)).clm_apply continuous_const
    have hi : Continuous (fun p : InteriorModuleTensor (E := E) φ ×
        InteriorModuleTensor (E := E) φ => MulOpposite.unop ⟪p.1, p.2⟫_(Cᵐᵒᵖ)) :=
      MulOpposite.continuous_unop.comp CStarModule.continuous_inner
    have hψ := (AdjointableMap.toCLMContinuousLinearMap.continuous.comp
      ((nonUnitalCStarHomCLM ψ).continuous.comp hi)).clm_apply (continuous_const (y := w))
    exact isClosed_eq (CStarModule.continuous_inner.comp (h₁.prodMk h₂))
      (CStarModule.continuous_inner.comp (continuous_const.prodMk hψ))
  | ih u v =>
    rw [creation_coe, creation_coe, completionInner_coe]
    rw [(preCreation φ ψ u).adjoint_identity]
    change ⟪z, ((preCreation φ ψ u).adjoint.comp (preCreation φ ψ v)) w⟫_(Dᵐᵒᵖ) = _
    rw [preCreation_adjoint_comp]

theorem creation_adjoint_comp (u v : InteriorModuleTensor (E := E) φ) :
    (creation φ ψ u).adjoint.comp (creation φ ψ v) =
      ψ (MulOpposite.unop ⟪u, v⟫_(Cᵐᵒᵖ)) := by
  apply AdjointableMap.ext
  intro w
  apply module_inner_ext_right (B := D)
  intro z
  change ⟪z, (creation φ ψ u).adjointCLM (creation φ ψ v w)⟫_(Dᵐᵒᵖ) = _
  rw [← (creation φ ψ u).adjoint_identity]
  exact creation_pair φ ψ u v z w

/-- C-balancing is proved before the second tensor quotient is formed. -/
theorem creation_balance (c : C) (u : InteriorModuleTensor (E := E) φ) :
    creation φ ψ (MulOpposite.op c • u) = (creation φ ψ u).comp (ψ c) := by
  apply AdjointableMap.ext
  intro z
  change creation φ ψ (MulOpposite.op c • u) z = creation φ ψ u (ψ c z)
  induction u using Completion.induction_on with
  | hp =>
    have hsmul : Continuous (fun u : InteriorModuleTensor (E := E) φ =>
        MulOpposite.op c • u) :=
      continuous_completion_op_smul
        (B := C) (E := PreHilbertModuleTensor (E := E) φ) (MulOpposite.op c)
    have h₁ : Continuous (fun u : InteriorModuleTensor (E := E) φ =>
        creation φ ψ (MulOpposite.op c • u) z) :=
      ((AdjointableMap.toCLMContinuousLinearMap
        (B := D) (E := G) (F := RightTensor (E := E) φ ψ)).continuous.comp
          ((creation φ ψ).continuous.comp hsmul)).clm_apply (continuous_const (y := z))
    have h₂ : Continuous (fun u : InteriorModuleTensor (E := E) φ =>
        creation φ ψ u (ψ c z)) :=
      ((AdjointableMap.toCLMContinuousLinearMap
        (B := D) (E := G) (F := RightTensor (E := E) φ ψ)).continuous.comp
          (creation φ ψ).continuous).clm_apply (continuous_const (y := ψ c z))
    exact isClosed_eq h₁ h₂
  | ih u =>
    rw [completion_op_smul_coe, creation_coe, creation_coe]
    induction u using preModuleTensor_induction φ with
    | h0 =>
      have hzero : MulOpposite.op c • (0 : PreHilbertModuleTensor (E := E) φ) = 0 :=
        (moduleCoefficientActionLinear (MulOpposite.op c) :
          PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] PreHilbertModuleTensor (E := E) φ).map_zero
      simp only [hzero, map_zero, AdjointableMap.coe_zero_apply]
    | hθ x y =>
      rw [preModuleTensor_smul_mk, preCreation_mk, preCreation_mk]
      simp only [pureCreation, moduleCreationMap_balance, AdjointableMap.comp_apply]
    | hadd u v hu hv =>
      simp only [module_smul_add, map_add, AdjointableMap.coe_add_apply, hu, hv]

end BC4lean.KKTheory.InteriorModuleTensorAssociator
