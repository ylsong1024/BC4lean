import BC4lean.InteriorModuleTensorCreationComposition
import BC4lean.InteriorModuleTensorIsometry
import BC4lean.HilbertModuleEquiv

/-! # The actual interior Hilbert-module tensor associator

Composed creation gives a balanced bilinear contraction on the completed
first tensor and the third module. Its full pairing identity proves radical
descent and an isometry on the separated second tensor. The genuine completion
extends that isometry. Its range is closed and contains every nested pure
tensor by actual pure-tensor density, proving surjectivity and a Hilbert-module
unitary. Nonunital coefficient algebras and degenerate representations are allowed.
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

/-- The constructed bilinear map from the completed first tensor and G. -/
def bilinear : InteriorModuleTensor (E := E) φ →ₗ[ℂ] G →ₗ[ℂ]
    RightTensor (E := E) φ ψ where
  toFun u := (creation φ ψ u).toCLM.toLinearMap
  map_add' u v := by
    ext z
    change creation φ ψ (u + v) z = creation φ ψ u z + creation φ ψ v z
    rw [map_add]
    rfl
  map_smul' a u := by
    ext z
    change creation φ ψ (a • u) z = a • creation φ ψ u z
    rw [map_smul]
    rfl

theorem bilinear_balance (c : C) (u : InteriorModuleTensor (E := E) φ) (z : G) :
    bilinear φ ψ (MulOpposite.op c • u) z = bilinear φ ψ u (ψ c z) := by
  change creation φ ψ (MulOpposite.op c • u) z = creation φ ψ u (ψ c z)
  rw [creation_balance]
  rfl

/-- Descent through the actual C-balancing quotient of the second tensor. -/
def balancedMap :
    BalancedModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ →ₗ[ℂ]
      RightTensor (E := E) φ ψ :=
  moduleTensorLift ψ (bilinear φ ψ) (bilinear_balance φ ψ)

@[simp] theorem balancedMap_mk (u : InteriorModuleTensor (E := E) φ) (z : G) :
    balancedMap φ ψ (moduleTensorMk ψ u z) = creation φ ψ u z := rfl

/-- Preservation of the whole coefficient-valued pairing on finite tensors. -/
theorem balancedMap_inner
    (u v : BalancedModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ) :
    ⟪balancedMap φ ψ u, balancedMap φ ψ v⟫_(Dᵐᵒᵖ) = moduleTensorInner ψ u v := by
  induction u using moduleTensor_induction ψ with
  | h0 =>
    simp only [map_zero, LinearMap.zero_apply]
    exact CStarModule.inner_zero_left
      (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ)
  | hθ u z =>
    induction v using moduleTensor_induction ψ with
    | h0 =>
      simp only [map_zero]
      exact CStarModule.inner_zero_right
        (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ)
    | hθ v w =>
      rw [balancedMap_mk, balancedMap_mk, moduleTensorInner_mk_mk]
      exact creation_pair φ ψ u v z w
    | hadd v w hv hw =>
      simp only [map_add]
      rw [CStarModule.inner_add_right
        (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ), hv, hw]
  | hadd u v hu hv =>
    simp only [map_add, LinearMap.add_apply]
    rw [CStarModule.inner_add_left
      (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ), hu, hv]

theorem balancedMap_null
    {u : BalancedModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ}
    (hu : u ∈ moduleTensorNull ψ) : balancedMap φ ψ u = 0 := by
  apply (CStarModule.inner_self
    (A := Dᵐᵒᵖ) (E := RightTensor (E := E) φ ψ)).mp
  rw [balancedMap_inner]
  exact (mem_moduleTensorNull_iff ψ u).mp hu

/-- The actual linear map on the separated second tensor. -/
def preMap : PreHilbertModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ →ₗ[ℂ]
    RightTensor (E := E) φ ψ :=
  (moduleTensorNull ψ).liftQ (balancedMap φ ψ) (fun _ hu => balancedMap_null φ ψ hu)

@[simp] theorem preMap_mk (u : InteriorModuleTensor (E := E) φ) (z : G) :
    preMap φ ψ (preModuleTensorMk ψ u z) = creation φ ψ u z := rfl

theorem preMap_inner
    (u v : PreHilbertModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ) :
    ⟪preMap φ ψ u, preMap φ ψ v⟫_(Dᵐᵒᵖ) = ⟪u, v⟫_(Dᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact balancedMap_inner φ ψ u v

theorem preMap_norm
    (u : PreHilbertModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ) :
    ‖preMap φ ψ u‖ = ‖u‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Dᵐᵒᵖ), preMap_inner,
    ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Dᵐᵒᵖ)]

def preIsometry :
    PreHilbertModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ →ₗᵢ[ℂ]
      RightTensor (E := E) φ ψ where
  toLinearMap := preMap φ ψ
  norm_map' := preMap_norm φ ψ

/-- Extension into the already complete right-parenthesized tensor. -/
def completionMap : LeftTensor (E := E) φ ψ →L[ℂ] RightTensor (E := E) φ ψ :=
  (preIsometry φ ψ).toContinuousLinearMap.fromCompletion

@[simp] theorem completionMap_coe
    (u : PreHilbertModuleTensor (E := InteriorModuleTensor (E := E) φ) ψ) :
    completionMap φ ψ (u : LeftTensor φ ψ) = preMap φ ψ u :=
  ContinuousLinearMap.fromCompletion_apply_coe (preIsometry φ ψ).toContinuousLinearMap u

@[simp] theorem completionMap_mk (u : InteriorModuleTensor (E := E) φ) (z : G) :
    completionMap φ ψ (interiorModuleTensorMk ψ u z) = creation φ ψ u z :=
  completionMap_coe φ ψ (preModuleTensorMk ψ u z)

/-- The constructed associator has the canonical formula on all triple pure tensors. -/
@[simp] theorem completionMap_triple (x : E) (y : F) (z : G) :
    completionMap φ ψ (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z) =
      interiorModuleTensorMk (rightRepresentation φ ψ) x (interiorModuleTensorMk ψ y z) := by
  rw [completionMap_mk, creation_mk]
  rfl

theorem completionMap_norm (u : LeftTensor (E := E) φ ψ) :
    ‖completionMap φ ψ u‖ = ‖u‖ := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (completionMap φ ψ).continuous) continuous_norm
  | ih u => rw [completionMap_coe, Completion.norm_coe, preMap_norm]

def completionIsometry : LeftTensor (E := E) φ ψ →ₗᵢ[ℂ] RightTensor (E := E) φ ψ where
  toLinearMap := (completionMap φ ψ).toLinearMap
  norm_map' := completionMap_norm φ ψ

theorem completionMap_inner (u v : LeftTensor (E := E) φ ψ) :
    ⟪completionMap φ ψ u, completionMap φ ψ v⟫_(Dᵐᵒᵖ) = ⟪u, v⟫_(Dᵐᵒᵖ) := by
  induction u, v using Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (CStarModule.continuous_inner.comp
        (((completionMap φ ψ).continuous.comp continuous_fst).prodMk
          ((completionMap φ ψ).continuous.comp continuous_snd)))
      CStarModule.continuous_inner
  | ih u v =>
    rw [completionMap_coe, completionMap_coe, completionInner_coe]
    exact preMap_inner φ ψ u v

/-- Completeness closes the isometric range; both pure-tensor densities prove it is all. -/
theorem completionMap_surjective :
    Function.Surjective (completionMap (E := E) φ ψ) := by
  let R := (completionMap (E := E) φ ψ).range
  have hR : IsClosed (R : Set (RightTensor (E := E) φ ψ)) :=
    (completionIsometry (E := E) φ ψ).isometry.isUniformInducing.isComplete_range.isClosed
  have hθ (x : E) (w : InteriorModuleTensor (E := F) ψ) :
      interiorModuleTensorMk (rightRepresentation φ ψ) x w ∈ R := by
    induction w using Completion.induction_on with
    | hp =>
      exact hR.preimage (moduleCreationMap (rightRepresentation φ ψ) x).toCLM.continuous
    | ih w =>
      induction w using preModuleTensor_induction ψ with
      | h0 =>
        simpa only [Completion.coe_zero, map_zero] using R.zero_mem
      | hθ y z =>
        exact ⟨interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z,
          completionMap_triple φ ψ x y z⟩
      | hadd v w hv hw =>
        simpa only [Completion.coe_add, map_add] using R.add_mem hv hw
  have hspan : (Submodule.span ℂ
      (Set.range fun p : E × InteriorModuleTensor (E := F) ψ =>
        interiorModuleTensorMk (rightRepresentation φ ψ) p.1 p.2)) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, w⟩, rfl⟩
    exact hθ x w
  intro u
  exact (closure_minimal hspan hR) (interiorModuleTensor_span_dense
    (E := E) (rightRepresentation φ ψ) u)

/-- The genuine coefficient-inner-product-preserving interior-tensor unitary. -/
def hilbertEquiv : HilbertModuleEquiv D (LeftTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (completionIsometry φ ψ)
    (completionMap_surjective φ ψ)
  inner_map := completionMap_inner φ ψ

@[simp] theorem hilbertEquiv_triple (x : E) (y : F) (z : G) :
    hilbertEquiv φ ψ (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z) =
      interiorModuleTensorMk (rightRepresentation φ ψ) x (interiorModuleTensorMk ψ y z) :=
  completionMap_triple φ ψ x y z

@[simp] theorem hilbertEquiv_symm_triple (x : E) (y : F) (z : G) :
    (hilbertEquiv φ ψ).symm
      (interiorModuleTensorMk (rightRepresentation φ ψ) x (interiorModuleTensorMk ψ y z)) =
    interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z := by
  rw [← hilbertEquiv_triple, HilbertModuleEquiv.symm_apply_apply]

/-- The outer pure tensor, as a bounded complex-linear function of its first vector. -/
def leftPureCLM (z : G) : InteriorModuleTensor (E := E) φ →L[ℂ] LeftTensor (E := E) φ ψ :=
  ({ toFun := fun u => interiorModuleTensorMk ψ u z
     map_add' := fun u v => by simp
     map_smul' := fun a u => by simp } :
      InteriorModuleTensor (E := E) φ →ₗ[ℂ] LeftTensor (E := E) φ ψ).mkContinuous ‖z‖
    (fun u => by
      change ‖interiorModuleTensorMk ψ u z‖ ≤ ‖z‖ * ‖u‖
      simpa only [mul_comm] using interiorModuleTensorMk_norm_le ψ u z)

/-- Continuous linear maps on the left iterated tensor are determined by triple pure tensors. -/
theorem left_clm_ext {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f g : LeftTensor (E := E) φ ψ →L[ℂ] P}
    (h : ∀ x y z,
      f (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z) =
      g (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z)) : f = g := by
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext (φ := ψ)
  intro u z
  have hh : f.comp (leftPureCLM φ ψ z) = g.comp (leftPureCLM φ ψ z) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext (φ := φ)
    intro x y
    exact h x y z
  exact DFunLike.congr_fun hh u

/-- Continuous linear maps on the right iterated tensor are determined by triple pure tensors. -/
theorem right_clm_ext {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f g : RightTensor (E := E) φ ψ →L[ℂ] P}
    (h : ∀ x y z,
      f (interiorModuleTensorMk (rightRepresentation φ ψ) x (interiorModuleTensorMk ψ y z)) =
      g (interiorModuleTensorMk (rightRepresentation φ ψ) x (interiorModuleTensorMk ψ y z))) :
    f = g := by
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    (φ := rightRepresentation φ ψ)
  intro x w
  have hh : f.comp (moduleCreationMap (rightRepresentation φ ψ) x).toCLM =
      g.comp (moduleCreationMap (rightRepresentation φ ψ) x).toCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext (φ := ψ)
    intro y z
    exact h x y z
  exact DFunLike.congr_fun hh w

end BC4lean.KKTheory.InteriorModuleTensorAssociator

