import BC4lean.InteriorModuleTensorIsometry
import BC4lean.ModuleTensorOperator
import BC4lean.EquivariantHilbertModule

/-! # Genuine graded and equivariant interior tensors

The grading is `J_E ⊗ J_F` on actual elementary tensors. A graded left
representation is required so that this map respects coefficient balancing.
Likewise the group acts as `U_g ⊗ V_g`, using actual equivariance of the left
representation. The factor-isometry construction proves inner compatibility
on the actual separated quotient and its completion. General coefficient
gradings and automorphisms are retained. Discrete joint continuity follows
from the resulting genuine isometric group action.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

variable (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

/-- The exact pointwise grading condition on the left representation. -/
def ModuleTensorRepresentationGraded {δB : CStarGrading B} {δC : CStarGrading C}
    (J : GradedHilbertModule δC F) : Prop :=
  ∀ b y, J.grading (φ b y) = φ (δB.automorphism b) (J.grading y)

/-- The exact pointwise equivariance condition on the left representation. -/
def ModuleTensorRepresentationEquivariant
    (α : CStarAlgebraAction Γ B) {β : CStarAlgebraAction Γ C}
    (V : EquivariantHilbertModule β F) : Prop :=
  ∀ g b y, V.action g (φ b y) = φ (α.automorphism g b) (V.action g y)

namespace GradedHilbertModule

variable {φ} {δB : CStarGrading B} {δC : CStarGrading C}

/-- Compatible grading data on the original factors, before any quotient. -/
def interiorTensorFactor (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K) :
    ModuleTensorFactorIsometry (E := E) φ where
  coefficientB := δB.automorphism
  coefficientC := δC.automorphism
  first := J.grading
  second := K.grading
  first_smul := J.map_op_smul
  first_inner := J.inner_grading
  second_inner := K.inner_grading
  intertwines := hφ

/-- The genuine grading on the actual completed interior tensor. -/
def interiorTensor (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K) :
    GradedHilbertModule δC (InteriorModuleTensor (E := E) φ) where
  grading := (J.interiorTensorFactor K hφ).interiorIsometry
  involutive u := by
    let L := (J.interiorTensorFactor K hφ).interiorIsometry
    have hL : L.toLinearIsometry.toContinuousLinearMap.comp
        L.toLinearIsometry.toContinuousLinearMap = ContinuousLinearMap.id ℂ _ := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change (J.interiorTensorFactor K hφ).interiorIsometry
        ((J.interiorTensorFactor K hφ).interiorIsometry (interiorModuleTensorMk φ x y)) =
          interiorModuleTensorMk φ x y
      rw [ModuleTensorFactorIsometry.interiorIsometry_mk,
        ModuleTensorFactorIsometry.interiorIsometry_mk]
      change interiorModuleTensorMk φ (J.grading (J.grading x)) (K.grading (K.grading y)) = _
      rw [J.grading_sq, K.grading_sq]
    exact DFunLike.congr_fun hL u
  inner_grading := (J.interiorTensorFactor K hφ).interiorIsometry_inner

@[simp] theorem interiorTensor_grading_mk
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K) (x : E) (y : F) :
    (J.interiorTensor K hφ).grading (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk φ (J.grading x) (K.grading y) :=
  (J.interiorTensorFactor K hφ).interiorIsometry_mk x y

omit [PartialOrder B] [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace F] in
/-- For trivial coefficient gradings, the required left representation
condition is precisely that all represented operators are even. -/
theorem representationGraded_trivial_iff_even
    (K : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F) :
    ModuleTensorRepresentationGraded (δB := CStarGrading.trivial) φ K ↔
      ∀ b, K.IsEven K (φ b) := Iff.rfl

/-- An actual even first-factor operator remains even on the genuine tensor. -/
theorem IsEven.interiorModuleTensorOperator
    {J : GradedHilbertModule δB E} (K : GradedHilbertModule δC F)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    {T : AdjointableMap B E E} (hT : J.IsEven J T) :
    (J.interiorTensor K hφ).IsEven (J.interiorTensor K hφ) (KKTheory.interiorModuleTensorOperator φ T) := by
  let L := (J.interiorTensor K hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (KKTheory.interiorModuleTensorOperator φ T).toCLM =
      (KKTheory.interiorModuleTensorOperator φ T).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change (J.interiorTensor K hφ).grading
      (KKTheory.interiorModuleTensorOperator φ T (interiorModuleTensorMk φ x y)) =
        KKTheory.interiorModuleTensorOperator φ T
          ((J.interiorTensor K hφ).grading (interiorModuleTensorMk φ x y))
    rw [interiorModuleTensorOperator_mk, interiorTensor_grading_mk,
      interiorTensor_grading_mk, interiorModuleTensorOperator_mk, hT x]
  exact fun u => DFunLike.congr_fun h u

/-- An actual odd first-factor operator remains odd, including its minus
sign, on the genuine completed interior tensor. -/
theorem IsOdd.interiorModuleTensorOperator
    {J : GradedHilbertModule δB E} (K : GradedHilbertModule δC F)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    {T : AdjointableMap B E E} (hT : J.IsOdd J T) :
    (J.interiorTensor K hφ).IsOdd (J.interiorTensor K hφ) (KKTheory.interiorModuleTensorOperator φ T) := by
  let L := (J.interiorTensor K hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (KKTheory.interiorModuleTensorOperator φ T).toCLM =
      -((KKTheory.interiorModuleTensorOperator φ T).toCLM.comp L) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change (J.interiorTensor K hφ).grading
      (KKTheory.interiorModuleTensorOperator φ T (interiorModuleTensorMk φ x y)) =
        -(KKTheory.interiorModuleTensorOperator φ T
          ((J.interiorTensor K hφ).grading (interiorModuleTensorMk φ x y)))
    rw [interiorModuleTensorOperator_mk, interiorTensor_grading_mk,
      interiorTensor_grading_mk, interiorModuleTensorOperator_mk, hT x]
    simp only [map_neg, LinearMap.neg_apply]
  exact fun u => DFunLike.congr_fun h u

end GradedHilbertModule

namespace EquivariantHilbertModule

variable {φ} {α : CStarAlgebraAction Γ B} {β : CStarAlgebraAction Γ C}

/-- Compatible group data on the original factors, before any quotient. -/
def interiorTensorFactor (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule β F)
    (hφ : ModuleTensorRepresentationEquivariant φ α V) (g : Γ) :
    ModuleTensorFactorIsometry (E := E) φ where
  coefficientB := α.automorphism g
  coefficientC := β.automorphism g
  first := U.action g
  second := V.action g
  first_smul := U.map_op_smul g
  first_inner := U.inner_action g
  second_inner := V.inner_action g
  intertwines := hφ g

/-- The actual group homomorphism to completed tensor isometries. -/
def interiorTensorAction (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule β F)
    (hφ : ModuleTensorRepresentationEquivariant φ α V) :
    Γ →* (InteriorModuleTensor (E := E) φ ≃ₗᵢ[ℂ] InteriorModuleTensor (E := E) φ) where
  toFun g := (U.interiorTensorFactor V hφ g).interiorIsometry
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro u
    have hL : (U.interiorTensorFactor V hφ 1).interiorIsometry.toLinearIsometry.toContinuousLinearMap =
        ContinuousLinearMap.id ℂ _ := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change (U.interiorTensorFactor V hφ 1).interiorIsometry
        (interiorModuleTensorMk φ x y) = interiorModuleTensorMk φ x y
      rw [ModuleTensorFactorIsometry.interiorIsometry_mk]
      change interiorModuleTensorMk φ (U.action 1 x) (V.action 1 y) = _
      rw [map_one, map_one]
      rfl
    exact DFunLike.congr_fun hL u
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro u
    have hL : (U.interiorTensorFactor V hφ (g * h)).interiorIsometry.toLinearIsometry.toContinuousLinearMap =
        (U.interiorTensorFactor V hφ g).interiorIsometry.toLinearIsometry.toContinuousLinearMap.comp
          (U.interiorTensorFactor V hφ h).interiorIsometry.toLinearIsometry.toContinuousLinearMap := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change (U.interiorTensorFactor V hφ (g * h)).interiorIsometry
        (interiorModuleTensorMk φ x y) =
          (U.interiorTensorFactor V hφ g).interiorIsometry
            ((U.interiorTensorFactor V hφ h).interiorIsometry (interiorModuleTensorMk φ x y))
      rw [ModuleTensorFactorIsometry.interiorIsometry_mk,
        ModuleTensorFactorIsometry.interiorIsometry_mk,
        ModuleTensorFactorIsometry.interiorIsometry_mk]
      change interiorModuleTensorMk φ (U.action (g * h) x) (V.action (g * h) y) =
        interiorModuleTensorMk φ (U.action g (U.action h x)) (V.action g (V.action h y))
      rw [map_mul, map_mul]
      rfl
    exact DFunLike.congr_fun hL u

/-- The genuine compatible group action on the actual completed tensor. -/
def interiorTensor (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule β F)
    (hφ : ModuleTensorRepresentationEquivariant φ α V) :
    EquivariantHilbertModule β (InteriorModuleTensor (E := E) φ) where
  action := U.interiorTensorAction V hφ
  inner_action g := (U.interiorTensorFactor V hφ g).interiorIsometry_inner

@[simp] theorem interiorTensor_action_mk (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule β F)
    (hφ : ModuleTensorRepresentationEquivariant φ α V) (g : Γ) (x : E) (y : F) :
    (U.interiorTensor V hφ).action g (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk φ (U.action g x) (V.action g y) :=
  (U.interiorTensorFactor V hφ g).interiorIsometry_mk x y

omit [PartialOrder B] [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace F] in
/-- An equivariant adjointable representation supplies exactly the
pointwise intertwining needed to preserve the tensor balancing relations. -/
theorem representationEquivariant_of_conjugate
    (V : EquivariantHilbertModule β F)
    (hφ : ∀ g b, V.conjugateOperator g (φ b) = φ (α.automorphism g b)) :
    ModuleTensorRepresentationEquivariant φ α V := by
  intro g b y
  have h := congrArg (fun T : AdjointableMap C F F => T (V.action g y)) (hφ g b)
  simpa only [conjugateOperator, conjugateMap_apply, inv_apply_apply] using h

/-- The actual tensor action conjugates the induced first-factor operator
to the induced conjugated operator. -/
theorem interiorTensor_conjugateOperator
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule β F)
    (hφ : ModuleTensorRepresentationEquivariant φ α V)
    (g : Γ) (T : AdjointableMap B E E) :
    (U.interiorTensor V hφ).conjugateOperator g (KKTheory.interiorModuleTensorOperator φ T) =
      KKTheory.interiorModuleTensorOperator φ (U.conjugateOperator g T) := by
  have h : ((U.interiorTensor V hφ).conjugateOperator g (KKTheory.interiorModuleTensorOperator φ T)).toCLM =
      (KKTheory.interiorModuleTensorOperator φ (U.conjugateOperator g T)).toCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [conjugateMap_apply, interiorTensor_action_mk,
      interiorModuleTensorOperator_mk, V.apply_inv_apply]
  exact AdjointableMap.ext (fun u => DFunLike.congr_fun h u)

/-- Tensoring two grading-preserving actions gives a grading-preserving
action on the genuine interior tensor. -/
theorem interiorTensor_preservesGrading
    {δB : CStarGrading B} {δC : CStarGrading C}
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule β F)
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
    (hU : U.PreservesGrading J) (hV : V.PreservesGrading K)
    (hφ : ModuleTensorRepresentationEquivariant φ α V)
    (hφJ : ModuleTensorRepresentationGraded (δB := δB) φ K) :
    (U.interiorTensor V hφ).PreservesGrading (J.interiorTensor K hφJ) := by
  intro g u
  let L := (U.interiorTensor V hφ).action g
  let M := (J.interiorTensor K hφJ).grading
  have hLM : L.toLinearIsometry.toContinuousLinearMap.comp M.toLinearIsometry.toContinuousLinearMap =
      M.toLinearIsometry.toContinuousLinearMap.comp L.toLinearIsometry.toContinuousLinearMap := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change (U.interiorTensor V hφ).action g
      ((J.interiorTensor K hφJ).grading (interiorModuleTensorMk φ x y)) =
        (J.interiorTensor K hφJ).grading
          ((U.interiorTensor V hφ).action g (interiorModuleTensorMk φ x y))
    rw [GradedHilbertModule.interiorTensor_grading_mk, interiorTensor_action_mk,
      interiorTensor_action_mk, GradedHilbertModule.interiorTensor_grading_mk,
      hU g x, hV g y]
  exact DFunLike.congr_fun hLM u

/-- The constructed tensor action is jointly continuous for a discrete group. -/
theorem interiorTensor_continuous_action [TopologicalSpace Γ] [DiscreteTopology Γ]
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule β F)
    (hφ : ModuleTensorRepresentationEquivariant φ α V) :
    Continuous (fun p : Γ × InteriorModuleTensor (E := E) φ =>
      (U.interiorTensor V hφ).action p.1 p.2) :=
  (U.interiorTensor V hφ).continuous_action

end EquivariantHilbertModule
end BC4lean.KKTheory
