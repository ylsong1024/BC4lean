import BC4lean.GradedMatrixMoritaTensorUnitary
import BC4lean.GradedMatrixMoritaCycle
import BC4lean.GradedKasparovCycleIso

/-! # Actual first-factor transport and whole-cycle isomorphisms

The tensor unitary is constructed from x ⊗ y ↦ u(x) ⊗ y. Its balancing,
entire inner pairing, quotient descent, completion and dense pure range
are proved before it is used to transport cycle isomorphisms.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaFirstTensorUnitary
open scoped InnerProductSpace

variable {B C E G F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace G] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (u : HilbertModuleEquiv B E G)

def bilinear : E →ₗ[ℂ] F →ₗ[ℂ] InteriorModuleTensor (E := G) φ where
  toFun x := interiorModuleTensorMk φ (u x)
  map_add' x y := by ext z; simp
  map_smul' a x := by ext z; simp

theorem bilinear_balance {B C E G F : Type*}
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
    [CompleteSpace E] [CompleteSpace G] [CompleteSpace F]
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (u : HilbertModuleEquiv B E G)
    (b : B) (x : E) (y : F) :
    bilinear φ u (MulOpposite.op b • x) y = bilinear φ u x (φ b y) := by
  change interiorModuleTensorMk φ (u (MulOpposite.op b • x)) y =
    interiorModuleTensorMk φ (u x) (φ b y)
  rw [u.map_op_smul, interiorModuleTensorMk_balance]

def balancedMap : BalancedModuleTensor (E := E) φ →ₗ[ℂ] InteriorModuleTensor (E := G) φ :=
  moduleTensorLift φ (bilinear φ u) (bilinear_balance φ u)

@[simp] theorem balancedMap_mk (x : E) (y : F) :
    balancedMap φ u (moduleTensorMk φ x y) = interiorModuleTensorMk φ (u x) y := rfl

theorem balancedMap_inner (x y : BalancedModuleTensor (E := E) φ) :
    ⟪balancedMap φ u x, balancedMap φ u y⟫_(Cᵐᵒᵖ) = moduleTensorInner φ x y := by
  revert y
  refine moduleTensor_induction φ x ?_ ?_ ?_
  · intro y
    simp [CStarModule.inner_zero_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := G) φ)]
  · intro x z y
    refine moduleTensor_induction φ y ?_ ?_ ?_
    · simp [CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := G) φ)]
    · intro x' z'
      rw [balancedMap_mk, balancedMap_mk, interiorModuleTensorInner_mk_mk,
        moduleTensorInner_mk_mk]
      unfold moduleTensorPureInner
      rw [u.inner_map]
    · intro y z hy hz
      simp only [map_add, CStarModule.inner_add_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := G) φ), hy, hz]
  · intro x z hx hz y
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := G) φ), hx, hz]

def isometry : InteriorModuleTensor (E := E) φ →ₗᵢ[ℂ] InteriorModuleTensor (E := G) φ :=
  GradedMatrixMoritaCompletion.completedIsometry φ (balancedMap φ u) (balancedMap_inner φ u)

@[simp] theorem isometry_mk (x : E) (y : F) :
    isometry φ u (interiorModuleTensorMk φ x y) = interiorModuleTensorMk φ (u x) y :=
  GradedMatrixMoritaCompletion.completedIsometry_mk _ _ _ x y

theorem isometry_surjective : Function.Surjective (isometry φ u) := by
  let R := (isometry φ u).toLinearMap.range
  have hR : IsClosed (R : Set (InteriorModuleTensor (E := G) φ)) :=
    (isometry φ u).isometry.isUniformInducing.isComplete_range.isClosed
  have hspan : Submodule.span ℂ (Set.range fun p : G × F => interiorModuleTensorMk φ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    refine ⟨interiorModuleTensorMk φ (u.symm x) y, ?_⟩
    change isometry φ u (interiorModuleTensorMk φ (u.symm x) y) =
      interiorModuleTensorMk φ x y
    rw [isometry_mk, HilbertModuleEquiv.apply_symm_apply]
  intro z
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense φ z)

def hilbertEquiv : HilbertModuleEquiv C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := G) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ u) (isometry_surjective φ u)
  inner_map := GradedMatrixMoritaCompletion.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (x : E) (y : F) :
    hilbertEquiv φ u (interiorModuleTensorMk φ x y) = interiorModuleTensorMk φ (u x) y :=
  isometry_mk φ u x y

theorem hilbertEquiv_operator (S : AdjointableMap B E E) (T : AdjointableMap B G G)
    (hST : ∀ x, u (S x) = T (u x)) (z : InteriorModuleTensor (E := E) φ) :
    hilbertEquiv φ u (interiorModuleTensorOperator φ S z) =
      interiorModuleTensorOperator φ T (hilbertEquiv φ u z) := by
  let L := (hilbertEquiv φ u).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (interiorModuleTensorOperator φ S).toCLM =
      (interiorModuleTensorOperator φ T).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ u
      (interiorModuleTensorOperator φ S (interiorModuleTensorMk φ x y)) =
      interiorModuleTensorOperator φ T (hilbertEquiv φ u (interiorModuleTensorMk φ x y))
    simp only [interiorModuleTensorOperator_mk,
      hilbertEquiv_mk, hST]
  exact DFunLike.congr_fun h z

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}
  {c : GradedKasparovCycle α β δA δB E} {d : GradedKasparovCycle α β δA δB G}
  (η : CStarAlgebraAction Γ C) (δC : CStarGrading C)
  (K : GradedHilbertModule δC F) (V : EquivariantHilbertModule η F)
  (hη : η.PreservesGrading δC) (hV : V.PreservesGrading K)
  (hφJ : ModuleTensorRepresentationGraded (δB := δB) φ K)
  (hφU : ModuleTensorRepresentationEquivariant φ β V)
  (hφcompact : ∀ b, IsModuleCompact (φ b)) (hF : IsCountablyGeneratedModule C F)

def cycleIso (e : GradedKasparovCycleIso c d) : GradedKasparovCycleIso
    (GradedMatrixMoritaCycle.tensorWithCompactLeftAction c η δC K V hη hV φ hφJ hφU hφcompact hF)
    (GradedMatrixMoritaCycle.tensorWithCompactLeftAction d η δC K V hη hV φ hφJ hφU hφcompact hF) where
  moduleEquiv := hilbertEquiv φ e.moduleEquiv
  grading_intertwine z := by
    let L := (hilbertEquiv φ e.moduleEquiv).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp (c.grading.interiorTensor K hφJ).grading.toContinuousLinearEquiv.toContinuousLinearMap =
        (d.grading.interiorTensor K hφJ).grading.toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change hilbertEquiv φ e.moduleEquiv
        ((c.grading.interiorTensor K hφJ).grading (interiorModuleTensorMk φ x y)) =
        (d.grading.interiorTensor K hφJ).grading
          (hilbertEquiv φ e.moduleEquiv (interiorModuleTensorMk φ x y))
      simp only [GradedHilbertModule.interiorTensor_grading_mk,
        hilbertEquiv_mk, e.grading_intertwine]
    exact DFunLike.congr_fun h z
  action_intertwine g z := by
    let L := (hilbertEquiv φ e.moduleEquiv).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp ((c.groupAction.interiorTensor V hφU).action g).toContinuousLinearEquiv.toContinuousLinearMap =
        ((d.groupAction.interiorTensor V hφU).action g).toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change hilbertEquiv φ e.moduleEquiv
        ((c.groupAction.interiorTensor V hφU).action g (interiorModuleTensorMk φ x y)) =
        (d.groupAction.interiorTensor V hφU).action g
          (hilbertEquiv φ e.moduleEquiv (interiorModuleTensorMk φ x y))
      simp only [EquivariantHilbertModule.interiorTensor_action_mk,
        hilbertEquiv_mk, e.action_intertwine]
    exact DFunLike.congr_fun h z
  representation_intertwine a z := hilbertEquiv_operator φ e.moduleEquiv
    (c.representation a) (d.representation a) (e.representation_intertwine a) z
  operator_intertwine z := hilbertEquiv_operator φ e.moduleEquiv
    c.operator d.operator e.operator_intertwine z

end BC4lean.KKTheory.GradedMatrixMoritaFirstTensorUnitary
