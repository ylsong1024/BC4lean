import BC4lean.GradedMatrixMoritaSecondFibreTensor
import BC4lean.GradedIntervalKasparovFibre
import BC4lean.ModuleCreationMap

/-! # Exact intertwinings for evaluation in the second tensor variable -/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaSecondFibreTensor
open scoped InnerProductSpace

variable {B C X E M : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, C)ᵐᵒᵖ M]
  [CStarModule C(X, C)ᵐᵒᵖ M] [CompleteSpace E] [CompleteSpace M]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C(X, C) M M) (t : X)

omit [T2Space X] in
theorem evaluation_operator (T : AdjointableMap B E E) (u : InteriorModuleTensor (E := E) φ) :
    evaluation φ t (interiorModuleTensorOperator φ T u) =
      interiorModuleTensorOperator (fibreRepresentation φ t) T (evaluation φ t u) := by
  have h : (evaluation φ t).comp (interiorModuleTensorOperator φ T).toCLM =
      (interiorModuleTensorOperator (fibreRepresentation φ t) T).toCLM.comp (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [ContinuousLinearMap.comp_apply, interiorModuleTensorOperator_mk, evaluation_mk]
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_operator (T : AdjointableMap B E E)
    (z : HilbertModuleFibre C (InteriorModuleTensor (E := E) φ) t) :
    hilbertEquiv φ t (hilbertModuleFibreOperator (B := C) t (interiorModuleTensorOperator φ T) z) =
      interiorModuleTensorOperator (fibreRepresentation φ t) T (hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := InteriorModuleTensor (E := E) φ) t z
  rw [hilbertModuleFibreOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk, evaluation_operator]

theorem hilbertEquiv_representation {A : Type*} [NonUnitalCStarAlgebra A]
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A)
    (z : HilbertModuleFibre C (InteriorModuleTensor (E := E) φ) t) :
    hilbertEquiv φ t (hilbertModuleFibreOperator (B := C) t (interiorModuleTensorOperator φ (ρ a)) z) =
      interiorModuleTensorOperator (fibreRepresentation φ t) (ρ a) (hilbertEquiv φ t z) :=
  hilbertEquiv_operator φ t (ρ a) z

omit [T2Space X] in
theorem evaluation_creation (x : E) (y : M) :
    evaluation φ t (moduleCreationMap φ x y) =
      moduleCreationMap (fibreRepresentation φ t) x (hilbertModuleFibreMk (B := C) t y) :=
  evaluation_mk φ t x y

omit [T2Space X] in
theorem evaluation_creation_adjoint (x : E) (u : InteriorModuleTensor (E := E) φ) :
    hilbertModuleFibreMk (B := C) t ((moduleCreationMap φ x).adjoint u) =
      (moduleCreationMap (fibreRepresentation φ t) x).adjoint (evaluation φ t u) := by
  have h : (hilbertModuleFibreMk (B := C) t).comp (moduleCreationMap φ x).adjoint.toCLM =
      (moduleCreationMap (fibreRepresentation φ t) x).adjoint.toCLM.comp (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro y z
    change hilbertModuleFibreMk (B := C) t
        ((moduleCreationMap φ x).adjoint (interiorModuleTensorMk φ y z)) =
      (moduleCreationMap (fibreRepresentation φ t) x).adjoint
        (evaluation φ t (interiorModuleTensorMk φ y z))
    calc
      _ = hilbertModuleFibreMk (B := C) t
          (φ (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) z) :=
        congrArg (hilbertModuleFibreMk (B := C) t) (moduleCreationMap_adjoint_mk φ x y z)
      _ = fibreRepresentation φ t (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ))
          (hilbertModuleFibreMk (B := C) t z) :=
        (fibreRepresentation_mk φ t (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) z).symm
      _ = (moduleCreationMap (fibreRepresentation φ t) x).adjoint
          (interiorModuleTensorMk (fibreRepresentation φ t) y
            (hilbertModuleFibreMk (B := C) t z)) :=
        (moduleCreationMap_adjoint_mk (fibreRepresentation φ t) x y
          (hilbertModuleFibreMk (B := C) t z)).symm
      _ = _ := congrArg (moduleCreationMap (fibreRepresentation φ t) x).adjoint
        (evaluation_mk φ t y z).symm
  exact DFunLike.congr_fun h u

variable {Γ : Type*} [Group Γ] {δB : CStarGrading B} {δC : CStarGrading C}
  {β : CStarAlgebraAction Γ B} {η : CStarAlgebraAction Γ C}

omit [PartialOrder B] [StarOrderedRing B] in
theorem fibreRepresentation_graded (K : GradedHilbertModule δC.continuousSections M)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K) :
    ModuleTensorRepresentationGraded (δB := δB) (fibreRepresentation φ t) (K.gradedFibre t) := by
  intro b y
  obtain ⟨z, rfl⟩ := hilbertModuleFibreMk_surjective (B := C) (M := M) t y
  rw [fibreRepresentation_mk, GradedHilbertModule.gradedFibre_grading_mk,
    GradedHilbertModule.gradedFibre_grading_mk, fibreRepresentation_mk, hφ]

omit [PartialOrder B] [StarOrderedRing B] in
theorem fibreRepresentation_equivariant (V : EquivariantHilbertModule η.continuousSections M)
    (hφ : ModuleTensorRepresentationEquivariant φ β V) :
    ModuleTensorRepresentationEquivariant (fibreRepresentation φ t) β (V.fibre t) := by
  intro g b y
  obtain ⟨z, rfl⟩ := hilbertModuleFibreMk_surjective (B := C) (M := M) t y
  rw [fibreRepresentation_mk, EquivariantHilbertModule.fibre_action_mk,
    EquivariantHilbertModule.fibre_action_mk, fibreRepresentation_mk, hφ]

theorem evaluation_grading (J : GradedHilbertModule δB E)
    (K : GradedHilbertModule δC.continuousSections M)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (u : InteriorModuleTensor (E := E) φ) :
    evaluation φ t ((J.interiorTensor K hφ).grading u) =
      (J.interiorTensor (K.gradedFibre t) (fibreRepresentation_graded φ t K hφ)).grading
        (evaluation φ t u) := by
  let JS := J.interiorTensor K hφ
  let JT := J.interiorTensor (K.gradedFibre t) (fibreRepresentation_graded φ t K hφ)
  have h : (evaluation φ t).comp JS.grading.toContinuousLinearEquiv.toContinuousLinearMap =
      JT.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change evaluation φ t ((J.interiorTensor K hφ).grading
        (interiorModuleTensorMk φ x y)) =
      (J.interiorTensor (K.gradedFibre t) (fibreRepresentation_graded φ t K hφ)).grading
        (evaluation φ t (interiorModuleTensorMk φ x y))
    calc
      _ = evaluation φ t (interiorModuleTensorMk φ (J.grading x) (K.grading y)) :=
        congrArg (evaluation φ t) (J.interiorTensor_grading_mk K hφ x y)
      _ = interiorModuleTensorMk (fibreRepresentation φ t) (J.grading x)
          (hilbertModuleFibreMk (B := C) t (K.grading y)) :=
        evaluation_mk φ t (J.grading x) (K.grading y)
      _ = interiorModuleTensorMk (fibreRepresentation φ t) (J.grading x)
          ((K.gradedFibre t).grading (hilbertModuleFibreMk (B := C) t y)) :=
        congrArg (interiorModuleTensorMk (fibreRepresentation φ t) (J.grading x))
          (K.gradedFibre_grading_mk t y).symm
      _ = (J.interiorTensor (K.gradedFibre t)
          (fibreRepresentation_graded φ t K hφ)).grading
          (interiorModuleTensorMk (fibreRepresentation φ t) x
            (hilbertModuleFibreMk (B := C) t y)) :=
        (J.interiorTensor_grading_mk (K.gradedFibre t)
          (fibreRepresentation_graded φ t K hφ) x (hilbertModuleFibreMk (B := C) t y)).symm
      _ = _ := congrArg (J.interiorTensor (K.gradedFibre t)
        (fibreRepresentation_graded φ t K hφ)).grading (evaluation_mk φ t x y).symm
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_grading (J : GradedHilbertModule δB E)
    (K : GradedHilbertModule δC.continuousSections M)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (z : HilbertModuleFibre C (InteriorModuleTensor (E := E) φ) t) :
    hilbertEquiv φ t (((J.interiorTensor K hφ).gradedFibre t).grading z) =
      (J.interiorTensor (K.gradedFibre t) (fibreRepresentation_graded φ t K hφ)).grading
        (hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := InteriorModuleTensor (E := E) φ) t z
  rw [GradedHilbertModule.gradedFibre_grading_mk, hilbertEquiv_mk, hilbertEquiv_mk,
    evaluation_grading]

theorem evaluation_action (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule η.continuousSections M)
    (hφ : ModuleTensorRepresentationEquivariant φ β V) (g : Γ)
    (u : InteriorModuleTensor (E := E) φ) :
    evaluation φ t ((U.interiorTensor V hφ).action g u) =
      (U.interiorTensor (V.fibre t) (fibreRepresentation_equivariant φ t V hφ)).action g
        (evaluation φ t u) := by
  let US := U.interiorTensor V hφ
  let UT := U.interiorTensor (V.fibre t) (fibreRepresentation_equivariant φ t V hφ)
  have h : (evaluation φ t).comp (US.action g).toContinuousLinearEquiv.toContinuousLinearMap =
      (UT.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change evaluation φ t ((U.interiorTensor V hφ).action g
        (interiorModuleTensorMk φ x y)) =
      (U.interiorTensor (V.fibre t) (fibreRepresentation_equivariant φ t V hφ)).action g
        (evaluation φ t (interiorModuleTensorMk φ x y))
    calc
      _ = evaluation φ t (interiorModuleTensorMk φ (U.action g x) (V.action g y)) :=
        congrArg (evaluation φ t) (U.interiorTensor_action_mk V hφ g x y)
      _ = interiorModuleTensorMk (fibreRepresentation φ t) (U.action g x)
          (hilbertModuleFibreMk (B := C) t (V.action g y)) :=
        evaluation_mk φ t (U.action g x) (V.action g y)
      _ = interiorModuleTensorMk (fibreRepresentation φ t) (U.action g x)
          ((V.fibre t).action g (hilbertModuleFibreMk (B := C) t y)) :=
        congrArg (interiorModuleTensorMk (fibreRepresentation φ t) (U.action g x))
          (V.fibre_action_mk t g y).symm
      _ = (U.interiorTensor (V.fibre t)
          (fibreRepresentation_equivariant φ t V hφ)).action g
          (interiorModuleTensorMk (fibreRepresentation φ t) x
            (hilbertModuleFibreMk (B := C) t y)) :=
        (U.interiorTensor_action_mk (V.fibre t)
          (fibreRepresentation_equivariant φ t V hφ) g x
          (hilbertModuleFibreMk (B := C) t y)).symm
      _ = _ := congrArg ((U.interiorTensor (V.fibre t)
        (fibreRepresentation_equivariant φ t V hφ)).action g) (evaluation_mk φ t x y).symm
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_action (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule η.continuousSections M)
    (hφ : ModuleTensorRepresentationEquivariant φ β V) (g : Γ)
    (z : HilbertModuleFibre C (InteriorModuleTensor (E := E) φ) t) :
    hilbertEquiv φ t (((U.interiorTensor V hφ).fibre t).action g z) =
      (U.interiorTensor (V.fibre t) (fibreRepresentation_equivariant φ t V hφ)).action g
        (hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := InteriorModuleTensor (E := E) φ) t z
  rw [EquivariantHilbertModule.fibre_action_mk, hilbertEquiv_mk, hilbertEquiv_mk, evaluation_action]

end BC4lean.KKTheory.GradedMatrixMoritaSecondFibreTensor
