import BC4lean.GradedMatrixMoritaFibreTensor
import BC4lean.ModuleCreationMap

/-! # Exact whole-module intertwinings of the first-variable fibre unitary

Every identity is first proved on actual pure tensors and then on the
completed module by continuous linear-map extensionality. The fibre
identities use genuine quotient surjectivity.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaFibreTensor
open scoped InnerProductSpace

variable {B C X E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul C(X, B)ᵐᵒᵖ E]
  [CStarModule C(X, B)ᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (t : X)

set_option maxHeartbeats 600000 in
theorem evaluation_operator (T : AdjointableMap C(X, B) E E) (u : SectionsTensor (E := E) φ) :
    evaluation φ t (interiorModuleTensorOperator (GradedMatrixMoritaSectionRepresentation.leftAction φ) T u) =
      interiorModuleTensorOperator φ (hilbertModuleFibreOperator (B := B) t T) (evaluation φ t u) := by
  have h : (evaluation φ t).comp
      (interiorModuleTensorOperator (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) T).toCLM =
      (interiorModuleTensorOperator φ (hilbertModuleFibreOperator (B := B) t T)).toCLM.comp
        (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := C(X, B)) (C := C(X, C)) (E := E) (F := C(X, F))
      (φ := GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)
      (P := EvaluatedTensor (E := E) φ t)
    intro x s
    simp only [ContinuousLinearMap.comp_apply, interiorModuleTensorOperator_mk,
      evaluation_mk, hilbertModuleFibreOperator_mk]
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_operator (T : AdjointableMap C(X, B) E E)
    (z : HilbertModuleFibre C (SectionsTensor (E := E) φ) t) :
    hilbertEquiv φ t (hilbertModuleFibreOperator (B := C) t
      (interiorModuleTensorOperator (GradedMatrixMoritaSectionRepresentation.leftAction φ) T) z) =
      interiorModuleTensorOperator φ (hilbertModuleFibreOperator (B := B) t T) (hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := SectionsTensor (E := E) φ) t z
  rw [hilbertModuleFibreOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk, evaluation_operator]

theorem hilbertEquiv_representation {A : Type*} [NonUnitalCStarAlgebra A]
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) E E) (a : A)
    (z : HilbertModuleFibre C (SectionsTensor (E := E) φ) t) :
    hilbertEquiv φ t (hilbertModuleFibreOperator (B := C) t
      (interiorModuleTensorOperator (GradedMatrixMoritaSectionRepresentation.leftAction φ) (ρ a)) z) =
      interiorModuleTensorOperator φ (hilbertModuleFibreOperator (B := B) t (ρ a))
        (hilbertEquiv φ t z) := hilbertEquiv_operator φ t (ρ a) z

set_option maxHeartbeats 4800000 in
theorem evaluation_creation (x : E) (s : C(X, F)) :
    evaluation (X := X) (E := E) (F := F) φ t
      (moduleCreationMap (B := C(X, B)) (C := C(X, C)) (E := E) (F := C(X, F))
        (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x s) =
      moduleCreationMap (B := B) (C := C) (E := HilbertModuleFibre B E t) (F := F) φ
        (hilbertModuleFibreMk (B := B) (M := E) t x) (s t) := by
  change evaluation (X := X) (E := E) φ t
      (interiorModuleTensorMk (E := E)
        (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x s) =
    interiorModuleTensorMk (E := HilbertModuleFibre B E t) φ
      (hilbertModuleFibreMk (B := B) t x) (s t)
  exact evaluation_mk (X := X) (E := E) φ t x s

set_option maxHeartbeats 2400000 in
theorem evaluation_creation_adjoint (x : E) (u : SectionsTensor (X := X) (E := E) (F := F) φ) :
    (moduleCreationMap (B := C(X, B)) (C := C(X, C)) (E := E) (F := C(X, F))
      (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x).adjoint u t =
      (moduleCreationMap (B := B) (C := C) (E := HilbertModuleFibre B E t) (F := F) φ
        (hilbertModuleFibreMk (B := B) (M := E) t x)).adjoint
        (evaluation (X := X) (E := E) (F := F) φ t u) := by
  have h : (continuousSectionEvaluation (E := F) t).comp
      (moduleCreationMap (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x).adjoint.toCLM =
      (moduleCreationMap φ (hilbertModuleFibreMk (B := B) t x)).adjoint.toCLM.comp
        (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := C(X, B)) (C := C(X, C)) (E := E) (F := C(X, F))
      (φ := GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)
      (P := F)
    intro y s
    change ((moduleCreationMap (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x).adjoint
        (interiorModuleTensorMk (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) y s)) t =
      (moduleCreationMap φ (hilbertModuleFibreMk (B := B) t x)).adjoint
        (evaluation φ t (interiorModuleTensorMk
          (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) y s))
    have hleft : (moduleCreationMap (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x).adjoint
        (interiorModuleTensorMk (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) y s) =
      GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ
        (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ)) s :=
      moduleCreationMap_adjoint_mk (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x y s
    have hright : (moduleCreationMap φ (hilbertModuleFibreMk (B := B) t x)).adjoint
        (interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t y) (s t)) =
      φ (MulOpposite.unop ⟪hilbertModuleFibreMk (B := B) t x,
        hilbertModuleFibreMk (B := B) t y⟫_(Bᵐᵒᵖ)) (s t) :=
      moduleCreationMap_adjoint_mk φ (hilbertModuleFibreMk (B := B) t x)
        (hilbertModuleFibreMk (B := B) t y) (s t)
    rw [hleft, evaluation_mk, hright, hilbertModuleFibre_inner_mk, MulOpposite.unop_op]
    rfl
  exact DFunLike.congr_fun h u

variable {Γ : Type*} [Group Γ] {δB : CStarGrading B} {δC : CStarGrading C}
  {β : CStarAlgebraAction Γ B} {η : CStarAlgebraAction Γ C}

set_option maxHeartbeats 600000 in
theorem evaluation_grading (J : GradedHilbertModule δB.continuousSections E)
    (K : GradedHilbertModule δC F) (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (u : SectionsTensor (E := E) φ) :
    evaluation φ t ((J.interiorTensor K.gradedContinuousSections
      (GradedMatrixMoritaSectionRepresentation.leftAction_graded φ K hφ)).grading u) =
      ((J.gradedFibre t).interiorTensor K hφ).grading (evaluation φ t u) := by
  let JS := J.interiorTensor K.gradedContinuousSections
    (GradedMatrixMoritaSectionRepresentation.leftAction_graded φ K hφ)
  let JT := (J.gradedFibre t).interiorTensor K hφ
  have h : (evaluation φ t).comp JS.grading.toContinuousLinearEquiv.toContinuousLinearMap =
      JT.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := C(X, B)) (C := C(X, C)) (E := E) (F := C(X, F))
      (φ := GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)
      (P := EvaluatedTensor (E := E) φ t)
    intro x s
    change evaluation φ t ((J.interiorTensor K.gradedContinuousSections
        (GradedMatrixMoritaSectionRepresentation.leftAction_graded φ K hφ)).grading
        (interiorModuleTensorMk (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x s)) =
      ((J.gradedFibre t).interiorTensor K hφ).grading
        (evaluation φ t (interiorModuleTensorMk
          (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x s))
    calc
      _ = evaluation φ t (interiorModuleTensorMk
          (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) (J.grading x)
          (K.gradedContinuousSections.grading s)) :=
        congrArg (evaluation φ t) (J.interiorTensor_grading_mk K.gradedContinuousSections
          (GradedMatrixMoritaSectionRepresentation.leftAction_graded φ K hφ) x s)
      _ = interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t (J.grading x))
          (K.grading (s t)) := evaluation_mk φ t (J.grading x) (K.gradedContinuousSections.grading s)
      _ = interiorModuleTensorMk φ ((J.gradedFibre t).grading
          (hilbertModuleFibreMk (B := B) t x)) (K.grading (s t)) :=
        congrArg (fun z => interiorModuleTensorMk φ z (K.grading (s t)))
          (J.gradedFibre_grading_mk t x).symm
      _ = ((J.gradedFibre t).interiorTensor K hφ).grading
          (interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x) (s t)) :=
        ((J.gradedFibre t).interiorTensor_grading_mk K hφ
          (hilbertModuleFibreMk (B := B) t x) (s t)).symm
      _ = _ := congrArg ((J.gradedFibre t).interiorTensor K hφ).grading
        (evaluation_mk φ t x s).symm
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_grading (J : GradedHilbertModule δB.continuousSections E)
    (K : GradedHilbertModule δC F) (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (z : HilbertModuleFibre C (SectionsTensor (E := E) φ) t) :
    hilbertEquiv φ t (((J.interiorTensor K.gradedContinuousSections
      (GradedMatrixMoritaSectionRepresentation.leftAction_graded φ K hφ)).gradedFibre t).grading z) =
      ((J.gradedFibre t).interiorTensor K hφ).grading (hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := SectionsTensor (E := E) φ) t z
  rw [GradedHilbertModule.gradedFibre_grading_mk, hilbertEquiv_mk, hilbertEquiv_mk,
    evaluation_grading]

set_option maxHeartbeats 600000 in
theorem evaluation_action (U : EquivariantHilbertModule β.continuousSections E)
    (V : EquivariantHilbertModule η F) (hφ : ModuleTensorRepresentationEquivariant φ β V)
    (g : Γ) (u : SectionsTensor (E := E) φ) :
    evaluation φ t ((U.interiorTensor V.continuousSections
      (GradedMatrixMoritaSectionRepresentation.leftAction_equivariant φ V hφ)).action g u) =
      ((U.fibre t).interiorTensor V hφ).action g (evaluation φ t u) := by
  let US := U.interiorTensor V.continuousSections
    (GradedMatrixMoritaSectionRepresentation.leftAction_equivariant φ V hφ)
  let UT := (U.fibre t).interiorTensor V hφ
  have h : (evaluation φ t).comp (US.action g).toContinuousLinearEquiv.toContinuousLinearMap =
      (UT.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp (evaluation φ t) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := C(X, B)) (C := C(X, C)) (E := E) (F := C(X, F))
      (φ := GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ)
      (P := EvaluatedTensor (E := E) φ t)
    intro x s
    change evaluation φ t ((U.interiorTensor V.continuousSections
        (GradedMatrixMoritaSectionRepresentation.leftAction_equivariant φ V hφ)).action g
        (interiorModuleTensorMk (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x s)) =
      ((U.fibre t).interiorTensor V hφ).action g
        (evaluation φ t (interiorModuleTensorMk
          (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x s))
    calc
      _ = evaluation φ t (interiorModuleTensorMk
          (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) (U.action g x)
          (V.continuousSections.action g s)) :=
        congrArg (evaluation φ t) (U.interiorTensor_action_mk V.continuousSections
          (GradedMatrixMoritaSectionRepresentation.leftAction_equivariant φ V hφ) g x s)
      _ = interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t (U.action g x))
          (V.action g (s t)) := evaluation_mk φ t (U.action g x) (V.continuousSections.action g s)
      _ = interiorModuleTensorMk φ ((U.fibre t).action g
          (hilbertModuleFibreMk (B := B) t x)) (V.action g (s t)) :=
        congrArg (fun z => interiorModuleTensorMk φ z (V.action g (s t)))
          (U.fibre_action_mk t g x).symm
      _ = ((U.fibre t).interiorTensor V hφ).action g
          (interiorModuleTensorMk φ (hilbertModuleFibreMk (B := B) t x) (s t)) :=
        ((U.fibre t).interiorTensor_action_mk V hφ g
          (hilbertModuleFibreMk (B := B) t x) (s t)).symm
      _ = _ := congrArg (((U.fibre t).interiorTensor V hφ).action g)
        (evaluation_mk φ t x s).symm
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_action (U : EquivariantHilbertModule β.continuousSections E)
    (V : EquivariantHilbertModule η F) (hφ : ModuleTensorRepresentationEquivariant φ β V)
    (g : Γ) (z : HilbertModuleFibre C (SectionsTensor (E := E) φ) t) :
    hilbertEquiv φ t (((U.interiorTensor V.continuousSections
      (GradedMatrixMoritaSectionRepresentation.leftAction_equivariant φ V hφ)).fibre t).action g z) =
      ((U.fibre t).interiorTensor V hφ).action g (hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := SectionsTensor (E := E) φ) t z
  rw [EquivariantHilbertModule.fibre_action_mk, hilbertEquiv_mk, hilbertEquiv_mk, evaluation_action]

end BC4lean.KKTheory.GradedMatrixMoritaFibreTensor
