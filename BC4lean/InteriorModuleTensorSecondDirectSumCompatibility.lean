import BC4lean.InteriorModuleTensorSecondDirectSum
import BC4lean.GradedEquivariantInteriorModuleTensor
import BC4lean.ModuleCreationMap

/-! # Whole-data naturality of second-factor tensor sums

The actual completed sum unitary intertwines first-factor operators,
source representations, both semilinear tensor gradings and the group
actions. Creation and its adjoint become actual block maps. These are
operator identities on entire completed modules, with no compactness
assumptions on the individual creation maps.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorSecondDirectSum

variable {B C E F G : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C G G)

local instance secondCompatibilitySourceComplete : CompleteSpace (HilbertModuleSum C F G) :=
  hilbertModuleSum_complete
local instance secondCompatibilityTargetComplete : CompleteSpace
    (HilbertModuleSum C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) ψ)) :=
  hilbertModuleSum_complete

theorem hilbertEquiv_creation (x : E) :
    (hilbertEquiv (E := E) φ ψ).toAdjointable.comp
      (moduleCreationMap (sumRepresentation φ ψ) x) =
    sumMap (moduleCreationMap φ x) (moduleCreationMap ψ x) := by
  ext y
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    moduleCreationMap_apply, sumMap_apply]
  change hilbertEquiv φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x y) =
    sumMk (interiorModuleTensorMk φ x y.fst) (interiorModuleTensorMk ψ x y.snd)
  exact hilbertEquiv_mk φ ψ x y

theorem hilbertEquiv_creation_adjoint (x : E) :
    (moduleCreationMap (sumRepresentation φ ψ) x).adjoint.comp
      (hilbertEquiv (E := E) φ ψ).symm.toAdjointable =
    sumMap (moduleCreationMap φ x).adjoint (moduleCreationMap ψ x).adjoint := by
  have h := congrArg AdjointableMap.adjoint (hilbertEquiv_creation φ ψ x)
  simpa only [AdjointableMap.adjoint_comp, HilbertModuleEquiv.toAdjointable_adjoint,
    sumMap_adjoint] using h

theorem hilbertEquiv_operator (S : AdjointableMap B E E)
    (u : SourceTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ (interiorModuleTensorOperator (sumRepresentation φ ψ) S u) =
      sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator ψ S)
        (hilbertEquiv φ ψ u) := by
  let W := (hilbertEquiv (E := E) φ ψ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp (interiorModuleTensorOperator (sumRepresentation φ ψ) S).toCLM =
      (sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator ψ S)).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ ψ
        (interiorModuleTensorOperator (sumRepresentation φ ψ) S
          (interiorModuleTensorMk (sumRepresentation φ ψ) x y)) =
      sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator ψ S)
        (hilbertEquiv φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x y))
    rw [interiorModuleTensorOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    simp only [sumMap_apply, sumMk_fst, sumMk_snd, interiorModuleTensorOperator_mk]
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_transport_operator (S : AdjointableMap B E E) :
    (hilbertEquiv (E := E) φ ψ).transport
      (interiorModuleTensorOperator (sumRepresentation φ ψ) S) =
    sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator ψ S) := by
  ext u
  change hilbertEquiv φ ψ
    (interiorModuleTensorOperator (sumRepresentation φ ψ) S ((hilbertEquiv φ ψ).symm u)) = _
  rw [hilbertEquiv_operator, HilbertModuleEquiv.apply_symm_apply]

theorem hilbertEquiv_representation {A : Type*} [NonUnitalCStarAlgebra A]
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) (u : SourceTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ (interiorModuleTensorOperator (sumRepresentation φ ψ) (ρ a) u) =
      sumMap (interiorModuleTensorOperator φ (ρ a)) (interiorModuleTensorOperator ψ (ρ a))
        (hilbertEquiv φ ψ u) := hilbertEquiv_operator φ ψ (ρ a) u

variable {δB : CStarGrading B} {δC : CStarGrading C}

omit [PartialOrder B] [StarOrderedRing B] [CompleteSpace F] [CompleteSpace G] in
theorem sumRepresentation_graded (K : GradedHilbertModule δC F) (L : GradedHilbertModule δC G)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (hψ : ModuleTensorRepresentationGraded (δB := δB) ψ L) :
    ModuleTensorRepresentationGraded (δB := δB) (sumRepresentation φ ψ) (K.sum L) := by
  intro b y
  change (K.sum L).grading (sumMap (φ b) (ψ b) y) =
    sumMap (φ (δB.automorphism b)) (ψ (δB.automorphism b)) ((K.sum L).grading y)
  simp only [sumMap_apply, GradedHilbertModule.sum_grading_apply, sumMk_fst, sumMk_snd]
  exact Prod.ext (hφ b y.fst) (hψ b y.snd)

theorem hilbertEquiv_grading (J : GradedHilbertModule δB E)
    (K : GradedHilbertModule δC F) (L : GradedHilbertModule δC G)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (hψ : ModuleTensorRepresentationGraded (δB := δB) ψ L)
    (u : SourceTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ
        ((J.interiorTensor (K.sum L) (sumRepresentation_graded φ ψ K L hφ hψ)).grading u) =
      ((J.interiorTensor K hφ).sum (J.interiorTensor L hψ)).grading (hilbertEquiv φ ψ u) := by
  let W := (hilbertEquiv (E := E) φ ψ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp
        (J.interiorTensor (K.sum L) (sumRepresentation_graded φ ψ K L hφ hψ)).grading.toContinuousLinearEquiv.toContinuousLinearMap =
      ((J.interiorTensor K hφ).sum (J.interiorTensor L hψ)).grading.toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ ψ
        ((J.interiorTensor (K.sum L) (sumRepresentation_graded φ ψ K L hφ hψ)).grading
          (interiorModuleTensorMk (sumRepresentation φ ψ) x y)) =
      ((J.interiorTensor K hφ).sum (J.interiorTensor L hψ)).grading
        (hilbertEquiv φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x y))
    rw [GradedHilbertModule.interiorTensor_grading_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    simp only [GradedHilbertModule.sum_grading_apply, sumMk_fst, sumMk_snd,
      GradedHilbertModule.interiorTensor_grading_mk]
  exact DFunLike.congr_fun h u

variable {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

omit [PartialOrder B] [StarOrderedRing B] [CompleteSpace F] [CompleteSpace G] in
theorem sumRepresentation_equivariant (V : EquivariantHilbertModule γ F)
    (W : EquivariantHilbertModule γ G)
    (hφ : ModuleTensorRepresentationEquivariant φ β V)
    (hψ : ModuleTensorRepresentationEquivariant ψ β W) :
    ModuleTensorRepresentationEquivariant (sumRepresentation φ ψ) β (V.sum W) := by
  intro g b y
  change (V.sum W).action g (sumMap (φ b) (ψ b) y) =
    sumMap (φ (β.automorphism g b)) (ψ (β.automorphism g b)) ((V.sum W).action g y)
  simp only [sumMap_apply, EquivariantHilbertModule.sum_action_apply, sumMk_fst, sumMk_snd]
  exact Prod.ext (hφ g b y.fst) (hψ g b y.snd)

theorem hilbertEquiv_action (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule γ F) (W : EquivariantHilbertModule γ G)
    (hφ : ModuleTensorRepresentationEquivariant φ β V)
    (hψ : ModuleTensorRepresentationEquivariant ψ β W)
    (g : Γ) (u : SourceTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ
        ((U.interiorTensor (V.sum W) (sumRepresentation_equivariant φ ψ V W hφ hψ)).action g u) =
      ((U.interiorTensor V hφ).sum (U.interiorTensor W hψ)).action g (hilbertEquiv φ ψ u) := by
  let L := (hilbertEquiv (E := E) φ ψ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp
        ((U.interiorTensor (V.sum W) (sumRepresentation_equivariant φ ψ V W hφ hψ)).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      (((U.interiorTensor V hφ).sum (U.interiorTensor W hψ)).action g).toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ ψ
        ((U.interiorTensor (V.sum W) (sumRepresentation_equivariant φ ψ V W hφ hψ)).action g
          (interiorModuleTensorMk (sumRepresentation φ ψ) x y)) =
      ((U.interiorTensor V hφ).sum (U.interiorTensor W hψ)).action g
        (hilbertEquiv φ ψ (interiorModuleTensorMk (sumRepresentation φ ψ) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    simp only [EquivariantHilbertModule.sum_action_apply, sumMk_fst, sumMk_snd,
      EquivariantHilbertModule.interiorTensor_action_mk]
  exact DFunLike.congr_fun h u

end BC4lean.KKTheory.InteriorModuleTensorSecondDirectSum
