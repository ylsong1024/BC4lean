import BC4lean.GradedMatrixMoritaTensorDirectSum
import BC4lean.GradedMatrixMoritaCycle
import BC4lean.GradedKasparovDirectSum

/-! # Exact cycle intertwinings of the tensor/direct-sum unitary

The same coefficient-Hilbert unitary intertwines the actual semilinear
grading, diagonal group action, representation and first lifted operator.
Both source and coefficient algebra gradings are retained.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaTensorDirectSum
open scoped InnerProductSpace

variable {B C E G F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace G] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance sourceSumCompleteCycle : CompleteSpace (HilbertModuleSum B E G) := hilbertModuleSum_complete
local instance targetSumCompleteCycle : CompleteSpace
    (HilbertModuleSum C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := G) φ)) :=
  hilbertModuleSum_complete

theorem hilbertEquiv_operator (S : AdjointableMap B E E) (T : AdjointableMap B G G)
    (u : SourceTensor (E := E) (G := G) φ) :
    hilbertEquiv φ (interiorModuleTensorOperator φ (sumMap S T) u) =
      sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ T) (hilbertEquiv φ u) := by
  let L := (hilbertEquiv (E := E) (G := G) φ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (interiorModuleTensorOperator φ (sumMap S T)).toCLM =
      (sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ T)).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv (E := E) (G := G) φ
        (interiorModuleTensorOperator φ (sumMap S T) (interiorModuleTensorMk φ x y)) =
      sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ T)
        (hilbertEquiv (E := E) (G := G) φ (interiorModuleTensorMk φ x y))
    simp only [interiorModuleTensorOperator_mk,
      hilbertEquiv_mk, sumMap_apply, sumMk_fst, sumMk_snd]
  exact DFunLike.congr_fun h u

variable {δB : CStarGrading B} {δC : CStarGrading C}

theorem hilbertEquiv_grading (J : GradedHilbertModule δB E) (L : GradedHilbertModule δB G)
    (K : GradedHilbertModule δC F) (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (u : SourceTensor (E := E) (G := G) φ) :
    hilbertEquiv φ (((J.sum L).interiorTensor K hφ).grading u) =
      ((J.interiorTensor K hφ).sum (L.interiorTensor K hφ)).grading (hilbertEquiv φ u) := by
  let W := (hilbertEquiv (E := E) (G := G) φ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp ((J.sum L).interiorTensor K hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap =
      ((J.interiorTensor K hφ).sum (L.interiorTensor K hφ)).grading.toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv (E := E) (G := G) φ
        (((J.sum L).interiorTensor K hφ).grading (interiorModuleTensorMk φ x y)) =
      ((J.interiorTensor K hφ).sum (L.interiorTensor K hφ)).grading
        (hilbertEquiv (E := E) (G := G) φ (interiorModuleTensorMk φ x y))
    simp only [GradedHilbertModule.interiorTensor_grading_mk,
      hilbertEquiv_mk, GradedHilbertModule.sum_grading_apply, sumMk_fst, sumMk_snd]
  exact DFunLike.congr_fun h u

variable {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B} {η : CStarAlgebraAction Γ C}

theorem hilbertEquiv_action (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β G)
    (W : EquivariantHilbertModule η F) (hφ : ModuleTensorRepresentationEquivariant φ β W)
    (g : Γ) (u : SourceTensor (E := E) (G := G) φ) :
    hilbertEquiv φ (((U.sum V).interiorTensor W hφ).action g u) =
      ((U.interiorTensor W hφ).sum (V.interiorTensor W hφ)).action g (hilbertEquiv φ u) := by
  let L := (hilbertEquiv (E := E) (G := G) φ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (((U.sum V).interiorTensor W hφ).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      (((U.interiorTensor W hφ).sum (V.interiorTensor W hφ)).action g).toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv (E := E) (G := G) φ
        (((U.sum V).interiorTensor W hφ).action g (interiorModuleTensorMk φ x y)) =
      ((U.interiorTensor W hφ).sum (V.interiorTensor W hφ)).action g
        (hilbertEquiv (E := E) (G := G) φ (interiorModuleTensorMk φ x y))
    simp only [EquivariantHilbertModule.interiorTensor_action_mk,
      hilbertEquiv_mk, EquivariantHilbertModule.sum_action_apply, sumMk_fst, sumMk_snd]
  exact DFunLike.congr_fun h u

theorem hilbertEquiv_representation {A : Type*} [NonUnitalCStarAlgebra A]
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (σ : A →⋆ₙₐ[ℂ] AdjointableMap B G G)
    (a : A) (u : SourceTensor (E := E) (G := G) φ) :
    hilbertEquiv φ (interiorModuleTensorOperator φ (sumRepresentation ρ σ a) u) =
      sumMap (interiorModuleTensorOperator φ (ρ a)) (interiorModuleTensorOperator φ (σ a))
        (hilbertEquiv φ u) := hilbertEquiv_operator φ (ρ a) (σ a) u

variable {A : Type*} [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle α β δA δB G)
  (η : CStarAlgebraAction Γ C) (δC : CStarGrading C)
  (K : GradedHilbertModule δC F) (V : EquivariantHilbertModule η F)
  (hη : η.PreservesGrading δC) (hV : V.PreservesGrading K)
  (hφJ : ModuleTensorRepresentationGraded (δB := δB) φ K)
  (hφU : ModuleTensorRepresentationEquivariant φ β V)
  (hφcompact : ∀ b, IsModuleCompact (φ b)) (hF : IsCountablyGeneratedModule C F)

/-- The raw tensor cycle of a genuine direct sum is unitarily the genuine sum of tensor cycles. -/
def cycleIso : GradedKasparovCycleIso
    (GradedMatrixMoritaCycle.tensorWithCompactLeftAction (c.directSum d)
      η δC K V hη hV φ hφJ hφU hφcompact hF)
    ((GradedMatrixMoritaCycle.tensorWithCompactLeftAction c η δC K V hη hV φ hφJ hφU hφcompact hF).directSum
      (GradedMatrixMoritaCycle.tensorWithCompactLeftAction d η δC K V hη hV φ hφJ hφU hφcompact hF)) where
  moduleEquiv := hilbertEquiv φ
  grading_intertwine u := hilbertEquiv_grading φ c.grading d.grading K hφJ u
  action_intertwine g u := hilbertEquiv_action φ c.groupAction d.groupAction V hφU g u
  representation_intertwine a u := hilbertEquiv_representation φ c.representation d.representation a u
  operator_intertwine u := hilbertEquiv_operator φ c.operator d.operator u

end BC4lean.KKTheory.GradedMatrixMoritaTensorDirectSum
