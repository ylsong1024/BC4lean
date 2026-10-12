import BC4lean.CliffordPairSecondTensor
import BC4lean.GradedEquivariantInteriorModuleTensor
import BC4lean.CliffordExternalEvenRepresentation

/-! # Whole grading and first-factor compatibility of the true second pair

The completed product-coefficient unitary intertwines the actual tensor
grading with the grading-twisted pair swap. The first-factor operator is
the diagonal pair of the actual base tensor operator.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordPairSecondTensor

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)

def baseGrading : GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
    (BaseTensor (E := E) φ) :=
  J.interiorTensor GradedHilbertModule.trivial (fun _ _ => rfl)

@[simp] theorem baseGrading_mk (x : E) (y : F) :
    (baseGrading φ J).grading (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk φ (J.grading x) y :=
  GradedHilbertModule.interiorTensor_grading_mk _ _ _ x y

def sourceGrading :
    GradedHilbertModule (cliffordCoefficientGrading (B := C)) (Source (E := E) φ) :=
  J.interiorTensor (φ := representation φ) (cliffordPairGrading (B := C) (H := F))
    (fun _ _ => rfl)

private theorem sourceGrading_mk (x : E) (y : CliffordPairModule C F) :
    (sourceGrading φ J).grading (interiorModuleTensorMk (representation φ) x y) =
      interiorModuleTensorMk (representation φ) (J.grading x) (cliffordPairGrading.grading y) :=
  GradedHilbertModule.interiorTensor_grading_mk _ _ _ x y

/-- This identity concerns the whole actual completed carrier. -/
theorem hilbertEquiv_grading (z : Source (E := E) φ) :
    hilbertEquiv φ ((sourceGrading φ J).grading z) =
      (cliffordExternalEvenGrading (baseGrading φ J)).grading (hilbertEquiv φ z) := by
  let W := (hilbertEquiv (E := E) φ).toAdjointable.toCLM
  let L := (sourceGrading φ J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (cliffordExternalEvenGrading (baseGrading φ J)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp L = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ ((sourceGrading φ J).grading
      (interiorModuleTensorMk (representation φ) x y)) =
        (cliffordExternalEvenGrading (baseGrading φ J)).grading
          (hilbertEquiv φ (interiorModuleTensorMk (representation φ) x y))
    rw [sourceGrading_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext <;> exact (baseGrading_mk φ J _ _).symm
  exact DFunLike.congr_fun h z

/-- The original actual first-factor map remains a full diagonal pair. -/
theorem hilbertEquiv_firstFactor (T : AdjointableMap B E E) (z : Source (E := E) φ) :
    hilbertEquiv φ (interiorModuleTensorOperator (representation φ) T z) =
      cliffordPairMap (interiorModuleTensorOperator φ T) (interiorModuleTensorOperator φ T)
        (hilbertEquiv φ z) := by
  let W := (hilbertEquiv (E := E) φ).toAdjointable.toCLM
  have h : W.comp (interiorModuleTensorOperator (representation φ) T).toCLM =
      (cliffordPairMap (interiorModuleTensorOperator φ T)
        (interiorModuleTensorOperator φ T)).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ
      (interiorModuleTensorOperator (representation φ) T
        (interiorModuleTensorMk (representation φ) x y)) =
      cliffordPairMap (interiorModuleTensorOperator φ T) (interiorModuleTensorOperator φ T)
        (hilbertEquiv φ (interiorModuleTensorMk (representation φ) x y))
    rw [interiorModuleTensorOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext <;> exact (interiorModuleTensorOperator_mk φ T _ _).symm
  exact DFunLike.congr_fun h z

variable {Γ : Type*} [Group Γ]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule γ F)
  (hφ : ModuleTensorRepresentationEquivariant φ β V)

omit [PartialOrder B] [StarOrderedRing B] [StarOrderedRing C] in
include hφ in
theorem representation_equivariant :
    ModuleTensorRepresentationEquivariant (representation φ) β (cliffordPairAction V) := by
  intro g b y
  apply Prod.ext <;> exact hφ g b _

/-- Both original group actions pass through the genuine completed unitary. -/
theorem hilbertEquiv_action (g : Γ) (z : Source (E := E) φ) :
    hilbertEquiv φ ((U.interiorTensor (cliffordPairAction V)
      (representation_equivariant φ V hφ)).action g z) =
    (cliffordPairAction (U.interiorTensor V hφ)).action g (hilbertEquiv φ z) := by
  let W := (hilbertEquiv (E := E) φ).toAdjointable.toCLM
  let L := (U.interiorTensor (cliffordPairAction V)
    (representation_equivariant φ V hφ)).action g
  let K := (cliffordPairAction (U.interiorTensor V hφ)).action g
  have h : W.comp L.toContinuousLinearEquiv.toContinuousLinearMap =
      K.toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ
      ((U.interiorTensor (cliffordPairAction V)
        (representation_equivariant φ V hφ)).action g
          (interiorModuleTensorMk (representation φ) x y)) =
      (cliffordPairAction (U.interiorTensor V hφ)).action g
        (hilbertEquiv φ (interiorModuleTensorMk (representation φ) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext <;> exact (EquivariantHilbertModule.interiorTensor_action_mk U V hφ g _ _).symm
  exact DFunLike.congr_fun h z

end BC4lean.KKTheory.CliffordPairSecondTensor
