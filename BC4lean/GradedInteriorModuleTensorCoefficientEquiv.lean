import BC4lean.InteriorModuleTensorCoefficientOperators
import BC4lean.GradedCycleCoefficientEquiv
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # Genuine semilinear grading and action naturality under coefficient change

The intermediate and final coefficient star equivalences intertwine the
actual algebra gradings and actions. The tensor unitary intertwines their
constructed module gradings and actions on the whole completed modules.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorCoefficientEquiv

variable {B B' C C' E F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (eB : B ≃⋆ₐ[ℂ] B') (eC : C ≃⋆ₐ[ℂ] C')
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

section Grading

variable {δB : CStarGrading B} {δC : CStarGrading C}
  (δB' : CStarGrading B') (δC' : CStarGrading C')
  (hB : ∀ b, eB (δB.automorphism b) = δB'.automorphism (eB b))
  (hC : ∀ c, eC (δC.automorphism c) = δC'.automorphism (eC c))
  (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
  (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)

include hB hφ in
theorem leftAction_graded : ModuleTensorRepresentationGraded (δB := δB')
    (leftAction eB eC φ) (K.coefficientChanged eC δC' hC) := by
  let _retainedOriginalPartialB : PartialOrder B := inferInstance
  let _retainedOriginalStarOrderB : StarOrderedRing B := inferInstance
  let _retainedOriginalPartialBprime : PartialOrder B' := inferInstance
  let _retainedOriginalStarOrderBprime : StarOrderedRing B' := inferInstance
  let _retainedOriginalCompleteF : CompleteSpace F := inferInstance
  intro b y
  have hb : eB.symm (δB'.automorphism b) = δB.automorphism (eB.symm b) := by
    apply eB.injective
    change eB (eB.symm (δB'.automorphism b)) =
      eB (δB.automorphism (eB.symm b))
    rw [eB.apply_symm_apply, hB, eB.apply_symm_apply]
  change K.grading (φ (eB.symm b) (y : F)) =
    φ (eB.symm (δB'.automorphism b)) (K.grading (y : F))
  rw [hb]
  exact hφ (eB.symm b) (y : F)

def tensorChangedGrading : GradedHilbertModule δC' (TensorChangedFactors (E := E) eB eC φ) :=
  (J.coefficientChanged eB δB' hB).interiorTensor (K.coefficientChanged eC δC' hC)
    (leftAction_graded eB eC φ δB' δC' hB hC K hφ)

def changedTensorGrading : GradedHilbertModule δC' (ChangedTensor (E := E) eC φ) :=
  (J.interiorTensor K hφ).coefficientChanged eC δC' hC

theorem reverseHilbertEquiv_grading (z : TensorChangedFactors (E := E) eB eC φ) :
    reverseHilbertEquiv (E := E) eB eC φ
      ((tensorChangedGrading eB eC φ δB' δC' hB hC J K hφ).grading z) =
      (changedTensorGrading eC φ δC' hC J K hφ).grading (reverseHilbertEquiv (E := E) eB eC φ z) := by
  let U := (reverseHilbertEquiv (E := E) eB eC φ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : U.comp (tensorChangedGrading eB eC φ δB' δC' hB hC J K hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap =
      (changedTensorGrading eC φ δC' hC J K hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap.comp U := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change reverseHilbertEquiv (E := E) eB eC φ
      (((J.coefficientChanged eB δB' hB).interiorTensor (K.coefficientChanged eC δC' hC) _).grading
        (interiorModuleTensorMk (leftAction eB eC φ) x y)) =
      (changedTensorGrading eC φ δC' hC J K hφ).grading
        (reverseHilbertEquiv (E := E) eB eC φ
          (interiorModuleTensorMk (leftAction eB eC φ) x y))
    rw [GradedHilbertModule.interiorTensor_grading_mk, reverseHilbertEquiv_mk]
    change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
      (interiorModuleTensorMk (E := E) (F := F) φ (J.grading (coefficientChangedToOriginal (M := E) eB x)) (K.grading (coefficientChangedToOriginal (M := F) eC y))) =
      (changedTensorGrading eC φ δC' hC J K hφ).grading
        (reverseHilbertEquiv (E := E) eB eC φ
          (interiorModuleTensorMk (leftAction eB eC φ) x y))
    rw [reverseHilbertEquiv_mk]
    change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
      (interiorModuleTensorMk (E := E) (F := F) φ (J.grading (coefficientChangedToOriginal (M := E) eB x)) (K.grading (coefficientChangedToOriginal (M := F) eC y))) =
        coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
          ((J.interiorTensor K hφ).grading (interiorModuleTensorMk (E := E) (F := F) φ (coefficientChangedToOriginal (M := E) eB x) (coefficientChangedToOriginal (M := F) eC y)))
    exact congrArg (coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC)
      (GradedHilbertModule.interiorTensor_grading_mk (φ := φ) J K hφ
        (coefficientChangedToOriginal (M := E) eB x)
        (coefficientChangedToOriginal (M := F) eC y)).symm
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_grading (z : ChangedTensor (E := E) eC φ) :
    hilbertEquiv (E := E) eB eC φ ((changedTensorGrading eC φ δC' hC J K hφ).grading z) =
      (tensorChangedGrading eB eC φ δB' δC' hB hC J K hφ).grading (hilbertEquiv (E := E) eB eC φ z) := by
  apply (reverseHilbertEquiv (E := E) eB eC φ).injective
  change reverseHilbertEquiv (E := E) eB eC φ ((reverseHilbertEquiv (E := E) eB eC φ).symm _) =
    reverseHilbertEquiv (E := E) eB eC φ
      ((tensorChangedGrading eB eC φ δB' δC' hB hC J K hφ).grading
        ((reverseHilbertEquiv (E := E) eB eC φ).symm z))
  rw [HilbertModuleEquiv.apply_symm_apply, reverseHilbertEquiv_grading,
    HilbertModuleEquiv.apply_symm_apply]

end Grading

section Action

variable {Γ : Type*} [Group Γ]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (β' : CStarAlgebraAction Γ B') (γ' : CStarAlgebraAction Γ C')
  (hB : ∀ g b, eB (β.automorphism g b) = β'.automorphism g (eB b))
  (hC : ∀ g c, eC (γ.automorphism g c) = γ'.automorphism g (eC c))
  (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule γ F)
  (hφ : ModuleTensorRepresentationEquivariant φ β V)

include hB hφ in
theorem leftAction_equivariant : ModuleTensorRepresentationEquivariant
    (leftAction eB eC φ) β' (V.coefficientChanged eC γ' hC) := by
  let _retainedOriginalPartialB : PartialOrder B := inferInstance
  let _retainedOriginalStarOrderB : StarOrderedRing B := inferInstance
  let _retainedOriginalPartialBprime : PartialOrder B' := inferInstance
  let _retainedOriginalStarOrderBprime : StarOrderedRing B' := inferInstance
  let _retainedOriginalCompleteF : CompleteSpace F := inferInstance
  intro g b y
  have hb : eB.symm (β'.automorphism g b) = β.automorphism g (eB.symm b) := by
    apply eB.injective
    change eB (eB.symm (β'.automorphism g b)) =
      eB (β.automorphism g (eB.symm b))
    rw [eB.apply_symm_apply, hB, eB.apply_symm_apply]
  change V.action g (φ (eB.symm b) (y : F)) =
    φ (eB.symm (β'.automorphism g b)) (V.action g (y : F))
  rw [hb]
  exact hφ g (eB.symm b) (y : F)

def tensorChangedAction : EquivariantHilbertModule γ' (TensorChangedFactors (E := E) eB eC φ) :=
  (U.coefficientChanged eB β' hB).interiorTensor (V.coefficientChanged eC γ' hC)
    (leftAction_equivariant eB eC φ β' γ' hB hC V hφ)

def changedTensorAction : EquivariantHilbertModule γ' (ChangedTensor (E := E) eC φ) :=
  (U.interiorTensor V hφ).coefficientChanged eC γ' hC

theorem reverseHilbertEquiv_action (g : Γ) (z : TensorChangedFactors (E := E) eB eC φ) :
    reverseHilbertEquiv (E := E) eB eC φ
      ((tensorChangedAction eB eC φ β' γ' hB hC U V hφ).action g z) =
      (changedTensorAction eC φ γ' hC U V hφ).action g (reverseHilbertEquiv (E := E) eB eC φ z) := by
  let W := (reverseHilbertEquiv (E := E) eB eC φ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp ((tensorChangedAction eB eC φ β' γ' hB hC U V hφ).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      ((changedTensorAction eC φ γ' hC U V hφ).action g).toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change reverseHilbertEquiv (E := E) eB eC φ
      (((U.coefficientChanged eB β' hB).interiorTensor (V.coefficientChanged eC γ' hC) _).action g
        (interiorModuleTensorMk (leftAction eB eC φ) x y)) =
      (changedTensorAction eC φ γ' hC U V hφ).action g
        (reverseHilbertEquiv (E := E) eB eC φ
          (interiorModuleTensorMk (leftAction eB eC φ) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk, reverseHilbertEquiv_mk]
    change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
      (interiorModuleTensorMk (E := E) (F := F) φ (U.action g (coefficientChangedToOriginal (M := E) eB x)) (V.action g (coefficientChangedToOriginal (M := F) eC y))) =
      (changedTensorAction eC φ γ' hC U V hφ).action g
        (reverseHilbertEquiv (E := E) eB eC φ
          (interiorModuleTensorMk (leftAction eB eC φ) x y))
    rw [reverseHilbertEquiv_mk]
    change coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
      (interiorModuleTensorMk (E := E) (F := F) φ (U.action g (coefficientChangedToOriginal (M := E) eB x)) (V.action g (coefficientChangedToOriginal (M := F) eC y))) =
        coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC
          ((U.interiorTensor V hφ).action g (interiorModuleTensorMk (E := E) (F := F) φ (coefficientChangedToOriginal (M := E) eB x) (coefficientChangedToOriginal (M := F) eC y)))
    exact congrArg (coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC)
      (EquivariantHilbertModule.interiorTensor_action_mk (φ := φ) U V hφ g
        (coefficientChangedToOriginal (M := E) eB x)
        (coefficientChangedToOriginal (M := F) eC y)).symm
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_action (g : Γ) (z : ChangedTensor (E := E) eC φ) :
    hilbertEquiv (E := E) eB eC φ ((changedTensorAction eC φ γ' hC U V hφ).action g z) =
      (tensorChangedAction eB eC φ β' γ' hB hC U V hφ).action g (hilbertEquiv (E := E) eB eC φ z) := by
  apply (reverseHilbertEquiv (E := E) eB eC φ).injective
  change reverseHilbertEquiv (E := E) eB eC φ ((reverseHilbertEquiv (E := E) eB eC φ).symm _) =
    reverseHilbertEquiv (E := E) eB eC φ
      ((tensorChangedAction eB eC φ β' γ' hB hC U V hφ).action g
        ((reverseHilbertEquiv (E := E) eB eC φ).symm z))
  rw [HilbertModuleEquiv.apply_symm_apply, reverseHilbertEquiv_action,
    HilbertModuleEquiv.apply_symm_apply]

end Action
end BC4lean.KKTheory.InteriorModuleTensorCoefficientEquiv
