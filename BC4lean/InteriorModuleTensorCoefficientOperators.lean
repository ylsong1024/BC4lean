import BC4lean.InteriorModuleTensorCoefficientEquiv
import BC4lean.ModuleCreationMap

/-! # Actual operator and rectangular creation naturality of coefficient change -/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorCoefficientEquiv
open scoped InnerProductSpace

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

theorem reverseHilbertEquiv_operator (T : AdjointableMap B E E)
    (z : TensorChangedFactors eB eC φ) :
    reverseHilbertEquiv eB eC φ
      (interiorModuleTensorOperator (leftAction eB eC φ) (coefficientChangedOperator eB T) z) =
      coefficientChangedOperator eC (interiorModuleTensorOperator φ T)
        (reverseHilbertEquiv eB eC φ z) := by
  let U := (reverseHilbertEquiv (E := E) eB eC φ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : U.comp (interiorModuleTensorOperator (leftAction eB eC φ)
      (coefficientChangedOperator eB T)).toCLM =
      (coefficientChangedOperator eC (interiorModuleTensorOperator φ T)).toCLM.comp U := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change reverseHilbertEquiv eB eC φ
        (interiorModuleTensorOperator (leftAction eB eC φ)
          (coefficientChangedOperator eB T)
          (interiorModuleTensorMk (leftAction eB eC φ) x y)) =
      coefficientChangedOperator eC (interiorModuleTensorOperator φ T)
        (reverseHilbertEquiv eB eC φ
          (interiorModuleTensorMk (leftAction eB eC φ) x y))
    rw [interiorModuleTensorOperator_mk, reverseHilbertEquiv_mk,
      reverseHilbertEquiv_mk]
    change coefficientChangedLinearIsometry eC
        (interiorModuleTensorMk φ (T (coefficientChangedToOriginal eB x))
          (coefficientChangedToOriginal eC y)) =
      coefficientChangedLinearIsometry eC
        (interiorModuleTensorOperator φ T
          (interiorModuleTensorMk φ (coefficientChangedToOriginal eB x)
            (coefficientChangedToOriginal eC y)))
    rw [interiorModuleTensorOperator_mk]
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_operator (T : AdjointableMap B E E) (z : ChangedTensor eC φ) :
    hilbertEquiv eB eC φ
      (coefficientChangedOperator eC (interiorModuleTensorOperator φ T) z) =
      interiorModuleTensorOperator (leftAction eB eC φ) (coefficientChangedOperator eB T)
        (hilbertEquiv eB eC φ z) := by
  apply (reverseHilbertEquiv eB eC φ).injective
  change reverseHilbertEquiv eB eC φ ((reverseHilbertEquiv eB eC φ).symm _) =
    reverseHilbertEquiv eB eC φ
      (interiorModuleTensorOperator (leftAction eB eC φ) (coefficientChangedOperator eB T)
        ((reverseHilbertEquiv eB eC φ).symm z))
  rw [HilbertModuleEquiv.apply_symm_apply, reverseHilbertEquiv_operator,
    HilbertModuleEquiv.apply_symm_apply]

theorem transport_firstOperator (T : AdjointableMap B E E) :
    (hilbertEquiv (E := E) eB eC φ).transport
      (coefficientChangedOperator eC (interiorModuleTensorOperator φ T)) =
      interiorModuleTensorOperator (leftAction eB eC φ) (coefficientChangedOperator eB T) := by
  apply AdjointableMap.ext
  intro z
  rw [HilbertModuleEquiv.transport_apply, hilbertEquiv_operator,
    HilbertModuleEquiv.apply_symm_apply]

theorem creation (x : E) (y : CoefficientChangedModule eC F) :
    hilbertEquiv eB eC φ (coefficientChangedOperator eC (moduleCreationMap φ x) y) =
      moduleCreationMap (leftAction eB eC φ) (coefficientChangedLinearIsometry eB x) y :=
  hilbertEquiv_mk eB eC φ x (y : F)

theorem creation_operator (x : E) :
    (hilbertEquiv (E := E) eB eC φ).toAdjointable.comp
      (coefficientChangedOperator eC (moduleCreationMap φ x)) =
      moduleCreationMap (leftAction eB eC φ) (coefficientChangedLinearIsometry eB x) := by
  apply AdjointableMap.ext
  intro y
  exact creation eB eC φ x y

theorem creation_adjoint (x : E) (z : ChangedTensor eC φ) :
    coefficientChangedOperator eC (moduleCreationMap φ x).adjoint z =
      (moduleCreationMap (leftAction eB eC φ) (coefficientChangedLinearIsometry eB x)).adjoint
        (hilbertEquiv eB eC φ z) := by
  let V := (coefficientChangedLinearIsometry (M := InteriorModuleTensor (E := E) φ) eC).toContinuousLinearEquiv.toContinuousLinearMap
  let U := (hilbertEquiv (E := E) eB eC φ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : (coefficientChangedOperator eC (moduleCreationMap φ x).adjoint).toCLM.comp V =
      (moduleCreationMap (leftAction eB eC φ) (coefficientChangedLinearIsometry eB x)).adjoint.toCLM.comp
        (U.comp V) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro y v
    change coefficientChangedOperator eC (moduleCreationMap φ x).adjoint
        (coefficientChangedLinearIsometry eC (interiorModuleTensorMk φ y v)) =
      (moduleCreationMap (leftAction eB eC φ) (coefficientChangedLinearIsometry eB x)).adjoint
        (hilbertEquiv eB eC φ
          (coefficientChangedLinearIsometry eC (interiorModuleTensorMk φ y v)))
    rw [hilbertEquiv_mk]
    change coefficientChangedLinearIsometry eC
        ((moduleCreationMap φ x).adjoint
          (preModuleTensorMk φ y v :
            UniformSpace.Completion (PreHilbertModuleTensor (E := E) φ))) =
      (moduleCreationMap (leftAction eB eC φ) (coefficientChangedLinearIsometry eB x)).adjoint
        (preModuleTensorMk (leftAction eB eC φ)
          (coefficientChangedLinearIsometry eB y) (coefficientChangedLinearIsometry eC v) :
          UniformSpace.Completion (PreHilbertModuleTensor
            (E := CoefficientChangedModule eB E) (leftAction eB eC φ)))
    rw [moduleCreationMap_adjoint_mk, moduleCreationMap_adjoint_mk]
    change coefficientChangedLinearIsometry eC
        (φ (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) v) =
      coefficientChangedLinearIsometry eC
        (φ (eB.symm (eB (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)))) v)
    rw [eB.symm_apply_apply]
  exact DFunLike.congr_fun h (z : InteriorModuleTensor (E := E) φ)

theorem creation_adjoint_operator (x : E) :
    coefficientChangedOperator eC (moduleCreationMap φ x).adjoint =
      (moduleCreationMap (leftAction eB eC φ) (coefficientChangedLinearIsometry eB x)).adjoint.comp
        (hilbertEquiv (E := E) eB eC φ).toAdjointable := by
  apply AdjointableMap.ext
  intro z
  exact creation_adjoint eB eC φ x z

theorem hilbertEquiv_representation {A : Type*} [NonUnitalCStarAlgebra A]
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) (z : ChangedTensor eC φ) :
    hilbertEquiv eB eC φ
      (coefficientChangedOperator eC (interiorModuleTensorOperator φ (ρ a)) z) =
      interiorModuleTensorOperator (leftAction eB eC φ) (coefficientChangedOperator eB (ρ a))
        (hilbertEquiv eB eC φ z) := hilbertEquiv_operator eB eC φ (ρ a) z

end BC4lean.KKTheory.InteriorModuleTensorCoefficientEquiv
