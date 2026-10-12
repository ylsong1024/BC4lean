import BC4lean.GradedRectangularConnectionTransfer
import BC4lean.GradedModuleConnectionComposition
import BC4lean.ModuleCreationLocalCompactCFC
import BC4lean.ModuleCompactLocalizedNegativePart

/-! # The genuine anticommutator connection in the triple-product argument

Compact first-pair connection errors are transferred through the third
connection by the rectangular rank-one theorem. This proves the actual
anticommutator intertwining with the second-pair anticommutator. Independently,
the composed third connection gives the first-pair zero-connection and its
positive-part residual. No associativity or technical partition is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedTripleAnticommutatorConnection
open scoped InnerProductSpace
open InteriorModuleTensorAssociator
open GradedModuleConnectionComposition
open RectangularInteriorModuleTensorOperator

variable {B C D E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  {δB : CStarGrading B} {δC : CStarGrading C}
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)
  (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
  (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)

theorem associator_tensor_creation (x : E) :
    (hilbertEquiv (E := E) φ ψ).toAdjointable.comp (tensor ψ (moduleCreationMap φ x)) =
      moduleCreationMap (rightRepresentation φ ψ) x := by
  apply AdjointableMap.toCLM_injective
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
  intro y z
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    RectangularInteriorModuleTensorOperator.tensor_mk, moduleCreationMap_apply]
  exact hilbertEquiv_triple φ ψ x y z

def pairLift (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) :
    AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ) :=
  (hilbertEquiv φ ψ).transport (interiorModuleTensorOperator ψ Q)

def firstConnectionError
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (S : AdjointableMap C F F) (x : E) : AdjointableMap C F (InteriorModuleTensor (E := E) φ) :=
  Q.comp (moduleCreationMap φ x) - (moduleCreationMap φ (J.grading x)).comp S

/-- The true total grading gives the opposite signed rectangular error. -/
theorem conjugate_firstConnectionError
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (S : AdjointableMap C F F)
    (hQodd : (J.interiorTensor K hφ).IsOdd (J.interiorTensor K hφ) Q)
    (hSodd : K.IsOdd K S) (x : E) :
    GradedRectangularConnectionTransfer.conjugate K (J.interiorTensor K hφ)
      (firstConnectionError φ J Q S x) = -firstConnectionError φ J Q S (J.grading x) := by
  apply AdjointableMap.ext
  intro y
  rw [GradedRectangularConnectionTransfer.conjugate_apply, AdjointableMap.coe_neg_apply]
  simp only [firstConnectionError, AdjointableMap.coe_sub_apply,
    AdjointableMap.comp_apply, moduleCreationMap_apply]
  change (J.interiorTensor K hφ).grading
      (Q (interiorModuleTensorMk (E := E) φ x (K.grading y)) -
        interiorModuleTensorMk (E := E) φ (J.grading x) (S (K.grading y))) =
    -(Q (interiorModuleTensorMk (E := E) φ (J.grading x) y) -
      interiorModuleTensorMk (E := E) φ (J.grading (J.grading x)) (S y))
  rw [map_sub, hQodd (interiorModuleTensorMk (E := E) φ x (K.grading y)),
    GradedHilbertModule.interiorTensor_grading_mk, K.grading_sq,
    GradedHilbertModule.interiorTensor_grading_mk, J.grading_sq,
    hSodd (K.grading y), K.grading_sq, (interiorModuleTensorMk (E := E) φ x).map_neg]
  abel

theorem pairLift_creation_error
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (S : AdjointableMap C F F) (x : E) :
    (pairLift φ ψ Q).comp (moduleCreationMap (rightRepresentation φ ψ) x) -
      (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)).comp
        (interiorModuleTensorOperator ψ S) =
    (hilbertEquiv (E := E) φ ψ).toAdjointable.comp
      (tensor ψ (firstConnectionError φ J Q S x)) := by
  have hv := associator_tensor_creation φ ψ x
  have hj := associator_tensor_creation φ ψ (J.grading x)
  rw [firstConnectionError, tensor_sub, tensor_comp, tensor_comp, tensor_endo, tensor_endo]
  apply AdjointableMap.ext
  intro y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub,
    pairLift, HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.toAdjointable_apply]
  have hx := congrArg (fun T : AdjointableMap D (InteriorModuleTensor (E := F) ψ)
    (RightTensor (E := E) φ ψ) => T y) hv
  have hJ := congrArg (fun T : AdjointableMap D (InteriorModuleTensor (E := F) ψ)
    (RightTensor (E := E) φ ψ) => T (interiorModuleTensorOperator ψ S y)) hj
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply] at hx hJ
  rw [← hx, HilbertModuleEquiv.symm_apply_apply, hJ]

/-- The first-pair third connection is derived from both signed
connections on the two original creation factors. -/
theorem composed_isSignedModuleConnection
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (T : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (U : AdjointableMap D G G)
    (hR : IsSignedModuleConnection J (rightRepresentation φ ψ) T R)
    (hT : IsSignedModuleConnection K ψ U T) :
    IsSignedModuleConnection (J.interiorTensor K hφ) ψ U ((hilbertEquiv φ ψ).symm.transport R) := by
  constructor
  · intro u
    exact transport_creation_defect_compact φ ψ J K hφ R U u
      (creation_defect_compact φ ψ J K hφ R T U hR.creation hT.creation u)
  · intro u
    rw [← HilbertModuleEquiv.transport_star]
    exact transport_creation_defect_compact φ ψ J K hφ (star R) (star U) u
      (creation_adjoint_defect_compact φ ψ J K hφ R T U
        hR.creation_adjoint hT.creation_adjoint u)

/-- The rectangular transfer is the actual compact Jacobi remainder. -/
theorem anticommutator_connection_compact
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (S : AdjointableMap C F F)
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (T : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (U : AdjointableMap D G G)
    (hQ : IsSignedModuleConnection J φ S Q)
    (hR : IsSignedModuleConnection J (rightRepresentation φ ψ) T R)
    (hT : IsSignedModuleConnection K ψ U T)
    (hQodd : (J.interiorTensor K hφ).IsOdd (J.interiorTensor K hφ) Q)
    (hSodd : K.IsOdd K S) (x : E) :
    IsModuleCompact ((pairLift φ ψ Q * R + R * pairLift φ ψ Q).comp
      (moduleCreationMap (rightRepresentation φ ψ) x) -
      (moduleCreationMap (rightRepresentation φ ψ) x).comp
        (interiorModuleTensorOperator ψ S * T + T * interiorModuleTensorOperator ψ S)) := by
  let Ω := hilbertEquiv (E := E) φ ψ
  let Rₗ := Ω.symm.transport R
  let k := fun y => firstConnectionError φ J Q S y
  have hleft := composed_isSignedModuleConnection φ ψ J K hφ R T U hR hT
  have hj := GradedRectangularConnectionTransfer.defect_compact K (J.interiorTensor K hφ)
    ψ U Rₗ T hleft hT (hQ.creation x)
  change IsModuleCompact (Rₗ.comp (tensor ψ (firstConnectionError φ J Q S x)) -
    (tensor ψ (GradedRectangularConnectionTransfer.conjugate K (J.interiorTensor K hφ)
      (firstConnectionError φ J Q S x))).comp T) at hj
  rw [conjugate_firstConnectionError φ J K hφ Q S hQodd hSodd x, tensor_neg] at hj
  have hcompact := hj.comp_left Ω.toAdjointable
  have heq : Ω.toAdjointable.comp ((Rₗ.comp (tensor ψ (k x))) -
      (-(tensor ψ (k (J.grading x)))).comp T) =
    R.comp ((pairLift φ ψ Q).comp (moduleCreationMap (rightRepresentation φ ψ) x) -
      (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)).comp (interiorModuleTensorOperator ψ S)) +
    ((pairLift φ ψ Q).comp (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)) -
      (moduleCreationMap (rightRepresentation φ ψ) x).comp (interiorModuleTensorOperator ψ S)).comp T := by
    have hx := pairLift_creation_error φ ψ J Q S x
    have hJ := pairLift_creation_error φ ψ J Q S (J.grading x)
    rw [J.grading_sq] at hJ
    rw [hx, hJ]
    apply AdjointableMap.ext
    intro y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply, Rₗ,
      HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_symm,
      HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.apply_symm_apply, map_sub, map_neg]
    abel
  rw [heq] at hcompact
  have hsum := (((hR.creation x).comp_left (pairLift φ ψ Q)).add
    ((hR.creation (J.grading x)).comp_right (interiorModuleTensorOperator ψ S))).add hcompact
  convert hsum using 1
  apply AdjointableMap.ext
  intro y
  simp only [AdjointableMap.comp_apply, AdjointableMap.mul_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, J.grading_sq, map_add, map_sub]
  abel

/-- The same composed connection gives the true first-pair zero-connection. -/
theorem anticommutator_pair_creation_compact
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (T : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (U : AdjointableMap D G G)
    (hR : IsSignedModuleConnection J (rightRepresentation φ ψ) T R)
    (hT : IsSignedModuleConnection K ψ U T)
    (hQodd : (J.interiorTensor K hφ).IsOdd (J.interiorTensor K hφ) Q)
    (u : InteriorModuleTensor (E := E) φ) :
    IsModuleCompact ((interiorModuleTensorOperator ψ Q * (hilbertEquiv φ ψ).symm.transport R +
      (hilbertEquiv φ ψ).symm.transport R * interiorModuleTensorOperator ψ Q).comp
        (moduleCreationMap ψ u)) :=
  oddTensorAnticommutator_comp_creation (J.interiorTensor K hφ) ψ U
    ((hilbertEquiv φ ψ).symm.transport R)
    (composed_isSignedModuleConnection φ ψ J K hφ R T U hR hT).creation Q hQodd u

end BC4lean.KKTheory.GradedTripleAnticommutatorConnection
