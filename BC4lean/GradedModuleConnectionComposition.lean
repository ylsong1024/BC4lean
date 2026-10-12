import BC4lean.InteriorModuleTensorAssociatorCompatibility
import BC4lean.GradedConnectionDefectAlgebra

/-! # Genuine composition of graded creation connections

The two compact arbitrary-vector connection defects give a compact defect
for the composed creation map on every completed first-pair vector. The proof
uses the actual composed creation map, pure-tensor density and closedness of
the rectangular compact ideal. Applying it to adjoints preserves both original
adjoint tests. The actual tensor associator transports these defects to the
left iterated tensor. No tensor of an arbitrary compact map is declared compact.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedModuleConnectionComposition
open scoped InnerProductSpace
open InteriorModuleTensorAssociator

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

/-- The error is an actual continuous linear map into the rectangular operator space. -/
def defectMap (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (T : AdjointableMap D G G) : InteriorModuleTensor (E := E) φ →L[ℂ]
      AdjointableMap D G (RightTensor (E := E) φ ψ) :=
  (AdjointableMap.compLeftContinuousLinearMap R).comp (creation φ ψ) -
    (AdjointableMap.compRightContinuousLinearMap T).comp
      ((creation φ ψ).comp (J.interiorTensor K hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem defectMap_apply
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (T : AdjointableMap D G G) (u : InteriorModuleTensor (E := E) φ) :
    defectMap φ ψ J K hφ R T u = R.comp (creation φ ψ u) -
      (creation φ ψ ((J.interiorTensor K hφ).grading u)).comp T := rfl

/-- Prop.9(i): connections compose on the genuine completed first-pair tensor. -/
theorem creation_defect_compact
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (S : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (T : AdjointableMap D G G)
    (hR : ∀ x : E, IsModuleCompact
      (R.comp (moduleCreationMap (rightRepresentation φ ψ) x) -
        (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)).comp S))
    (hS : ∀ y : F, IsModuleCompact
      (S.comp (moduleCreationMap ψ y) - (moduleCreationMap ψ (K.grading y)).comp T))
    (u : InteriorModuleTensor (E := E) φ) :
    IsModuleCompact (R.comp (creation φ ψ u) -
      (creation φ ψ ((J.interiorTensor K hφ).grading u)).comp T) := by
  let L := defectMap φ ψ J K hφ R T
  let P := (moduleCompact D G (RightTensor (E := E) φ ψ)).comap L.toLinearMap
  have hP : IsClosed (P : Set (InteriorModuleTensor (E := E) φ)) :=
    moduleCompact_isClosed.preimage L.continuous
  have hpure (x : E) (y : F) : interiorModuleTensorMk φ x y ∈ P := by
    change IsModuleCompact (L (interiorModuleTensorMk φ x y))
    rw [defectMap_apply, creation_mk, GradedHilbertModule.interiorTensor_grading_mk, creation_mk]
    have heq : R.comp (pureCreation φ ψ x y) - (pureCreation φ ψ (J.grading x) (K.grading y)).comp T =
        (R.comp (moduleCreationMap (rightRepresentation φ ψ) x) -
          (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)).comp S).comp
            (moduleCreationMap ψ y) +
        (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)).comp
          (S.comp (moduleCreationMap ψ y) - (moduleCreationMap ψ (K.grading y)).comp T) := by
      apply AdjointableMap.ext
      intro z
      simp only [pureCreation, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, map_sub]
      abel
    rw [heq]
    exact ((hR x).comp_right (moduleCreationMap ψ y)).add
      ((hS y).comp_left (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)))
  have hspan : Submodule.span ℂ (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact hpure x y
  change u ∈ P
  exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ u)

/-- The full adjoint connection follows by the same proved composition, without
assuming any of the three operators selfadjoint. -/
theorem creation_adjoint_defect_compact
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (S : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (T : AdjointableMap D G G)
    (hR : ∀ x : E, IsModuleCompact
      ((star R).comp (moduleCreationMap (rightRepresentation φ ψ) x) -
        (moduleCreationMap (rightRepresentation φ ψ) (J.grading x)).comp (star S)))
    (hS : ∀ y : F, IsModuleCompact
      ((star S).comp (moduleCreationMap ψ y) - (moduleCreationMap ψ (K.grading y)).comp (star T)))
    (u : InteriorModuleTensor (E := E) φ) :
    IsModuleCompact ((star R).comp (creation φ ψ u) -
      (creation φ ψ ((J.interiorTensor K hφ).grading u)).comp (star T)) :=
  creation_defect_compact φ ψ J K hφ (star R) (star S) (star T) hR hS u

/-- The actual associator intertwines the creation maps for every first-pair vector. -/
theorem associator_creation (u : InteriorModuleTensor (E := E) φ) :
    (hilbertEquiv (E := E) φ ψ).toAdjointable.comp (moduleCreationMap ψ u) = creation φ ψ u := by
  apply AdjointableMap.ext
  intro z
  exact completionMap_mk φ ψ u z

theorem inverse_associator_creation (u : InteriorModuleTensor (E := E) φ) :
    (hilbertEquiv (E := E) φ ψ).symm.toAdjointable.comp (creation φ ψ u) = moduleCreationMap ψ u := by
  apply AdjointableMap.ext
  intro z
  have h := congrArg (fun Q : AdjointableMap D G (RightTensor (E := E) φ ψ) => Q z)
    (associator_creation φ ψ u)
  change (hilbertEquiv φ ψ) (moduleCreationMap ψ u z) = creation φ ψ u z at h
  change (hilbertEquiv φ ψ).symm (creation φ ψ u z) = moduleCreationMap ψ u z
  rw [← h, HilbertModuleEquiv.symm_apply_apply]

/-- Compact composition defects transport to the left iterated tensor by the
actual unitary. Its inner-product construction is independent of the operators. -/
theorem transport_creation_defect_compact
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (T : AdjointableMap D G G) (u : InteriorModuleTensor (E := E) φ)
    (hu : IsModuleCompact (R.comp (creation φ ψ u) -
      (creation φ ψ ((J.interiorTensor K hφ).grading u)).comp T)) :
    IsModuleCompact (((hilbertEquiv (E := E) φ ψ).symm.transport R).comp (moduleCreationMap ψ u) -
      (moduleCreationMap ψ ((J.interiorTensor K hφ).grading u)).comp T) := by
  have h := hu.comp_left (hilbertEquiv (E := E) φ ψ).symm.toAdjointable
  convert h using 1
  apply AdjointableMap.ext
  intro z
  have hcreate := congrArg (fun Q : AdjointableMap D G (RightTensor (E := E) φ ψ) => Q z)
    (associator_creation φ ψ u)
  have hinv := congrArg (fun Q : AdjointableMap D G (LeftTensor (E := E) φ ψ) => Q (T z))
    (inverse_associator_creation φ ψ ((J.interiorTensor K hφ).grading u))
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_symm,
    HilbertModuleEquiv.toAdjointable_apply, map_sub] at hcreate hinv ⊢
  rw [hcreate, hinv]

end BC4lean.KKTheory.GradedModuleConnectionComposition
