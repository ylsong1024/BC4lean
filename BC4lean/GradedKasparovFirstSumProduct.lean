import BC4lean.GradedMatrixMoritaTensorDirectSumCycle
import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.EssentialModulePositivityFibre

/-! # Actual product operators distribute over the first Hilbert sum

The completed tensor/sum unitary transports the genuine sum of product
cycles. Each of the four connection defects is a sum of actual compact
rectangular maps. Positive lifts sum by their actual star-square forms.
-/

noncomputable section
namespace BC4lean.KKTheory

local instance completeSum {C E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [CompleteSpace E] [CompleteSpace F] : CompleteSpace (HilbertModuleSum C E F) :=
  hilbertModuleSum_complete

theorem IsPositiveModuloModuleCompact.sumMap
    {C E F : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Cᵐᵒᵖ E] [CStarModule Cᵐᵒᵖ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
    {S : AdjointableMap C E E} {T : AdjointableMap C F F}
    (hS : IsPositiveModuloModuleCompact S) (hT : IsPositiveModuloModuleCompact T) :
    IsPositiveModuloModuleCompact (sumMap S T) := by
  obtain ⟨V, hV⟩ := hS.exists_star_square
  obtain ⟨W, hW⟩ := hT.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).2
  refine ⟨BC4lean.KKTheory.sumMap V W, ?_⟩
  simpa only [← sumMap_star, ← sumMap_mul, ← sumMap_sub] using hV.sumMap hW

namespace GradedKasparovFirstSumProduct
open GradedMatrixMoritaTensorDirectSum

variable {Γ A B C E G F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (c : GradedKasparovCycle α β δA δB E) (c' : GradedKasparovCycle α β δA δB G)
  (d : GradedKasparovCycle β γ δB δC F)

def operator (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
    (R' : AdjointableMap C (InteriorModuleTensor (E := G) d.representation)
      (InteriorModuleTensor (E := G) d.representation)) :
    AdjointableMap C (InteriorModuleTensor (E := HilbertModuleSum B E G) d.representation)
      (InteriorModuleTensor (E := HilbertModuleSum B E G) d.representation) :=
  (hilbertEquiv (E := E) (G := G) d.representation).symm.transport (sumMap R R')

theorem operator_intertwine (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
    (R' : AdjointableMap C (InteriorModuleTensor (E := G) d.representation)
      (InteriorModuleTensor (E := G) d.representation))
    (z : InteriorModuleTensor (E := HilbertModuleSum B E G) d.representation) :
    hilbertEquiv (E := E) (G := G) d.representation (operator d R R' z) =
      sumMap R R' (hilbertEquiv (E := E) (G := G) d.representation z) := by
  simp only [operator, HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_symm,
    HilbertModuleEquiv.apply_symm_apply]

section Defects
variable (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
  (R' : AdjointableMap C (InteriorModuleTensor (E := G) d.representation)
    (InteriorModuleTensor (E := G) d.representation))
  (S : AdjointableMap C F F) (x : HilbertModuleSum B E G)

theorem creation_defect_sub_compact
    (h : IsModuleCompact ((moduleCreationMap d.representation x.fst).comp S -
      R.comp (moduleCreationMap d.representation x.fst)))
    (h' : IsModuleCompact ((moduleCreationMap d.representation x.snd).comp S -
      R'.comp (moduleCreationMap d.representation x.snd))) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp S -
      (operator d R R').comp (moduleCreationMap d.representation x)) := by
  have hk := ((h.comp_left (sumInl (F := InteriorModuleTensor (E := G) d.representation))).add
    (h'.comp_left (sumInr (E := InteriorModuleTensor (E := E) d.representation))))
  have hout := hk.comp_left (hilbertEquiv (E := E) (G := G) d.representation).symm.toAdjointable
  let U := hilbertEquiv (E := E) (G := G) d.representation
  have hcreation (w : F) : U (moduleCreationMap d.representation x w) =
      sumMk (moduleCreationMap d.representation x.fst w)
        (moduleCreationMap d.representation x.snd w) := by
    change U (interiorModuleTensorMk d.representation x w) =
      sumMk (interiorModuleTensorMk d.representation x.fst w)
        (interiorModuleTensorMk d.representation x.snd w)
    exact hilbertEquiv_mk d.representation x w
  have hinv (z : HilbertModuleSum C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := G) d.representation)) :
      U (U.symm.toAdjointable z) = z := by
    change U (U.symm z) = z
    exact U.apply_symm_apply z
  convert hout using 1
  ext y
  apply U.injective
  simp only [AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply,
    AdjointableMap.comp_apply]
  change U (moduleCreationMap d.representation x (S y) -
      operator d R R' (moduleCreationMap d.representation x y)) =
    U (U.symm.toAdjointable
      (sumInl (F := InteriorModuleTensor (E := G) d.representation)
        (moduleCreationMap d.representation x.fst (S y) -
          R (moduleCreationMap d.representation x.fst y)) +
        sumInr (E := InteriorModuleTensor (E := E) d.representation)
          (moduleCreationMap d.representation x.snd (S y) -
            R' (moduleCreationMap d.representation x.snd y))))
  rw [map_sub, hcreation, operator_intertwine, hcreation, hinv]
  simp only [sumMap_apply, sumInl_apply, sumInr_apply, sumMk_add]
  apply Prod.ext
  · simp only [WithCStarModule.sub_fst, sumMk_fst, add_zero]
  · simp only [WithCStarModule.sub_snd, sumMk_snd, zero_add]

set_option maxHeartbeats 400000 in
theorem creation_defect_add_compact
    (h : IsModuleCompact ((moduleCreationMap d.representation x.fst).comp S +
      R.comp (moduleCreationMap d.representation x.fst)))
    (h' : IsModuleCompact ((moduleCreationMap d.representation x.snd).comp S +
      R'.comp (moduleCreationMap d.representation x.snd))) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp S +
      (operator d R R').comp (moduleCreationMap d.representation x)) := by
  have hk := ((h.comp_left (sumInl (F := InteriorModuleTensor (E := G) d.representation))).add
    (h'.comp_left (sumInr (E := InteriorModuleTensor (E := E) d.representation))))
  have hout := hk.comp_left (hilbertEquiv (E := E) (G := G) d.representation).symm.toAdjointable
  let U := hilbertEquiv (E := E) (G := G) d.representation
  have hcreation (w : F) : U (moduleCreationMap d.representation x w) =
      sumMk (moduleCreationMap d.representation x.fst w)
        (moduleCreationMap d.representation x.snd w) := by
    change U (interiorModuleTensorMk d.representation x w) =
      sumMk (interiorModuleTensorMk d.representation x.fst w)
        (interiorModuleTensorMk d.representation x.snd w)
    exact hilbertEquiv_mk d.representation x w
  have hinv (z : HilbertModuleSum C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := G) d.representation)) :
      U (U.symm.toAdjointable z) = z := by
    change U (U.symm z) = z
    exact U.apply_symm_apply z
  convert hout using 1
  ext y
  apply U.injective
  simp only [AdjointableMap.coe_add_apply, AdjointableMap.comp_apply]
  change U (moduleCreationMap d.representation x (S y) +
      operator d R R' (moduleCreationMap d.representation x y)) =
    U (U.symm.toAdjointable
      (sumInl (F := InteriorModuleTensor (E := G) d.representation)
        (moduleCreationMap d.representation x.fst (S y) +
          R (moduleCreationMap d.representation x.fst y)) +
        sumInr (E := InteriorModuleTensor (E := E) d.representation)
          (moduleCreationMap d.representation x.snd (S y) +
            R' (moduleCreationMap d.representation x.snd y))))
  rw [map_add, hcreation, operator_intertwine, hcreation, hinv]
  simp only [sumMap_apply, sumInl_apply, sumInr_apply, sumMk_add]
  apply Prod.ext
  · simp only [sumMk_fst, add_zero]
  · simp only [sumMk_snd, zero_add]

end Defects

theorem connection
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    {R' : AdjointableMap C (InteriorModuleTensor (E := G) d.representation)
      (InteriorModuleTensor (E := G) d.representation)}
    (hR : GradedKasparovConnection c d R) (hR' : GradedKasparovConnection c' d R') :
    GradedKasparovConnection (c.directSum c') d (operator d R R') := by
  have hstar : star (operator d R R') = operator d (star R) (star R') := by
    simp only [operator, ← HilbertModuleEquiv.transport_star, ← sumMap_star]
  constructor
  · intro x hx
    have hx0 := congrArg (fun z : HilbertModuleSum B E G => z.fst) hx
    change c.grading.grading x.fst = x.fst at hx0
    have hx1 := congrArg (fun z : HilbertModuleSum B E G => z.snd) hx
    change c'.grading.grading x.snd = x.snd at hx1
    exact creation_defect_sub_compact d R R' d.operator x (hR.even _ hx0) (hR'.even _ hx1)
  · intro x hx
    have hx0 := congrArg (fun z : HilbertModuleSum B E G => z.fst) hx
    change c.grading.grading x.fst = x.fst at hx0
    have hx1 := congrArg (fun z : HilbertModuleSum B E G => z.snd) hx
    change c'.grading.grading x.snd = x.snd at hx1
    rw [hstar]
    exact creation_defect_sub_compact d (star R) (star R') (star d.operator) x
      (hR.even_adjoint _ hx0) (hR'.even_adjoint _ hx1)
  · intro x hx
    have hx0 := congrArg (fun z : HilbertModuleSum B E G => z.fst) hx
    change c.grading.grading x.fst = -x.fst at hx0
    have hx1 := congrArg (fun z : HilbertModuleSum B E G => z.snd) hx
    change c'.grading.grading x.snd = -x.snd at hx1
    exact creation_defect_add_compact d R R' d.operator x (hR.odd _ hx0) (hR'.odd _ hx1)
  · intro x hx
    have hx0 := congrArg (fun z : HilbertModuleSum B E G => z.fst) hx
    change c.grading.grading x.fst = -x.fst at hx0
    have hx1 := congrArg (fun z : HilbertModuleSum B E G => z.snd) hx
    change c'.grading.grading x.snd = -x.snd at hx1
    rw [hstar]
    exact creation_defect_add_compact d (star R) (star R') (star d.operator) x
      (hR.odd_adjoint _ hx0) (hR'.odd_adjoint _ hx1)

section ActualProducts
variable {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}
  {R' : AdjointableMap C (InteriorModuleTensor (E := G) d.representation)
    (InteriorModuleTensor (E := G) d.representation)}
  (hR : IsGradedKasparovProductOperator c d R) (hR' : IsGradedKasparovProductOperator c' d R')

include hR hR' in
theorem conditions : GradedKasparovTensorOperatorConditions (c.directSum c') d (operator d R R') := by
  let U := hilbertEquiv (E := E) (G := G) d.representation
  let k := (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).directSum
    (gradedKasparovTensorCycleOfConditions c' d R' hR'.cycleConditions)
  apply transportedCycle_tensorConditions (c.directSum c') d k U.symm
  · intro x
    apply U.injective
    rw [HilbertModuleEquiv.apply_symm_apply]
    change (((c.grading.interiorTensor d.grading d.representation_graded).sum
      (c'.grading.interiorTensor d.grading d.representation_graded)).grading) x = U ((((c.grading.sum c'.grading).interiorTensor d.grading d.representation_graded).grading) (U.symm x))
    have ht := hilbertEquiv_grading d.representation c.grading c'.grading d.grading
      d.representation_graded (U.symm x)
    change U ((((c.grading.sum c'.grading).interiorTensor d.grading d.representation_graded).grading) (U.symm x)) = (((c.grading.interiorTensor d.grading d.representation_graded).sum
      (c'.grading.interiorTensor d.grading d.representation_graded)).grading) (U (U.symm x)) at ht
    rw [HilbertModuleEquiv.apply_symm_apply] at ht
    exact ht.symm
  · intro g x
    apply U.injective
    rw [HilbertModuleEquiv.apply_symm_apply]
    change (((c.groupAction.interiorTensor d.groupAction (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).sum
      (c'.groupAction.interiorTensor d.groupAction (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant))).action g) x = U ((((c.groupAction.sum c'.groupAction).interiorTensor d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).action g) (U.symm x))
    have ht := hilbertEquiv_action d.representation c.groupAction c'.groupAction d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant) g (U.symm x)
    change U ((((c.groupAction.sum c'.groupAction).interiorTensor d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).action g) (U.symm x)) = (((c.groupAction.interiorTensor d.groupAction (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).sum
      (c'.groupAction.interiorTensor d.groupAction (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant))).action g) (U (U.symm x)) at ht
    rw [HilbertModuleEquiv.apply_symm_apply] at ht
    exact ht.symm
  · intro a x
    apply U.injective
    rw [HilbertModuleEquiv.apply_symm_apply]
    change (sumMap (interiorModuleTensorOperator d.representation (c.representation a))
      (interiorModuleTensorOperator d.representation (c'.representation a))) x = U ((interiorModuleTensorOperator d.representation
      (sumRepresentation c.representation c'.representation a)) (U.symm x))
    have ht := hilbertEquiv_representation d.representation c.representation c'.representation a (U.symm x)
    change U ((interiorModuleTensorOperator d.representation
      (sumRepresentation c.representation c'.representation a)) (U.symm x)) = (sumMap (interiorModuleTensorOperator d.representation (c.representation a))
      (interiorModuleTensorOperator d.representation (c'.representation a))) (U (U.symm x)) at ht
    rw [HilbertModuleEquiv.apply_symm_apply] at ht
    exact ht.symm

theorem positivityOperator (a : A) :
    (hilbertEquiv (E := E) (G := G) d.representation).transport
      (gradedKasparovProductPositivityOperator (c.directSum c') d (operator d R R') a) =
      sumMap (gradedKasparovProductPositivityOperator c d R a)
        (gradedKasparovProductPositivityOperator c' d R' a) := by
  have hρ : (hilbertEquiv (E := E) (G := G) d.representation).transport
      (gradedKasparovTensorRepresentation (c.directSum c') d a) =
      sumMap (gradedKasparovTensorRepresentation c d a) (gradedKasparovTensorRepresentation c' d a) := by
    ext y
    change (hilbertEquiv (E := E) (G := G) d.representation)
      (interiorModuleTensorOperator d.representation
        (sumRepresentation c.representation c'.representation a)
        ((hilbertEquiv (E := E) (G := G) d.representation).symm y)) =
      sumMap (interiorModuleTensorOperator d.representation (c.representation a))
        (interiorModuleTensorOperator d.representation (c'.representation a)) y
    rw [hilbertEquiv_representation, HilbertModuleEquiv.apply_symm_apply]
  have hT : (hilbertEquiv (E := E) (G := G) d.representation).transport
      (interiorModuleTensorOperator d.representation (c.directSum c').operator) =
      sumMap (interiorModuleTensorOperator d.representation c.operator)
        (interiorModuleTensorOperator d.representation c'.operator) := by
    ext y
    change (hilbertEquiv (E := E) (G := G) d.representation)
      (interiorModuleTensorOperator d.representation (sumMap c.operator c'.operator)
        ((hilbertEquiv (E := E) (G := G) d.representation).symm y)) =
      sumMap (interiorModuleTensorOperator d.representation c.operator)
        (interiorModuleTensorOperator d.representation c'.operator) y
    rw [hilbertEquiv_operator, HilbertModuleEquiv.apply_symm_apply]
  simp only [gradedKasparovProductPositivityOperator, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_star, hρ, hT,
    operator, HilbertModuleEquiv.transport_symm_symm, ← sumMap_mul, ← sumMap_add, ← sumMap_star]

include hR hR' in
theorem isProduct : IsGradedKasparovProductOperator (c.directSum c') d (operator d R R') where
  cycleConditions := conditions c c' d hR hR'
  connection := connection c c' d hR.connection hR'.connection
  positivity a := by
    have h := ((hR.positivity a).sumMap (hR'.positivity a)).transport
      (hilbertEquiv (E := E) (G := G) d.representation).symm
    rw [← positivityOperator c c' d (R := R) (R' := R'), HilbertModuleEquiv.transport_symm] at h
    exact h

include hR hR' in
def cycleIso : GradedKasparovCycleIso
    (gradedKasparovTensorCycleOfConditions (c.directSum c') d (operator d R R')
      (isProduct c c' d hR hR').cycleConditions)
    ((gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).directSum
      (gradedKasparovTensorCycleOfConditions c' d R' hR'.cycleConditions)) where
  moduleEquiv := hilbertEquiv (E := E) (G := G) d.representation
  grading_intertwine := hilbertEquiv_grading d.representation c.grading c'.grading d.grading d.representation_graded
  action_intertwine := hilbertEquiv_action d.representation c.groupAction c'.groupAction d.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
  representation_intertwine := hilbertEquiv_representation d.representation c.representation c'.representation
  operator_intertwine := operator_intertwine d R R'

end ActualProducts
end GradedKasparovFirstSumProduct
end BC4lean.KKTheory
