import BC4lean.InteriorModuleTensorSecondDirectSumCompatibility
import BC4lean.GradedKasparovFirstSumProduct

/-! # Actual product operators distribute over the second Hilbert sum

The completed second-factor sum unitary intertwines the actual block
creation maps. Its inverse transports the sum of two genuine product
cycles; all four connection defects and the positive lifts descend.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedKasparovSecondSumProduct
open InteriorModuleTensorSecondDirectSum

variable {Γ A B C E F G : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G] [CompleteSpace G]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (c : GradedKasparovCycle α β δA δB E)
  (d : GradedKasparovCycle β γ δB δC F) (d' : GradedKasparovCycle β γ δB δC G)

local instance sourceSumComplete : CompleteSpace (HilbertModuleSum C F G) := hilbertModuleSum_complete
local instance targetSumComplete : CompleteSpace
    (HilbertModuleSum C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d'.representation)) := hilbertModuleSum_complete

def operator (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
    (R' : AdjointableMap C (InteriorModuleTensor (E := E) d'.representation)
      (InteriorModuleTensor (E := E) d'.representation)) :
    AdjointableMap C (InteriorModuleTensor (E := E) (d.directSum d').representation)
      (InteriorModuleTensor (E := E) (d.directSum d').representation) :=
  (hilbertEquiv (E := E) d.representation d'.representation).symm.transport (sumMap R R')

theorem operator_intertwine (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
    (R' : AdjointableMap C (InteriorModuleTensor (E := E) d'.representation)
      (InteriorModuleTensor (E := E) d'.representation))
    (z : InteriorModuleTensor (E := E) (d.directSum d').representation) :
    hilbertEquiv (E := E) d.representation d'.representation (operator d d' R R' z) =
      sumMap R R' (hilbertEquiv (E := E) d.representation d'.representation z) := by
  let U := hilbertEquiv (E := E) d.representation d'.representation
  change U (U.symm (sumMap R R' (U z))) = sumMap R R' (U z)
  exact U.apply_symm_apply _

section Defects
variable (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
  (R' : AdjointableMap C (InteriorModuleTensor (E := E) d'.representation)
    (InteriorModuleTensor (E := E) d'.representation))
  (S : AdjointableMap C F F) (S' : AdjointableMap C G G) (x : E)

theorem creation_defect_sub_compact
    (h : IsModuleCompact ((moduleCreationMap d.representation x).comp S -
      R.comp (moduleCreationMap d.representation x)))
    (h' : IsModuleCompact ((moduleCreationMap d'.representation x).comp S' -
      R'.comp (moduleCreationMap d'.representation x))) :
    IsModuleCompact ((moduleCreationMap (d.directSum d').representation x).comp (sumMap S S') -
      (operator d d' R R').comp (moduleCreationMap (d.directSum d').representation x)) := by
  have hout := (h.sumMap h').comp_left
    (hilbertEquiv (E := E) d.representation d'.representation).symm.toAdjointable
  let U := hilbertEquiv (E := E) d.representation d'.representation
  let θ : AdjointableMap C (HilbertModuleSum C F G)
      (SourceTensor (E := E) d.representation d'.representation) :=
    moduleCreationMap (sumRepresentation d.representation d'.representation) x
  let O : AdjointableMap C (SourceTensor (E := E) d.representation d'.representation)
      (SourceTensor (E := E) d.representation d'.representation) :=
    U.symm.transport (sumMap R R')
  have hcreation (y : HilbertModuleSum C F G) :
      U (θ y) =
        sumMk (moduleCreationMap d.representation x y.fst)
          (moduleCreationMap d'.representation x y.snd) := by
    change U (interiorModuleTensorMk (sumRepresentation d.representation d'.representation) x y) =
      sumMk (interiorModuleTensorMk d.representation x y.fst)
        (interiorModuleTensorMk d'.representation x y.snd)
    exact hilbertEquiv_mk d.representation d'.representation x y
  have hop (z : SourceTensor (E := E) d.representation d'.representation) :
      U (O z) = sumMap R R' (U z) := by
    change U (U.symm (sumMap R R' (U z))) = sumMap R R' (U z)
    exact U.apply_symm_apply _
  have hinv (z : TargetSum (E := E) d.representation d'.representation) : U (U.symm z) = z :=
    U.apply_symm_apply z
  have heq : θ.comp (sumMap S S') - O.comp θ =
      U.symm.toAdjointable.comp
        (sumMap ((moduleCreationMap d.representation x).comp S -
          R.comp (moduleCreationMap d.representation x))
          ((moduleCreationMap d'.representation x).comp S' -
            R'.comp (moduleCreationMap d'.representation x))) := by
    ext y
    apply U.injective
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply]
    change U (θ (sumMap S S' y) - O (θ y)) =
      U (U.symm (sumMap ((moduleCreationMap d.representation x).comp S -
        R.comp (moduleCreationMap d.representation x))
        ((moduleCreationMap d'.representation x).comp S' -
          R'.comp (moduleCreationMap d'.representation x)) y))
    rw [HilbertModuleEquiv.map_sub, hcreation, hop, hcreation, hinv]
    apply Prod.ext
    · simp only [WithCStarModule.sub_fst, sumMap_apply, sumMk_fst,
        AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply]
    · simp only [WithCStarModule.sub_snd, sumMap_apply, sumMk_snd,
        AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply]
  change IsModuleCompact (θ.comp (sumMap S S') - O.comp θ)
  rw [heq]
  exact hout

theorem creation_defect_add_compact
    (h : IsModuleCompact ((moduleCreationMap d.representation x).comp S +
      R.comp (moduleCreationMap d.representation x)))
    (h' : IsModuleCompact ((moduleCreationMap d'.representation x).comp S' +
      R'.comp (moduleCreationMap d'.representation x))) :
    IsModuleCompact ((moduleCreationMap (d.directSum d').representation x).comp (sumMap S S') +
      (operator d d' R R').comp (moduleCreationMap (d.directSum d').representation x)) := by
  have hout := (h.sumMap h').comp_left
    (hilbertEquiv (E := E) d.representation d'.representation).symm.toAdjointable
  let U := hilbertEquiv (E := E) d.representation d'.representation
  let θ : AdjointableMap C (HilbertModuleSum C F G)
      (SourceTensor (E := E) d.representation d'.representation) :=
    moduleCreationMap (sumRepresentation d.representation d'.representation) x
  let O : AdjointableMap C (SourceTensor (E := E) d.representation d'.representation)
      (SourceTensor (E := E) d.representation d'.representation) :=
    U.symm.transport (sumMap R R')
  have hcreation (y : HilbertModuleSum C F G) :
      U (θ y) =
        sumMk (moduleCreationMap d.representation x y.fst)
          (moduleCreationMap d'.representation x y.snd) := by
    change U (interiorModuleTensorMk (sumRepresentation d.representation d'.representation) x y) =
      sumMk (interiorModuleTensorMk d.representation x y.fst)
        (interiorModuleTensorMk d'.representation x y.snd)
    exact hilbertEquiv_mk d.representation d'.representation x y
  have hop (z : SourceTensor (E := E) d.representation d'.representation) :
      U (O z) = sumMap R R' (U z) := by
    change U (U.symm (sumMap R R' (U z))) = sumMap R R' (U z)
    exact U.apply_symm_apply _
  have hinv (z : TargetSum (E := E) d.representation d'.representation) : U (U.symm z) = z :=
    U.apply_symm_apply z
  have heq : θ.comp (sumMap S S') + O.comp θ =
      U.symm.toAdjointable.comp
        (sumMap ((moduleCreationMap d.representation x).comp S +
          R.comp (moduleCreationMap d.representation x))
          ((moduleCreationMap d'.representation x).comp S' +
            R'.comp (moduleCreationMap d'.representation x))) := by
    ext y
    apply U.injective
    simp only [AdjointableMap.coe_add_apply, AdjointableMap.comp_apply]
    change U (θ (sumMap S S' y) + O (θ y)) =
      U (U.symm (sumMap ((moduleCreationMap d.representation x).comp S +
        R.comp (moduleCreationMap d.representation x))
        ((moduleCreationMap d'.representation x).comp S' +
          R'.comp (moduleCreationMap d'.representation x)) y))
    rw [HilbertModuleEquiv.map_add, hcreation, hop, hcreation, hinv]
    apply Prod.ext
    · simp only [WithCStarModule.add_fst, sumMap_apply, sumMk_fst,
        AdjointableMap.coe_add_apply, AdjointableMap.comp_apply]
    · simp only [WithCStarModule.add_snd, sumMap_apply, sumMk_snd,
        AdjointableMap.coe_add_apply, AdjointableMap.comp_apply]
  change IsModuleCompact (θ.comp (sumMap S S') + O.comp θ)
  rw [heq]
  exact hout

end Defects

theorem connection
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    {R' : AdjointableMap C (InteriorModuleTensor (E := E) d'.representation)
      (InteriorModuleTensor (E := E) d'.representation)}
    (hR : GradedKasparovConnection c d R) (hR' : GradedKasparovConnection c d' R') :
    GradedKasparovConnection c (d.directSum d') (operator d d' R R') := by
  have hstar : star (operator d d' R R') = operator d d' (star R) (star R') := by
    change star ((hilbertEquiv (E := E) d.representation d'.representation).symm.transport
      (sumMap R R')) =
      (hilbertEquiv (E := E) d.representation d'.representation).symm.transport
        (sumMap (star R) (star R'))
    rw [← HilbertModuleEquiv.transport_star, ← sumMap_star]
  constructor
  · intro x hx
    exact creation_defect_sub_compact d d' R R' d.operator d'.operator x
      (hR.even x hx) (hR'.even x hx)
  · intro x hx
    rw [hstar]
    change IsModuleCompact ((moduleCreationMap (d.directSum d').representation x).comp
      (star (sumMap d.operator d'.operator)) - _)
    rw [← sumMap_star]
    exact creation_defect_sub_compact d d' (star R) (star R') (star d.operator) (star d'.operator) x
      (hR.even_adjoint x hx) (hR'.even_adjoint x hx)
  · intro x hx
    exact creation_defect_add_compact d d' R R' d.operator d'.operator x
      (hR.odd x hx) (hR'.odd x hx)
  · intro x hx
    rw [hstar]
    change IsModuleCompact ((moduleCreationMap (d.directSum d').representation x).comp
      (star (sumMap d.operator d'.operator)) + _)
    rw [← sumMap_star]
    exact creation_defect_add_compact d d' (star R) (star R') (star d.operator) (star d'.operator) x
      (hR.odd_adjoint x hx) (hR'.odd_adjoint x hx)

section ActualProducts
variable {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}
  {R' : AdjointableMap C (InteriorModuleTensor (E := E) d'.representation)
    (InteriorModuleTensor (E := E) d'.representation)}
  (hR : IsGradedKasparovProductOperator c d R) (hR' : IsGradedKasparovProductOperator c d' R')

include hR hR' in
theorem conditions : GradedKasparovTensorOperatorConditions c (d.directSum d') (operator d d' R R') := by
  let U := hilbertEquiv (E := E) d.representation d'.representation
  let k := (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).directSum
    (gradedKasparovTensorCycleOfConditions c d' R' hR'.cycleConditions)
  have hinv (x : TargetSum (E := E) d.representation d'.representation) : U (U.symm x) = x :=
    U.apply_symm_apply x
  apply transportedCycle_tensorConditions c (d.directSum d') k U.symm
  · intro x
    have h := hilbertEquiv_grading d.representation d'.representation
      c.grading d.grading d'.grading d.representation_graded d'.representation_graded (U.symm x)
    change U ((gradedKasparovTensorGrading c (d.directSum d')).grading (U.symm x)) =
      k.grading.grading (U (U.symm x)) at h
    have hc := congrArg (fun z : TargetSum (E := E) d.representation d'.representation =>
      k.grading.grading z) (hinv x)
    exact (congrArg (fun z : TargetSum (E := E) d.representation d'.representation =>
      U.symm z) (h.trans hc)).symm.trans (U.symm_apply_apply _)
  · intro g x
    have h := hilbertEquiv_action d.representation d'.representation
      c.groupAction d.groupAction d'.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
      (d'.groupAction.representationEquivariant_of_conjugate d'.representation_equivariant) g (U.symm x)
    change U ((gradedKasparovTensorAction c (d.directSum d')).action g (U.symm x)) =
      k.groupAction.action g (U (U.symm x)) at h
    have hc := congrArg (fun z : TargetSum (E := E) d.representation d'.representation =>
      k.groupAction.action g z) (hinv x)
    exact (congrArg (fun z : TargetSum (E := E) d.representation d'.representation =>
      U.symm z) (h.trans hc)).symm.trans (U.symm_apply_apply _)
  · intro a x
    have h := hilbertEquiv_representation d.representation d'.representation c.representation a (U.symm x)
    change U (gradedKasparovTensorRepresentation c (d.directSum d') a (U.symm x)) =
      k.representation a (U (U.symm x)) at h
    have hc := congrArg (fun z : TargetSum (E := E) d.representation d'.representation =>
      k.representation a z) (hinv x)
    exact (congrArg (fun z : TargetSum (E := E) d.representation d'.representation =>
      U.symm z) (h.trans hc)).symm.trans (U.symm_apply_apply _)

theorem positivityOperator (a : A) :
    (hilbertEquiv (E := E) d.representation d'.representation).transport
      (gradedKasparovProductPositivityOperator c (d.directSum d') (operator d d' R R') a) =
      sumMap (gradedKasparovProductPositivityOperator c d R a)
        (gradedKasparovProductPositivityOperator c d' R' a) := by
  let U := hilbertEquiv (E := E) d.representation d'.representation
  let ρ : AdjointableMap C (SourceTensor (E := E) d.representation d'.representation)
      (SourceTensor (E := E) d.representation d'.representation) :=
    interiorModuleTensorOperator (sumRepresentation d.representation d'.representation) (c.representation a)
  let T : AdjointableMap C (SourceTensor (E := E) d.representation d'.representation)
      (SourceTensor (E := E) d.representation d'.representation) :=
    interiorModuleTensorOperator (sumRepresentation d.representation d'.representation) c.operator
  let O : AdjointableMap C (SourceTensor (E := E) d.representation d'.representation)
      (SourceTensor (E := E) d.representation d'.representation) :=
    U.symm.transport (sumMap R R')
  have hρ : U.transport ρ =
      sumMap (gradedKasparovTensorRepresentation c d a) (gradedKasparovTensorRepresentation c d' a) := by
    change U.transport (interiorModuleTensorOperator
      (sumRepresentation d.representation d'.representation) (c.representation a)) = _
    exact hilbertEquiv_transport_operator d.representation d'.representation (c.representation a)
  have hT : U.transport T =
      sumMap (interiorModuleTensorOperator d.representation c.operator)
        (interiorModuleTensorOperator d'.representation c.operator) := by
    change U.transport (interiorModuleTensorOperator
      (sumRepresentation d.representation d'.representation) c.operator) = _
    exact hilbertEquiv_transport_operator d.representation d'.representation c.operator
  have hO : U.transport O = sumMap R R' := by
    change U.transport (U.symm.transport (sumMap R R')) = sumMap R R'
    exact U.transport_symm_symm _
  change U.transport (ρ * (T * O + O * T) * star ρ) = _
  rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_star, hρ, hT, hO]
  simp only [← sumMap_mul, ← sumMap_add, ← sumMap_star, gradedKasparovProductPositivityOperator]

include hR hR' in
theorem isProduct : IsGradedKasparovProductOperator c (d.directSum d') (operator d d' R R') where
  cycleConditions := conditions c d d' hR hR'
  connection := connection c d d' hR.connection hR'.connection
  positivity a := by
    let U := hilbertEquiv (E := E) d.representation d'.representation
    let P : AdjointableMap C (SourceTensor (E := E) d.representation d'.representation)
        (SourceTensor (E := E) d.representation d'.representation) :=
      gradedKasparovProductPositivityOperator c (d.directSum d') (operator d d' R R') a
    have heq : U.transport P =
        sumMap (gradedKasparovProductPositivityOperator c d R a)
          (gradedKasparovProductPositivityOperator c d' R' a) :=
      positivityOperator c d d' (R := R) (R' := R') a
    have h := ((hR.positivity a).sumMap (hR'.positivity a)).transport U.symm
    rw [← heq] at h
    change IsPositiveModuloModuleCompact P
    simpa only [HilbertModuleEquiv.transport_symm] using h

include hR hR' in
def cycleIso : GradedKasparovCycleIso
    (gradedKasparovTensorCycleOfConditions c (d.directSum d') (operator d d' R R')
      (isProduct c d d' hR hR').cycleConditions)
    ((gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).directSum
      (gradedKasparovTensorCycleOfConditions c d' R' hR'.cycleConditions)) where
  moduleEquiv := hilbertEquiv (E := E) d.representation d'.representation
  grading_intertwine := hilbertEquiv_grading d.representation d'.representation
    c.grading d.grading d'.grading d.representation_graded d'.representation_graded
  action_intertwine := hilbertEquiv_action d.representation d'.representation
    c.groupAction d.groupAction d'.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    (d'.groupAction.representationEquivariant_of_conjugate d'.representation_equivariant)
  representation_intertwine := hilbertEquiv_representation d.representation d'.representation c.representation
  operator_intertwine := operator_intertwine d d' R R'

end ActualProducts
end BC4lean.KKTheory.GradedKasparovSecondSumProduct
