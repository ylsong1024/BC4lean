import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.EssentialModulePositivityFibre
import BC4lean.GradedKasparovSecondTensorUnitary

/-! # Transport of a genuine product through a second-cycle isomorphism

The actual second tensor unitary intertwines all cycle data. Rectangular
connection errors are conjugated between the actual source modules, and
the original-first localized positivity is conjugated by the same unitary.
No operator on the second tensor factor is assumed to be balanced.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C E F G : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E)
  (d : GradedKasparovCycle β γ δB δC F) (d' : GradedKasparovCycle β γ δB δC G)
  (e : GradedKasparovCycleIso d d')

def gradedKasparovSecondIsoProductOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :
    AdjointableMap C (InteriorModuleTensor (E := E) d'.representation)
      (InteriorModuleTensor (E := E) d'.representation) :=
  (GradedKasparovSecondTensorUnitary.hilbertEquiv (E := E) d d' e).transport R

theorem gradedKasparovSecondIsoProduct_conditions
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : GradedKasparovTensorOperatorConditions c d R) :
    GradedKasparovTensorOperatorConditions c d'
      (gradedKasparovSecondIsoProductOperator d d' e R) :=
  transportedCycle_tensorConditions c d' (gradedKasparovTensorCycleOfConditions c d R hR)
    (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e)
    (GradedKasparovSecondTensorUnitary.hilbertEquiv_grading d d' e c)
    (GradedKasparovSecondTensorUnitary.hilbertEquiv_action d d' e c)
    (GradedKasparovSecondTensorUnitary.hilbertEquiv_representation d d' e c)

section Defects
variable (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) (S : AdjointableMap C F F) (x : E)

theorem gradedKasparovSecondIsoProduct_creation_defect_sub :
    e.moduleEquiv.transportMap (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e)
      ((moduleCreationMap d.representation x).comp S - R.comp (moduleCreationMap d.representation x)) =
      (moduleCreationMap d'.representation x).comp (e.moduleEquiv.transport S) -
        (gradedKasparovSecondIsoProductOperator d d' e R).comp (moduleCreationMap d'.representation x) := by
  have htransport (z : InteriorModuleTensor (E := E) d.representation) :
      GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e (R z) =
        gradedKasparovSecondIsoProductOperator d d' e R
          (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e z) := by
    simp only [gradedKasparovSecondIsoProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  ext y
  simp only [HilbertModuleEquiv.transportMap_apply, HilbertModuleEquiv.transport_apply,
    AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub,
    htransport, GradedKasparovSecondTensorUnitary.creation, HilbertModuleEquiv.apply_symm_apply]

theorem gradedKasparovSecondIsoProduct_creation_defect_add :
    e.moduleEquiv.transportMap (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e)
      ((moduleCreationMap d.representation x).comp S + R.comp (moduleCreationMap d.representation x)) =
      (moduleCreationMap d'.representation x).comp (e.moduleEquiv.transport S) +
        (gradedKasparovSecondIsoProductOperator d d' e R).comp (moduleCreationMap d'.representation x) := by
  have htransport (z : InteriorModuleTensor (E := E) d.representation) :
      GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e (R z) =
        gradedKasparovSecondIsoProductOperator d d' e R
          (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e z) := by
    simp only [gradedKasparovSecondIsoProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  ext y
  simp only [HilbertModuleEquiv.transportMap_apply, HilbertModuleEquiv.transport_apply,
    AdjointableMap.comp_apply, AdjointableMap.coe_add_apply, map_add,
    htransport, GradedKasparovSecondTensorUnitary.creation, HilbertModuleEquiv.apply_symm_apply]

end Defects

theorem gradedKasparovSecondIsoProduct_connection
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : GradedKasparovConnection c d R) :
    GradedKasparovConnection c d' (gradedKasparovSecondIsoProductOperator d d' e R) where
  even x hx := by
    have h := e.moduleEquiv.transportMap_isModuleCompact
      (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e) (hR.even x hx)
    simpa only [gradedKasparovSecondIsoProduct_creation_defect_sub, e.transport_operator] using h
  even_adjoint x hx := by
    have h := e.moduleEquiv.transportMap_isModuleCompact
      (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e) (hR.even_adjoint x hx)
    simpa only [gradedKasparovSecondIsoProduct_creation_defect_sub, HilbertModuleEquiv.transport_star,
      e.transport_operator, gradedKasparovSecondIsoProductOperator] using h
  odd x hx := by
    have h := e.moduleEquiv.transportMap_isModuleCompact
      (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e) (hR.odd x hx)
    simpa only [gradedKasparovSecondIsoProduct_creation_defect_add, e.transport_operator] using h
  odd_adjoint x hx := by
    have h := e.moduleEquiv.transportMap_isModuleCompact
      (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e) (hR.odd_adjoint x hx)
    simpa only [gradedKasparovSecondIsoProduct_creation_defect_add, HilbertModuleEquiv.transport_star,
      e.transport_operator, gradedKasparovSecondIsoProductOperator] using h

theorem gradedKasparovSecondIsoProduct_positivityOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (a : A) :
    (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e).transport
      (gradedKasparovProductPositivityOperator c d R a) =
      gradedKasparovProductPositivityOperator c d'
        (gradedKasparovSecondIsoProductOperator d d' e R) a := by
  simp only [gradedKasparovProductPositivityOperator, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_star,
    GradedKasparovSecondTensorUnitary.transport_representation,
    GradedKasparovSecondTensorUnitary.transport_firstOperator, gradedKasparovSecondIsoProductOperator]

theorem gradedKasparovSecondIsoProduct_isProduct
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    IsGradedKasparovProductOperator c d' (gradedKasparovSecondIsoProductOperator d d' e R) where
  cycleConditions := gradedKasparovSecondIsoProduct_conditions c d d' e hR.cycleConditions
  connection := gradedKasparovSecondIsoProduct_connection c d d' e hR.connection
  positivity a := by
    have h := (hR.positivity a).transport (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e)
    rwa [gradedKasparovSecondIsoProduct_positivityOperator] at h

def gradedKasparovSecondIsoProduct_cycleIso
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    GradedKasparovCycleIso (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions)
      (gradedKasparovTensorCycleOfConditions c d' (gradedKasparovSecondIsoProductOperator d d' e R)
        (gradedKasparovSecondIsoProduct_isProduct c d d' e hR).cycleConditions) where
  moduleEquiv := GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e
  grading_intertwine := GradedKasparovSecondTensorUnitary.hilbertEquiv_grading d d' e c
  action_intertwine := GradedKasparovSecondTensorUnitary.hilbertEquiv_action d d' e c
  representation_intertwine := GradedKasparovSecondTensorUnitary.hilbertEquiv_representation d d' e c
  operator_intertwine z := by
    change (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e) (R z) =
      (GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e).transport R
        ((GradedKasparovSecondTensorUnitary.hilbertEquiv d d' e) z)
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
