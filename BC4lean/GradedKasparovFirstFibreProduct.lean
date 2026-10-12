import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.EssentialModulePositivityFibre
import BC4lean.GradedMatrixMoritaFibreCreationCompatibility
import BC4lean.GradedKasparovIntervalSectionsCycle

/-! # Genuine products descend through the first correspondence fibre

The fixed second cycle is lifted to the genuine continuous-section cycle.
Actual homogeneous projections lift every homogeneous first fibre vector.
All four connection errors descend through rectangular fibre maps and the
two constructed evaluation unitaries. The same tensor unitary transports
the genuine cycle and original-first localized positive lift.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B C X E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul C(X, B)ᵐᵒᵖ E]
  [CStarModule C(X, B)ᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

theorem GradedHilbertModule.gradedFibre_even_lift
    (J : GradedHilbertModule δB.continuousSections E) (t : X)
    (x : HilbertModuleFibre B E t) (hx : (J.gradedFibre t).grading x = x) :
    ∃ y : E, J.grading y = y ∧ hilbertModuleFibreMk (B := B) t y = x := by
  obtain ⟨z, hz⟩ := hilbertModuleFibreMk_surjective (B := B) (M := E) t x
  refine ⟨J.evenPart z, J.grading_evenPart z, ?_⟩
  have hJ : hilbertModuleFibreMk (B := B) t (J.grading z) = x := by
    rw [← GradedHilbertModule.gradedFibre_grading_mk, hz, hx]
  simp only [GradedHilbertModule.evenPart, map_smul, map_add, hz, hJ]
  module

theorem GradedHilbertModule.gradedFibre_odd_lift
    (J : GradedHilbertModule δB.continuousSections E) (t : X)
    (x : HilbertModuleFibre B E t) (hx : (J.gradedFibre t).grading x = -x) :
    ∃ y : E, J.grading y = -y ∧ hilbertModuleFibreMk (B := B) t y = x := by
  obtain ⟨z, hz⟩ := hilbertModuleFibreMk_surjective (B := B) (M := E) t x
  refine ⟨J.oddPart z, J.grading_oddPart z, ?_⟩
  have hJ : hilbertModuleFibreMk (B := B) t (J.grading z) = -x := by
    rw [← GradedHilbertModule.gradedFibre_grading_mk, hz, hx]
  simp only [GradedHilbertModule.oddPart, map_smul, map_sub, hz, hJ]
  module

variable (c : GradedKasparovCycle α (β.continuousSections (X := X)) δA δB.continuousSections E)
  (d : GradedKasparovCycle β γ δB δC F) (t : X)

def gradedKasparovFirstFibreTensorEquiv : HilbertModuleEquiv C
    (HilbertModuleFibre C (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation) t)
    (InteriorModuleTensor (E := HilbertModuleFibre B E t) d.representation) :=
  GradedMatrixMoritaFibreTensor.hilbertEquiv d.representation t

def gradedKasparovFirstFibreProductOperator
    (R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)) :
    AdjointableMap C (InteriorModuleTensor (E := HilbertModuleFibre B E t) d.representation)
      (InteriorModuleTensor (E := HilbertModuleFibre B E t) d.representation) :=
  (gradedKasparovFirstFibreTensorEquiv (E := E) d t).transport (hilbertModuleFibreOperator t R)

theorem gradedKasparovFirstFibreTensorEquiv_operator (T : AdjointableMap C(X, B) E E) :
    (gradedKasparovFirstFibreTensorEquiv (E := E) d t).transport
      (hilbertModuleFibreOperator t (interiorModuleTensorOperator (d.continuousSections (X := X)).representation T)) =
      interiorModuleTensorOperator d.representation (hilbertModuleFibreOperator (B := B) t T) := by
  ext y
  rw [HilbertModuleEquiv.transport_apply]
  rw [show (gradedKasparovFirstFibreTensorEquiv (E := E) d t)
      (hilbertModuleFibreOperator t
        (interiorModuleTensorOperator (d.continuousSections (X := X)).representation T)
          ((gradedKasparovFirstFibreTensorEquiv (E := E) d t).symm y)) =
      interiorModuleTensorOperator d.representation (hilbertModuleFibreOperator (B := B) t T)
        ((gradedKasparovFirstFibreTensorEquiv (E := E) d t)
          ((gradedKasparovFirstFibreTensorEquiv (E := E) d t).symm y)) from
    GradedMatrixMoritaFibreTensor.hilbertEquiv_operator d.representation t T _]
  rw [HilbertModuleEquiv.apply_symm_apply]

theorem gradedKasparovFirstFibreProduct_conditions
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)}
    (hR : GradedKasparovTensorOperatorConditions c (d.continuousSections (X := X)) R) :
    GradedKasparovTensorOperatorConditions (c.fibre t) d
      (gradedKasparovFirstFibreProductOperator (E := E) d t R) := by
  let k := (gradedKasparovTensorCycleOfConditions c (d.continuousSections (X := X)) R hR).fibre t
  apply transportedCycle_tensorConditions (c.fibre t) d k
    (gradedKasparovFirstFibreTensorEquiv (E := E) d t)
  · exact GradedMatrixMoritaFibreTensor.hilbertEquiv_grading d.representation t
      c.grading d.grading d.representation_graded
  · exact GradedMatrixMoritaFibreTensor.hilbertEquiv_action d.representation t
      c.groupAction d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
  · exact GradedMatrixMoritaFibreTensor.hilbertEquiv_representation d.representation t c.representation

section Defects
variable (R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)
    (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation))
  (S : AdjointableMap C(X, C) C(X, F) C(X, F)) (S₀ : AdjointableMap C F F)
  (hS : ∀ z, continuousSectionHilbertModuleFibreEquiv (B := C) t
      (hilbertModuleFibreOperator t S z) =
        S₀ (continuousSectionHilbertModuleFibreEquiv (B := C) t z)) (x : E)

include hS in
theorem gradedKasparovFirstFibre_creation_defect_sub :
    (continuousSectionHilbertModuleFibreEquiv (B := C) (E := F) t).transportMap
      (gradedKasparovFirstFibreTensorEquiv (E := E) d t)
      (hilbertModuleFibreRectangularMap t
        ((moduleCreationMap (d.continuousSections (X := X)).representation x).comp S -
          R.comp (moduleCreationMap (d.continuousSections (X := X)).representation x))) =
      (moduleCreationMap d.representation (hilbertModuleFibreMk (B := B) t x)).comp S₀ -
        (gradedKasparovFirstFibreProductOperator (E := E) d t R).comp
          (moduleCreationMap d.representation (hilbertModuleFibreMk (B := B) t x)) := by
  have htransport (z : HilbertModuleFibre C
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation) t) :
      gradedKasparovFirstFibreTensorEquiv (E := E) d t (hilbertModuleFibreOperator t R z) =
        gradedKasparovFirstFibreProductOperator (E := E) d t R
          (gradedKasparovFirstFibreTensorEquiv (E := E) d t z) := by
    simp only [gradedKasparovFirstFibreProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  have hcreation (z : HilbertModuleFibre C C(X, F) t) :
      gradedKasparovFirstFibreTensorEquiv (E := E) d t
        (hilbertModuleFibreRectangularMap t
          (moduleCreationMap (d.continuousSections (X := X)).representation x) z) =
        moduleCreationMap d.representation (hilbertModuleFibreMk (B := B) t x)
          (continuousSectionHilbertModuleFibreEquiv (B := C) t z) :=
    GradedMatrixMoritaFibreCreationCompatibility.first_creation d.representation t x z
  ext y
  simp only [HilbertModuleEquiv.transportMap_apply, hilbertModuleFibreRectangularMap_sub,
    hilbertModuleFibreRectangularMap_comp, hilbertModuleFibreRectangularMap_eq_operator,
    AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub, htransport,
    hcreation, hS, HilbertModuleEquiv.apply_symm_apply]

include hS in
theorem gradedKasparovFirstFibre_creation_defect_add :
    (continuousSectionHilbertModuleFibreEquiv (B := C) (E := F) t).transportMap
      (gradedKasparovFirstFibreTensorEquiv (E := E) d t)
      (hilbertModuleFibreRectangularMap t
        ((moduleCreationMap (d.continuousSections (X := X)).representation x).comp S +
          R.comp (moduleCreationMap (d.continuousSections (X := X)).representation x))) =
      (moduleCreationMap d.representation (hilbertModuleFibreMk (B := B) t x)).comp S₀ +
        (gradedKasparovFirstFibreProductOperator (E := E) d t R).comp
          (moduleCreationMap d.representation (hilbertModuleFibreMk (B := B) t x)) := by
  have htransport (z : HilbertModuleFibre C
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation) t) :
      gradedKasparovFirstFibreTensorEquiv (E := E) d t (hilbertModuleFibreOperator t R z) =
        gradedKasparovFirstFibreProductOperator (E := E) d t R
          (gradedKasparovFirstFibreTensorEquiv (E := E) d t z) := by
    simp only [gradedKasparovFirstFibreProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  have hcreation (z : HilbertModuleFibre C C(X, F) t) :
      gradedKasparovFirstFibreTensorEquiv (E := E) d t
        (hilbertModuleFibreRectangularMap t
          (moduleCreationMap (d.continuousSections (X := X)).representation x) z) =
        moduleCreationMap d.representation (hilbertModuleFibreMk (B := B) t x)
          (continuousSectionHilbertModuleFibreEquiv (B := C) t z) :=
    GradedMatrixMoritaFibreCreationCompatibility.first_creation d.representation t x z
  ext y
  simp only [HilbertModuleEquiv.transportMap_apply, hilbertModuleFibreRectangularMap_add,
    hilbertModuleFibreRectangularMap_comp, hilbertModuleFibreRectangularMap_eq_operator,
    AdjointableMap.comp_apply, AdjointableMap.coe_add_apply, map_add, htransport,
    hcreation, hS, HilbertModuleEquiv.apply_symm_apply]

end Defects

theorem gradedKasparovFirstFibreProduct_connection
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)}
    (hR : GradedKasparovConnection c (d.continuousSections (X := X)) R) :
    GradedKasparovConnection (c.fibre t) d (gradedKasparovFirstFibreProductOperator (E := E) d t R) := by
  have hS (z : HilbertModuleFibre C C(X, F) t) :
      continuousSectionHilbertModuleFibreEquiv (B := C) (E := F) t
        (hilbertModuleFibreOperator t (d.continuousSections (X := X)).operator z) =
          d.operator (continuousSectionHilbertModuleFibreEquiv (B := C) (E := F) t z) :=
    (d.continuousSectionsFibreIso t).operator_intertwine z
  have hSstar (z : HilbertModuleFibre C C(X, F) t) :
      continuousSectionHilbertModuleFibreEquiv (B := C) t
        (hilbertModuleFibreOperator t (star (d.continuousSections (X := X)).operator) z) =
          star d.operator (continuousSectionHilbertModuleFibreEquiv (B := C) t z) := by
    rw [hilbertModuleFibreOperator_star]
    have htransport : (continuousSectionHilbertModuleFibreEquiv (B := C) (E := F) t).transport
        (hilbertModuleFibreOperator t (d.continuousSections (X := X)).operator) =
          d.operator := (d.continuousSectionsFibreIso t).transport_operator
    have hstar : (continuousSectionHilbertModuleFibreEquiv (B := C) (E := F) t).transport
        (star (hilbertModuleFibreOperator t (d.continuousSections (X := X)).operator)) =
          star d.operator := by
      rw [HilbertModuleEquiv.transport_star, htransport]
    have h := congrArg (fun T : AdjointableMap C F F =>
      T (continuousSectionHilbertModuleFibreEquiv (B := C) (E := F) t z)) hstar
    simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h
  constructor
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := c.grading.gradedFibre_even_lift t x hx
    have h := (continuousSectionHilbertModuleFibreEquiv (B := C) t).transportMap_isModuleCompact
      (gradedKasparovFirstFibreTensorEquiv (E := E) d t) ((hR.even y hy).rectangular_fibre t)
    rwa [gradedKasparovFirstFibre_creation_defect_sub d t R (d.continuousSections (X := X)).operator
      d.operator hS y, hyx] at h
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := c.grading.gradedFibre_even_lift t x hx
    have h := (continuousSectionHilbertModuleFibreEquiv (B := C) t).transportMap_isModuleCompact
      (gradedKasparovFirstFibreTensorEquiv (E := E) d t) ((hR.even_adjoint y hy).rectangular_fibre t)
    rw [gradedKasparovFirstFibre_creation_defect_sub d t (star R)
      (star (d.continuousSections (X := X)).operator) (star d.operator) hSstar y, hyx] at h
    simpa only [gradedKasparovFirstFibreProductOperator, hilbertModuleFibreOperator_star,
      HilbertModuleEquiv.transport_star] using h
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := c.grading.gradedFibre_odd_lift t x hx
    have h := (continuousSectionHilbertModuleFibreEquiv (B := C) t).transportMap_isModuleCompact
      (gradedKasparovFirstFibreTensorEquiv (E := E) d t) ((hR.odd y hy).rectangular_fibre t)
    rwa [gradedKasparovFirstFibre_creation_defect_add d t R (d.continuousSections (X := X)).operator
      d.operator hS y, hyx] at h
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := c.grading.gradedFibre_odd_lift t x hx
    have h := (continuousSectionHilbertModuleFibreEquiv (B := C) t).transportMap_isModuleCompact
      (gradedKasparovFirstFibreTensorEquiv (E := E) d t) ((hR.odd_adjoint y hy).rectangular_fibre t)
    rw [gradedKasparovFirstFibre_creation_defect_add d t (star R)
      (star (d.continuousSections (X := X)).operator) (star d.operator) hSstar y, hyx] at h
    simpa only [gradedKasparovFirstFibreProductOperator, hilbertModuleFibreOperator_star,
      HilbertModuleEquiv.transport_star] using h

theorem gradedKasparovFirstFibreProduct_positivityOperator
    (R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)) (a : A) :
    (gradedKasparovFirstFibreTensorEquiv (E := E) d t).transport
      (hilbertModuleFibreOperator t (gradedKasparovProductPositivityOperator c (d.continuousSections (X := X)) R a)) =
      gradedKasparovProductPositivityOperator (c.fibre t) d
        (gradedKasparovFirstFibreProductOperator (E := E) d t R) a := by
  unfold gradedKasparovProductPositivityOperator
  simp only [gradedKasparovTensorRepresentation_apply]
  rw [show (c.fibre t).operator = hilbertModuleFibreOperator (B := B) t c.operator from rfl,
    show (c.fibre t).representation a =
      hilbertModuleFibreOperator (B := B) t (c.representation a) from rfl]
  simp only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_add,
    hilbertModuleFibreOperator_star, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_star,
    gradedKasparovFirstFibreTensorEquiv_operator, gradedKasparovFirstFibreProductOperator]
  have hrepresentation : (gradedKasparovFirstFibreTensorEquiv (E := E) d t).transport
      (hilbertModuleFibreOperator t
        ((gradedKasparovTensorRepresentation c (d.continuousSections (X := X))) a)) =
      interiorModuleTensorOperator d.representation
        (hilbertModuleFibreOperator (B := B) t (c.representation a)) := by
    change (gradedKasparovFirstFibreTensorEquiv (E := E) d t).transport
        (hilbertModuleFibreOperator t
          (interiorModuleTensorOperator (d.continuousSections (X := X)).representation
            (c.representation a))) =
      interiorModuleTensorOperator d.representation
        (hilbertModuleFibreOperator (B := B) t (c.representation a))
    exact gradedKasparovFirstFibreTensorEquiv_operator d t (c.representation a)
  simp only [hrepresentation]

theorem gradedKasparovFirstFibreProduct_isProduct
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)}
    (hR : IsGradedKasparovProductOperator c (d.continuousSections (X := X)) R) :
    IsGradedKasparovProductOperator (c.fibre t) d (gradedKasparovFirstFibreProductOperator (E := E) d t R) where
  cycleConditions := gradedKasparovFirstFibreProduct_conditions c d t hR.cycleConditions
  connection := gradedKasparovFirstFibreProduct_connection c d t hR.connection
  positivity a := by
    have h := ((hR.positivity a).fibre t).transport (gradedKasparovFirstFibreTensorEquiv (E := E) d t)
    rwa [gradedKasparovFirstFibreProduct_positivityOperator] at h

def gradedKasparovFirstFibreProduct_cycleIso
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)
      (InteriorModuleTensor (E := E) (d.continuousSections (X := X)).representation)}
    (hR : IsGradedKasparovProductOperator c (d.continuousSections (X := X)) R) :
    GradedKasparovCycleIso
      ((gradedKasparovTensorCycleOfConditions c (d.continuousSections (X := X)) R hR.cycleConditions).fibre t)
      (gradedKasparovTensorCycleOfConditions (c.fibre t) d
        (gradedKasparovFirstFibreProductOperator (E := E) d t R)
        (gradedKasparovFirstFibreProduct_isProduct c d t hR).cycleConditions) where
  moduleEquiv := gradedKasparovFirstFibreTensorEquiv (E := E) d t
  grading_intertwine := GradedMatrixMoritaFibreTensor.hilbertEquiv_grading d.representation t
    c.grading d.grading d.representation_graded
  action_intertwine := GradedMatrixMoritaFibreTensor.hilbertEquiv_action d.representation t
    c.groupAction d.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
  representation_intertwine := GradedMatrixMoritaFibreTensor.hilbertEquiv_representation
    d.representation t c.representation
  operator_intertwine z := by
    change (gradedKasparovFirstFibreTensorEquiv (E := E) d t)
        (hilbertModuleFibreOperator t R z) =
      (gradedKasparovFirstFibreTensorEquiv (E := E) d t).transport
        (hilbertModuleFibreOperator t R)
          ((gradedKasparovFirstFibreTensorEquiv (E := E) d t) z)
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
