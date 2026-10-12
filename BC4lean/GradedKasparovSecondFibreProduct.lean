import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.EssentialModulePositivityFibre
import BC4lean.GradedMatrixMoritaFibreCreationCompatibility

/-! # Genuine products descend through the second correspondence fibre

The first correspondence is fixed, while the second is an arbitrary complete
module over continuous coefficients. The constructed tensor fibre unitary
transports the actual fibre cycle. Every rectangular connection error is
evaluated before composing with the unitary; localized positive lifts are
evaluated by the genuine star homomorphism. No extension of the second
representation to continuous intermediate coefficients is used.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C X E M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, C)ᵐᵒᵖ M]
  [CStarModule C(X, C)ᵐᵒᵖ M] [CompleteSpace E] [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E)
  (d : GradedKasparovCycle β (γ.continuousSections (X := X)) δB δC.continuousSections M)
  (t : X)

def gradedKasparovSecondFibreTensorEquiv : HilbertModuleEquiv C
    (HilbertModuleFibre C (InteriorModuleTensor (E := E) d.representation) t)
    (InteriorModuleTensor (E := E) (d.fibre t).representation) :=
  GradedMatrixMoritaSecondFibreTensor.hilbertEquiv d.representation t

def gradedKasparovSecondFibreProductOperator
    (R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :
    AdjointableMap C (InteriorModuleTensor (E := E) (d.fibre t).representation)
      (InteriorModuleTensor (E := E) (d.fibre t).representation) :=
  (gradedKasparovSecondFibreTensorEquiv (E := E) d t).transport (hilbertModuleFibreOperator t R)

theorem gradedKasparovSecondFibreTensorEquiv_operator
    (T : AdjointableMap B E E) :
    (gradedKasparovSecondFibreTensorEquiv (E := E) d t).transport
      (hilbertModuleFibreOperator t (interiorModuleTensorOperator d.representation T)) =
        interiorModuleTensorOperator (d.fibre t).representation T := by
  ext y
  rw [HilbertModuleEquiv.transport_apply]
  rw [show (gradedKasparovSecondFibreTensorEquiv (E := E) d t)
      (hilbertModuleFibreOperator t (interiorModuleTensorOperator d.representation T)
        ((gradedKasparovSecondFibreTensorEquiv (E := E) d t).symm y)) =
      interiorModuleTensorOperator (d.fibre t).representation T
        ((gradedKasparovSecondFibreTensorEquiv (E := E) d t)
          ((gradedKasparovSecondFibreTensorEquiv (E := E) d t).symm y)) from
    GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_operator d.representation t T _]
  rw [HilbertModuleEquiv.apply_symm_apply]

theorem gradedKasparovSecondFibreProduct_conditions
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : GradedKasparovTensorOperatorConditions c d R) :
    GradedKasparovTensorOperatorConditions c (d.fibre t)
      (gradedKasparovSecondFibreProductOperator (E := E) d t R) := by
  let k := (gradedKasparovTensorCycleOfConditions c d R hR).fibre t
  apply transportedCycle_tensorConditions c (d.fibre t) k
    (gradedKasparovSecondFibreTensorEquiv (E := E) d t)
  · exact GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_grading d.representation t
      c.grading d.grading d.representation_graded
  · exact GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_action d.representation t
      c.groupAction d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
  · intro a z
    exact GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_representation
      d.representation t c.representation a z

section ConnectionDefects

variable (R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
  (S : AdjointableMap C(X, C) M M) (x : E)

theorem gradedKasparovSecondFibre_creation_defect_sub :
    (gradedKasparovSecondFibreTensorEquiv (E := E) d t).toAdjointable.comp
      (hilbertModuleFibreRectangularMap t ((moduleCreationMap d.representation x).comp S -
        R.comp (moduleCreationMap d.representation x))) =
      (moduleCreationMap (d.fibre t).representation x).comp (hilbertModuleFibreOperator t S) -
        (gradedKasparovSecondFibreProductOperator (E := E) d t R).comp
          (moduleCreationMap (d.fibre t).representation x) := by
  have htransport (z : HilbertModuleFibre C (InteriorModuleTensor (E := E) d.representation) t) :
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t) (hilbertModuleFibreOperator t R z) =
        gradedKasparovSecondFibreProductOperator (E := E) d t R
          ((gradedKasparovSecondFibreTensorEquiv (E := E) d t) z) := by
    simp only [gradedKasparovSecondFibreProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  have hcreation (y : HilbertModuleFibre C M t) :
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t)
        (hilbertModuleFibreRectangularMap t (moduleCreationMap d.representation x) y) =
      moduleCreationMap (d.fibre t).representation x y :=
    GradedMatrixMoritaFibreCreationCompatibility.second_creation
      (E := E) d.representation t x y
  ext y
  simp only [hilbertModuleFibreRectangularMap_sub, hilbertModuleFibreRectangularMap_comp,
    hilbertModuleFibreRectangularMap_eq_operator, AdjointableMap.comp_apply,
    AdjointableMap.coe_sub_apply, HilbertModuleEquiv.toAdjointable_apply, map_sub,
    htransport, hcreation]

theorem gradedKasparovSecondFibre_creation_defect_add :
    (gradedKasparovSecondFibreTensorEquiv (E := E) d t).toAdjointable.comp
      (hilbertModuleFibreRectangularMap t ((moduleCreationMap d.representation x).comp S +
        R.comp (moduleCreationMap d.representation x))) =
      (moduleCreationMap (d.fibre t).representation x).comp (hilbertModuleFibreOperator t S) +
        (gradedKasparovSecondFibreProductOperator (E := E) d t R).comp
          (moduleCreationMap (d.fibre t).representation x) := by
  have htransport (z : HilbertModuleFibre C (InteriorModuleTensor (E := E) d.representation) t) :
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t) (hilbertModuleFibreOperator t R z) =
        gradedKasparovSecondFibreProductOperator (E := E) d t R
          ((gradedKasparovSecondFibreTensorEquiv (E := E) d t) z) := by
    simp only [gradedKasparovSecondFibreProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  have hcreation (y : HilbertModuleFibre C M t) :
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t)
        (hilbertModuleFibreRectangularMap t (moduleCreationMap d.representation x) y) =
      moduleCreationMap (d.fibre t).representation x y :=
    GradedMatrixMoritaFibreCreationCompatibility.second_creation
      (E := E) d.representation t x y
  ext y
  simp only [hilbertModuleFibreRectangularMap_add, hilbertModuleFibreRectangularMap_comp,
    hilbertModuleFibreRectangularMap_eq_operator, AdjointableMap.comp_apply,
    AdjointableMap.coe_add_apply, HilbertModuleEquiv.toAdjointable_apply, map_add,
    htransport, hcreation]

end ConnectionDefects

theorem gradedKasparovSecondFibreProduct_connection
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : GradedKasparovConnection c d R) :
    GradedKasparovConnection c (d.fibre t) (gradedKasparovSecondFibreProductOperator (E := E) d t R) where
  even x hx := by
    have h := ((hR.even x hx).rectangular_fibre t).comp_left
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t).toAdjointable
    rwa [gradedKasparovSecondFibre_creation_defect_sub] at h
  even_adjoint x hx := by
    have h := ((hR.even_adjoint x hx).rectangular_fibre t).comp_left
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t).toAdjointable
    rw [gradedKasparovSecondFibre_creation_defect_sub] at h
    rw [show (d.fibre t).operator = hilbertModuleFibreOperator t d.operator from rfl]
    simpa only [gradedKasparovSecondFibreProductOperator, hilbertModuleFibreOperator_star,
      HilbertModuleEquiv.transport_star] using h
  odd x hx := by
    have h := ((hR.odd x hx).rectangular_fibre t).comp_left
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t).toAdjointable
    rwa [gradedKasparovSecondFibre_creation_defect_add] at h
  odd_adjoint x hx := by
    have h := ((hR.odd_adjoint x hx).rectangular_fibre t).comp_left
      (gradedKasparovSecondFibreTensorEquiv (E := E) d t).toAdjointable
    rw [gradedKasparovSecondFibre_creation_defect_add] at h
    rw [show (d.fibre t).operator = hilbertModuleFibreOperator t d.operator from rfl]
    simpa only [gradedKasparovSecondFibreProductOperator, hilbertModuleFibreOperator_star,
      HilbertModuleEquiv.transport_star] using h

theorem gradedKasparovSecondFibreProduct_positivityOperator
    (R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (a : A) :
    (gradedKasparovSecondFibreTensorEquiv (E := E) d t).transport
      (hilbertModuleFibreOperator t (gradedKasparovProductPositivityOperator c d R a)) =
      gradedKasparovProductPositivityOperator c (d.fibre t)
        (gradedKasparovSecondFibreProductOperator (E := E) d t R) a := by
  simp only [gradedKasparovProductPositivityOperator, gradedKasparovTensorRepresentation_apply,
    hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_add, hilbertModuleFibreOperator_star,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_star, gradedKasparovSecondFibreTensorEquiv_operator,
    gradedKasparovSecondFibreProductOperator]

/-- Actual product membership, including all four connection conditions and
localized positivity, survives evaluation in the second correspondence. -/
theorem gradedKasparovSecondFibreProduct_isProduct
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    IsGradedKasparovProductOperator c (d.fibre t)
      (gradedKasparovSecondFibreProductOperator (E := E) d t R) where
  cycleConditions := gradedKasparovSecondFibreProduct_conditions c d t hR.cycleConditions
  connection := gradedKasparovSecondFibreProduct_connection c d t hR.connection
  positivity a := by
    have h := ((hR.positivity a).fibre t).transport (gradedKasparovSecondFibreTensorEquiv (E := E) d t)
    rwa [gradedKasparovSecondFibreProduct_positivityOperator] at h

def gradedKasparovSecondFibreProduct_cycleIso
    {R : AdjointableMap C(X, C) (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    GradedKasparovCycleIso ((gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).fibre t)
      (gradedKasparovTensorCycleOfConditions c (d.fibre t)
        (gradedKasparovSecondFibreProductOperator (E := E) d t R)
        (gradedKasparovSecondFibreProduct_isProduct c d t hR).cycleConditions) where
  moduleEquiv := gradedKasparovSecondFibreTensorEquiv (E := E) d t
  grading_intertwine := GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_grading d.representation t
    c.grading d.grading d.representation_graded
  action_intertwine := GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_action d.representation t
    c.groupAction d.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
  representation_intertwine := GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_representation
    d.representation t c.representation
  operator_intertwine z := by
    change (gradedKasparovSecondFibreTensorEquiv (E := E) d t)
      (hilbertModuleFibreOperator t R z) =
        gradedKasparovSecondFibreProductOperator (E := E) d t R
          ((gradedKasparovSecondFibreTensorEquiv (E := E) d t) z)
    simp only [gradedKasparovSecondFibreProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
