import BC4lean.GradedMatrixMoritaTensorUnitary
import BC4lean.GradedKasparovProductCriterion
import BC4lean.GradedKasparovCycleIso

/-! # Actual second-cycle tensor unitary and all input intertwinings

The Hilbert-module unitary is the previously constructed separated and
completed map `x ⊗ y ↦ x ⊗ e(y)`. That construction proves balance, the whole
inner pairing, radical descent, completion and surjectivity. This leaf applies
an actual second-cycle isomorphism to its exact representation hypothesis,
then proves grading, action, first-operator, source-representation, creation
and creation-adjoint identities on the entire completed tensor.

No second-factor tensor operator is asserted for an arbitrary Fredholm
operator: the second operator is intertwined after composing with creation.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedKasparovSecondTensorUnitary
open scoped InnerProductSpace

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

variable (d : GradedKasparovCycle β γ δB δC F)
  (d' : GradedKasparovCycle β γ δB δC G) (e : GradedKasparovCycleIso d d')

def hilbertEquiv : HilbertModuleEquiv C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d'.representation) :=
  GradedMatrixMoritaTensorUnitary.hilbertEquiv d.representation d'.representation
    e.moduleEquiv e.representation_intertwine

@[simp] theorem hilbertEquiv_mk (x : E) (y : F) :
    hilbertEquiv d d' e (interiorModuleTensorMk d.representation x y) =
      interiorModuleTensorMk d'.representation x (e.moduleEquiv y) :=
  GradedMatrixMoritaTensorUnitary.hilbertEquiv_mk _ _ _ _ x y

theorem hilbertEquiv_inner (x y : InteriorModuleTensor (E := E) d.representation) :
    ⟪hilbertEquiv d d' e x, hilbertEquiv d d' e y⟫_(Cᵐᵒᵖ) = ⟪x, y⟫_(Cᵐᵒᵖ) :=
  (hilbertEquiv d d' e).inner_map x y

theorem hilbertEquiv_operator (T : AdjointableMap B E E)
    (z : InteriorModuleTensor (E := E) d.representation) :
    hilbertEquiv d d' e (interiorModuleTensorOperator d.representation T z) =
      interiorModuleTensorOperator d'.representation T (hilbertEquiv d d' e z) :=
  GradedMatrixMoritaTensorUnitary.hilbertEquiv_operator _ _ _ _ T z

theorem transport_firstOperator (T : AdjointableMap B E E) :
    (hilbertEquiv d d' e).transport (interiorModuleTensorOperator d.representation T) =
      interiorModuleTensorOperator d'.representation T := by
  apply AdjointableMap.ext
  intro z
  rw [HilbertModuleEquiv.transport_apply, hilbertEquiv_operator,
    HilbertModuleEquiv.apply_symm_apply]

theorem creation (x : E) (y : F) :
    hilbertEquiv d d' e (moduleCreationMap d.representation x y) =
      moduleCreationMap d'.representation x (e.moduleEquiv y) :=
  hilbertEquiv_mk d d' e x y

theorem creation_adjoint (x : E) (z : InteriorModuleTensor (E := E) d.representation) :
    e.moduleEquiv ((moduleCreationMap d.representation x).adjoint z) =
      (moduleCreationMap d'.representation x).adjoint (hilbertEquiv d d' e z) := by
  let U := (hilbertEquiv (E := E) d d' e).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let V := e.moduleEquiv.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : V.comp (moduleCreationMap d.representation x).adjoint.toCLM =
      (moduleCreationMap d'.representation x).adjoint.toCLM.comp U := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro y v
    change e.moduleEquiv
        ((moduleCreationMap d.representation x).adjoint
          (interiorModuleTensorMk d.representation y v)) =
      (moduleCreationMap d'.representation x).adjoint
        (hilbertEquiv d d' e (interiorModuleTensorMk d.representation y v))
    rw [hilbertEquiv_mk]
    change e.moduleEquiv
        ((moduleCreationMap d.representation x).adjoint
          (preModuleTensorMk d.representation y v :
            UniformSpace.Completion (PreHilbertModuleTensor (E := E) d.representation))) =
      (moduleCreationMap d'.representation x).adjoint
        (preModuleTensorMk d'.representation y (e.moduleEquiv v) :
          UniformSpace.Completion (PreHilbertModuleTensor (E := E) d'.representation))
    rw [moduleCreationMap_adjoint_mk, moduleCreationMap_adjoint_mk]
    exact e.representation_intertwine _ _
  exact DFunLike.congr_fun h z

theorem creation_operator (x : E) :
    (hilbertEquiv (E := E) d d' e).toAdjointable.comp (moduleCreationMap d.representation x) =
      (moduleCreationMap d'.representation x).comp e.moduleEquiv.toAdjointable := by
  apply AdjointableMap.ext
  intro y
  exact creation d d' e x y

theorem creation_adjoint_operator (x : E) :
    e.moduleEquiv.toAdjointable.comp (moduleCreationMap d.representation x).adjoint =
      (moduleCreationMap d'.representation x).adjoint.comp
        (hilbertEquiv (E := E) d d' e).toAdjointable := by
  apply AdjointableMap.ext
  intro z
  exact creation_adjoint d d' e x z

theorem creation_secondOperator (x : E) (y : F) :
    hilbertEquiv d d' e (moduleCreationMap d.representation x (d.operator y)) =
      moduleCreationMap d'.representation x (d'.operator (e.moduleEquiv y)) := by
  rw [creation, e.operator_intertwine]

theorem creation_secondOperator_adjoint (x : E) (y : F) :
    hilbertEquiv d d' e (moduleCreationMap d.representation x (star d.operator y)) =
      moduleCreationMap d'.representation x (star d'.operator (e.moduleEquiv y)) := by
  have h : e.moduleEquiv (star d.operator y) = star d'.operator (e.moduleEquiv y) := by
    rw [← e.transport_operator, ← HilbertModuleEquiv.transport_star,
      HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
  rw [creation, h]

variable (c : GradedKasparovCycle α β δA δB E)

theorem hilbertEquiv_grading (z : InteriorModuleTensor (E := E) d.representation) :
    hilbertEquiv d d' e ((gradedKasparovTensorGrading c d).grading z) =
      (gradedKasparovTensorGrading c d').grading (hilbertEquiv d d' e z) := by
  let U := (hilbertEquiv (E := E) d d' e).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : U.comp (gradedKasparovTensorGrading c d).grading.toContinuousLinearEquiv.toContinuousLinearMap =
      (gradedKasparovTensorGrading c d').grading.toContinuousLinearEquiv.toContinuousLinearMap.comp U := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv d d' e
        ((gradedKasparovTensorGrading c d).grading
          (interiorModuleTensorMk d.representation x y)) =
      (gradedKasparovTensorGrading c d').grading
        (hilbertEquiv d d' e (interiorModuleTensorMk d.representation x y))
    change hilbertEquiv d d' e
        ((c.grading.interiorTensor d.grading d.representation_graded).grading
          (interiorModuleTensorMk d.representation x y)) =
      (c.grading.interiorTensor d'.grading d'.representation_graded).grading
        (hilbertEquiv d d' e (interiorModuleTensorMk d.representation x y))
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := d.representation) c.grading d.grading d.representation_graded x y]
    rw [hilbertEquiv_mk, hilbertEquiv_mk]
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := d'.representation) c.grading d'.grading d'.representation_graded
      x (e.moduleEquiv y)]
    rw [e.grading_intertwine]
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_action (g : Γ) (z : InteriorModuleTensor (E := E) d.representation) :
    hilbertEquiv d d' e ((gradedKasparovTensorAction c d).action g z) =
      (gradedKasparovTensorAction c d').action g (hilbertEquiv d d' e z) := by
  let U := (hilbertEquiv (E := E) d d' e).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : U.comp ((gradedKasparovTensorAction c d).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      ((gradedKasparovTensorAction c d').action g).toContinuousLinearEquiv.toContinuousLinearMap.comp U := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv d d' e
        ((gradedKasparovTensorAction c d).action g
          (interiorModuleTensorMk d.representation x y)) =
      (gradedKasparovTensorAction c d').action g
        (hilbertEquiv d d' e (interiorModuleTensorMk d.representation x y))
    simp only [gradedKasparovTensorAction,
      EquivariantHilbertModule.interiorTensor_action_mk, hilbertEquiv_mk, e.action_intertwine]
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_representation (a : A)
    (z : InteriorModuleTensor (E := E) d.representation) :
    hilbertEquiv d d' e (gradedKasparovTensorRepresentation c d a z) =
      gradedKasparovTensorRepresentation c d' a (hilbertEquiv d d' e z) :=
  hilbertEquiv_operator d d' e (c.representation a) z

theorem transport_representation (a : A) :
    (hilbertEquiv (E := E) d d' e).transport (gradedKasparovTensorRepresentation c d a) =
      gradedKasparovTensorRepresentation c d' a :=
  transport_firstOperator d d' e (c.representation a)

end BC4lean.KKTheory.GradedKasparovSecondTensorUnitary
