import BC4lean.GradedKasparovSourcePullback
import BC4lean.GradedInteriorModuleTensorCoefficientEquiv
import BC4lean.GradedKasparovProductCriterion

/-! # Actual simultaneous coefficient-change input cycles and tensor data

The first cycle changes its right coefficient algebra. The second cycle
precomposes its genuine left representation with the inverse intermediate
star equivalence and changes its final coefficients. These are actual cycles.
The constructed coefficient-change tensor unitary intertwines their canonical
tensor grading, action, source representation, first lift and rectangular
creation maps. This leaf assumes no product or Morita law.
-/

noncomputable section
namespace BC4lean.KKTheory

theorem GradedCoefficientEquiv.preservesGrading
    {Γ B B' : Type*} [Group Γ] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra B']
    {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction Γ B'}
    {δB : CStarGrading B} {δB' : CStarGrading B'}
    (e : GradedCoefficientEquiv β δB β' δB') (h : β.PreservesGrading δB) :
    β'.PreservesGrading δB' := by
  intro g b
  obtain ⟨a, rfl⟩ := e.starAlgEquiv.surjective b
  change (β'.automorphism g) (δB'.automorphism (e.starAlgEquiv a)) =
    δB'.automorphism ((β'.automorphism g) (e.starAlgEquiv a))
  rw [← e.grading_intertwine, ← e.action_intertwine, h, e.grading_intertwine, e.action_intertwine]

namespace GradedKasparovCoefficientTensorInputs

variable {Γ A B B' C C' E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction Γ B'}
  {γ : CStarAlgebraAction Γ C} {γ' : CStarAlgebraAction Γ C'}
  {δA : CStarGrading A} {δB : CStarGrading B} {δB' : CStarGrading B'}
  {δC : CStarGrading C} {δC' : CStarGrading C'}
  (eB : GradedCoefficientEquiv β δB β' δB') (eC : GradedCoefficientEquiv γ δC γ' δC')

def first (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle α β' δA δB' (CoefficientChangedModule eB.starAlgEquiv E) :=
  c.changeCoefficients eB

def second (d : GradedKasparovCycle β γ δB δC F) :
    GradedKasparovCycle β' γ' δB' δC' (CoefficientChangedModule eC.starAlgEquiv F) :=
  (d.sourcePullback β' δB' (eB.preservesGrading d.sourceAction_preservesGrading)
    eB.symm.starAlgEquiv.toNonUnitalStarAlgHom eB.symm.action_intertwine
      eB.symm.grading_intertwine).changeCoefficients eC

@[simp] theorem second_representation {Γ B B' C C' F : Type*} [Group Γ]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NonUnitalCStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [NonUnitalCStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
    [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
    {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction Γ B'}
    {γ : CStarAlgebraAction Γ C} {γ' : CStarAlgebraAction Γ C'}
    {δB : CStarGrading B} {δB' : CStarGrading B'}
    {δC : CStarGrading C} {δC' : CStarGrading C'}
    (eB : GradedCoefficientEquiv β δB β' δB') (eC : GradedCoefficientEquiv γ δC γ' δC')
    (d : GradedKasparovCycle β γ δB δC F) :
    (second eB eC d).representation =
      InteriorModuleTensorCoefficientEquiv.leftAction eB.starAlgEquiv eC.starAlgEquiv d.representation := rfl

variable (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)

def hilbertEquiv : HilbertModuleEquiv C'
    (CoefficientChangedModule eC.starAlgEquiv (InteriorModuleTensor (E := E) d.representation))
    (InteriorModuleTensor (E := CoefficientChangedModule eB.starAlgEquiv E) (second eB eC d).representation) :=
  InteriorModuleTensorCoefficientEquiv.hilbertEquiv eB.starAlgEquiv eC.starAlgEquiv d.representation

@[simp] theorem hilbertEquiv_mk (x : E) (y : F) :
    hilbertEquiv (E := E) eB eC d
      (coefficientChangedLinearIsometry eC.starAlgEquiv (interiorModuleTensorMk d.representation x y)) =
      interiorModuleTensorMk (second eB eC d).representation
        (coefficientChangedLinearIsometry eB.starAlgEquiv x) (coefficientChangedLinearIsometry eC.starAlgEquiv y) :=
  InteriorModuleTensorCoefficientEquiv.hilbertEquiv_mk _ _ _ x y

theorem hilbertEquiv_grading (z : CoefficientChangedModule eC.starAlgEquiv
    (InteriorModuleTensor (E := E) d.representation)) :
    hilbertEquiv (E := E) eB eC d
      (((gradedKasparovTensorGrading c d).coefficientChanged eC.starAlgEquiv δC' eC.grading_intertwine).grading z) =
      (gradedKasparovTensorGrading (first eB c) (second eB eC d)).grading
        (hilbertEquiv (E := E) eB eC d z) :=
  InteriorModuleTensorCoefficientEquiv.hilbertEquiv_grading eB.starAlgEquiv eC.starAlgEquiv
    d.representation δB' δC' eB.grading_intertwine eC.grading_intertwine
      c.grading d.grading d.representation_graded z

theorem hilbertEquiv_action (g : Γ) (z : CoefficientChangedModule eC.starAlgEquiv
    (InteriorModuleTensor (E := E) d.representation)) :
    hilbertEquiv (E := E) eB eC d
      (((gradedKasparovTensorAction c d).coefficientChanged eC.starAlgEquiv γ' eC.action_intertwine).action g z) =
      (gradedKasparovTensorAction (first eB c) (second eB eC d)).action g
        (hilbertEquiv (E := E) eB eC d z) :=
  InteriorModuleTensorCoefficientEquiv.hilbertEquiv_action eB.starAlgEquiv eC.starAlgEquiv
    d.representation β' γ' eB.action_intertwine eC.action_intertwine c.groupAction d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant) g z

theorem hilbertEquiv_representation (a : A) (z : CoefficientChangedModule eC.starAlgEquiv
    (InteriorModuleTensor (E := E) d.representation)) :
    hilbertEquiv (E := E) eB eC d
      (coefficientChangedOperator eC.starAlgEquiv (gradedKasparovTensorRepresentation c d a) z) =
      gradedKasparovTensorRepresentation (first eB c) (second eB eC d) a
        (hilbertEquiv (E := E) eB eC d z) :=
  InteriorModuleTensorCoefficientEquiv.hilbertEquiv_representation eB.starAlgEquiv eC.starAlgEquiv
    d.representation c.representation a z

theorem transport_firstOperator (T : AdjointableMap B E E) :
    (hilbertEquiv (E := E) eB eC d).transport
      (coefficientChangedOperator eC.starAlgEquiv (interiorModuleTensorOperator d.representation T)) =
      interiorModuleTensorOperator (second eB eC d).representation (coefficientChangedOperator eB.starAlgEquiv T) :=
  InteriorModuleTensorCoefficientEquiv.transport_firstOperator _ _ _ T

theorem transport_representation (a : A) :
    (hilbertEquiv (E := E) eB eC d).transport
      (coefficientChangedOperator eC.starAlgEquiv (gradedKasparovTensorRepresentation c d a)) =
      gradedKasparovTensorRepresentation (first eB c) (second eB eC d) a :=
  transport_firstOperator eB eC d (c.representation a)

theorem creation_operator (x : E) :
    (hilbertEquiv (E := E) eB eC d).toAdjointable.comp
      (coefficientChangedOperator eC.starAlgEquiv (moduleCreationMap d.representation x)) =
      moduleCreationMap (second eB eC d).representation (coefficientChangedLinearIsometry eB.starAlgEquiv x) :=
  InteriorModuleTensorCoefficientEquiv.creation_operator _ _ _ x

theorem creation_adjoint_operator (x : E) :
    coefficientChangedOperator eC.starAlgEquiv (moduleCreationMap d.representation x).adjoint =
      (moduleCreationMap (second eB eC d).representation
        (coefficientChangedLinearIsometry eB.starAlgEquiv x)).adjoint.comp
          (hilbertEquiv (E := E) eB eC d).toAdjointable :=
  InteriorModuleTensorCoefficientEquiv.creation_adjoint_operator _ _ _ x

end GradedKasparovCoefficientTensorInputs
end BC4lean.KKTheory
