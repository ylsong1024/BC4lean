import BC4lean.GradedKasparovCoefficientTensorInputs
import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.EssentialModulePositivityFibre

/-! # Exact product transport through actual coefficient equivalences

The changed tensor unitary carries the four rectangular connection laws,
all cycle defects and the localized positive lift. The intermediate source
is pulled back by the inverse equivalence before the final coefficients
are changed. Every compactness assertion concerns an actual compact map.
-/

noncomputable section
namespace BC4lean.KKTheory

theorem coefficientChangedOperator_comp
    {B C M N P : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M] [CStarModule Bᵐᵒᵖ M]
    [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [SMul Bᵐᵒᵖ P] [CStarModule Bᵐᵒᵖ P]
    (e : B ≃⋆ₐ[ℂ] C) (S : AdjointableMap B N P) (T : AdjointableMap B M N) :
    coefficientChangedOperator e (S.comp T) =
      (coefficientChangedOperator e S).comp (coefficientChangedOperator e T) := rfl

theorem IsPositiveModuloModuleCompact.coefficientChanged
    {B C M : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M] [CStarModule Bᵐᵒᵖ M]
    [CompleteSpace M] {T : AdjointableMap B M M}
    (hT : IsPositiveModuloModuleCompact T) (e : B ≃⋆ₐ[ℂ] C) :
    IsPositiveModuloModuleCompact (coefficientChangedOperator e T) := by
  obtain ⟨V, hV⟩ := hT.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).2
  refine ⟨coefficientChangedOperator e V, ?_⟩
  simpa only [coefficientChangedOperator_sub, coefficientChangedOperator_mul,
    coefficientChangedOperator_star] using hV.coefficientChanged e

namespace GradedKasparovCoefficientProduct
open GradedKasparovCoefficientTensorInputs

variable {Γ A B B' C C' E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction Γ B'}
  {γ : CStarAlgebraAction Γ C} {γ' : CStarAlgebraAction Γ C'}
  {δA : CStarGrading A} {δB : CStarGrading B} {δB' : CStarGrading B'}
  {δC : CStarGrading C} {δC' : CStarGrading C'}
  (eB : GradedCoefficientEquiv β δB β' δB') (eC : GradedCoefficientEquiv γ δC γ' δC')
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)

def operator (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) :
    AdjointableMap C' (InteriorModuleTensor (E := CoefficientChangedModule eB.starAlgEquiv E)
        (second eB eC d).representation)
      (InteriorModuleTensor (E := CoefficientChangedModule eB.starAlgEquiv E)
        (second eB eC d).representation) :=
  (hilbertEquiv (E := E) eB eC d).transport (coefficientChangedOperator eC.starAlgEquiv R)

theorem conditions {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}
    (hR : GradedKasparovTensorOperatorConditions c d R) :
    GradedKasparovTensorOperatorConditions (first eB c) (second eB eC d) (operator eB eC d R) :=
  transportedCycle_tensorConditions (first eB c) (second eB eC d)
    ((gradedKasparovTensorCycleOfConditions c d R hR).changeCoefficients eC)
    (hilbertEquiv (E := E) eB eC d)
    (hilbertEquiv_grading eB eC c d) (hilbertEquiv_action eB eC c d)
    (hilbertEquiv_representation eB eC c d)

section Defects
variable (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) (T : AdjointableMap C F F) (x : E)

theorem creation_defect_sub :
    (hilbertEquiv (E := E) eB eC d).toAdjointable.comp
      (coefficientChangedOperator eC.starAlgEquiv
        ((moduleCreationMap d.representation x).comp T - R.comp (moduleCreationMap d.representation x))) =
      (moduleCreationMap (second eB eC d).representation (coefficientChangedLinearIsometry eB.starAlgEquiv x)).comp
        (coefficientChangedOperator eC.starAlgEquiv T) -
      (operator eB eC d R).comp
        (moduleCreationMap (second eB eC d).representation (coefficientChangedLinearIsometry eB.starAlgEquiv x)) := by
  have hθ (y : CoefficientChangedModule eC.starAlgEquiv F) :
      hilbertEquiv (E := E) eB eC d
        (coefficientChangedOperator eC.starAlgEquiv (moduleCreationMap d.representation x) y) =
      moduleCreationMap (second eB eC d).representation
        (coefficientChangedLinearIsometry eB.starAlgEquiv x) y := by
    simpa only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply] using
      congrArg (fun V => V y) (creation_operator (E := E) eB eC d x)
  have hQ (z : CoefficientChangedModule eC.starAlgEquiv
      (InteriorModuleTensor (E := E) d.representation)) :
      hilbertEquiv (E := E) eB eC d (coefficientChangedOperator eC.starAlgEquiv R z) =
        operator eB eC d R (hilbertEquiv (E := E) eB eC d z) := by
    simp only [operator, HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
  ext y
  simp only [coefficientChangedOperator_sub, coefficientChangedOperator_comp,
    AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply, map_sub, hθ, hQ]

theorem creation_defect_add :
    (hilbertEquiv (E := E) eB eC d).toAdjointable.comp
      (coefficientChangedOperator eC.starAlgEquiv
        ((moduleCreationMap d.representation x).comp T + R.comp (moduleCreationMap d.representation x))) =
      (moduleCreationMap (second eB eC d).representation (coefficientChangedLinearIsometry eB.starAlgEquiv x)).comp
        (coefficientChangedOperator eC.starAlgEquiv T) +
      (operator eB eC d R).comp
        (moduleCreationMap (second eB eC d).representation (coefficientChangedLinearIsometry eB.starAlgEquiv x)) := by
  have hθ (y : CoefficientChangedModule eC.starAlgEquiv F) :
      hilbertEquiv (E := E) eB eC d
        (coefficientChangedOperator eC.starAlgEquiv (moduleCreationMap d.representation x) y) =
      moduleCreationMap (second eB eC d).representation
        (coefficientChangedLinearIsometry eB.starAlgEquiv x) y := by
    simpa only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply] using
      congrArg (fun V => V y) (creation_operator (E := E) eB eC d x)
  have hQ (z : CoefficientChangedModule eC.starAlgEquiv
      (InteriorModuleTensor (E := E) d.representation)) :
      hilbertEquiv (E := E) eB eC d (coefficientChangedOperator eC.starAlgEquiv R z) =
        operator eB eC d R (hilbertEquiv (E := E) eB eC d z) := by
    simp only [operator, HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
  ext y
  simp only [coefficientChangedOperator_add, coefficientChangedOperator_comp,
    AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
    HilbertModuleEquiv.toAdjointable_apply, map_add, hθ, hQ]

end Defects

theorem connection {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)} (hR : GradedKasparovConnection c d R) :
    GradedKasparovConnection (first eB c) (second eB eC d) (operator eB eC d R) := by
  constructor
  · intro x' hx'
    obtain ⟨x, rfl⟩ := (coefficientChangedLinearIsometry eB.starAlgEquiv).surjective x'
    have hx : c.grading.grading x = x := hx'
    have h := ((hR.even x hx).coefficientChanged eC.starAlgEquiv).comp_left
      (hilbertEquiv (E := E) eB eC d).toAdjointable
    rwa [creation_defect_sub eB eC d R d.operator x] at h
  · intro x' hx'
    obtain ⟨x, rfl⟩ := (coefficientChangedLinearIsometry eB.starAlgEquiv).surjective x'
    have hx : c.grading.grading x = x := hx'
    have h := ((hR.even_adjoint x hx).coefficientChanged eC.starAlgEquiv).comp_left
      (hilbertEquiv (E := E) eB eC d).toAdjointable
    rw [creation_defect_sub eB eC d (star R) (star d.operator) x] at h
    have hD : (second eB eC d).operator = coefficientChangedOperator eC.starAlgEquiv d.operator := rfl
    rw [hD]
    simpa only [operator, coefficientChangedOperator_star, HilbertModuleEquiv.transport_star] using h
  · intro x' hx'
    obtain ⟨x, rfl⟩ := (coefficientChangedLinearIsometry eB.starAlgEquiv).surjective x'
    have hx : c.grading.grading x = -x := hx'
    have h := ((hR.odd x hx).coefficientChanged eC.starAlgEquiv).comp_left
      (hilbertEquiv (E := E) eB eC d).toAdjointable
    rwa [creation_defect_add eB eC d R d.operator x] at h
  · intro x' hx'
    obtain ⟨x, rfl⟩ := (coefficientChangedLinearIsometry eB.starAlgEquiv).surjective x'
    have hx : c.grading.grading x = -x := hx'
    have h := ((hR.odd_adjoint x hx).coefficientChanged eC.starAlgEquiv).comp_left
      (hilbertEquiv (E := E) eB eC d).toAdjointable
    rw [creation_defect_add eB eC d (star R) (star d.operator) x] at h
    have hD : (second eB eC d).operator = coefficientChangedOperator eC.starAlgEquiv d.operator := rfl
    rw [hD]
    simpa only [operator, coefficientChangedOperator_star, HilbertModuleEquiv.transport_star] using h

theorem positivityOperator (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) (a : A) :
    (hilbertEquiv (E := E) eB eC d).transport
      (coefficientChangedOperator eC.starAlgEquiv (gradedKasparovProductPositivityOperator c d R a)) =
      gradedKasparovProductPositivityOperator (first eB c) (second eB eC d)
        (operator eB eC d R) a := by
  have hF : (first eB c).operator = coefficientChangedOperator eB.starAlgEquiv c.operator := rfl
  simp only [gradedKasparovProductPositivityOperator, coefficientChangedOperator_mul,
    coefficientChangedOperator_add, coefficientChangedOperator_star,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_star, transport_representation eB eC c d,
    transport_firstOperator eB eC d, operator, hF]

theorem isProduct {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    IsGradedKasparovProductOperator (first eB c) (second eB eC d) (operator eB eC d R) where
  cycleConditions := conditions eB eC c d hR.cycleConditions
  connection := connection eB eC c d hR.connection
  positivity a := by
    have h := ((hR.positivity a).coefficientChanged eC.starAlgEquiv).transport
      (hilbertEquiv (E := E) eB eC d)
    rwa [positivityOperator] at h

def cycleIso {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    GradedKasparovCycleIso
      ((gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).changeCoefficients eC)
      (gradedKasparovTensorCycleOfConditions (first eB c) (second eB eC d) (operator eB eC d R)
        (isProduct eB eC c d hR).cycleConditions) :=
  transportedCycle_tensorIso (first eB c) (second eB eC d)
    ((gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).changeCoefficients eC)
    (hilbertEquiv (E := E) eB eC d)
    (hilbertEquiv_grading eB eC c d) (hilbertEquiv_action eB eC c d)
    (hilbertEquiv_representation eB eC c d)

end GradedKasparovCoefficientProduct
end BC4lean.KKTheory
