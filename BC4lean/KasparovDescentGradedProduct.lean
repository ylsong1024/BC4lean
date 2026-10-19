import BC4lean.KasparovDescentConnection
import BC4lean.KasparovDescentTensorComparisonGrading
import BC4lean.KasparovDescentTensorComparisonSource
import BC4lean.KasparovDescentProductPositivity
import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.EssentialModulePositivityFibre

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine graded product-criterion transport under reduced descent

The construction uses the actual comparison, connection, raw graded
descent and full quadratic positivity results.


Given an actual original product operator R, tensor its actual cycle, then
transport by the inverse of the constructed crossed tensor unitary. Existing
whole-cycle tensor transport gives all genuine descended cycle conditions.
The separately proved four connection laws and full quadratic positivity
on every completed crossed source element give the existing actual graded
product criterion. No descended product field or desired criterion is an
input hypothesis. Native degree/Clifford/Morita comparison remains separate.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  [Countable Γ] [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
  (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
  (hR : GradedKasparovTensorOperatorConditions c d R)

/-- The actual descended original tensor cycle, before changing its whole carrier. -/
def descendedOriginalTensorCycle :=
  gradedCycle γ α (gradedKasparovTensorCycleOfConditions c d R hR)

private theorem productDescent_inverse_of_forward_aux
    {D M N : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Dᵐᵒᵖ M] [CStarModule Dᵐᵒᵖ M]
    [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Dᵐᵒᵖ N] [CStarModule Dᵐᵒᵖ N]
    (Q : HilbertModuleEquiv D M N) (S : M → M) (T : N → N)
    (h : ∀ v, Q (S v) = T (Q v)) (x : N) :
    Q.symm (T x) = S (Q.symm x) := by
  have hx : Q (S (Q.symm x)) = T x :=
    (h (Q.symm x)).trans (congrArg T (Q.apply_symm_apply x))
  exact (congrArg (fun v : N => Q.symm v) hx).symm.trans
    (Q.symm_apply_apply (S (Q.symm x)))

private theorem productDescent_unit_action_aux
    {D M : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Dᵐᵒᵖ M] [CStarModule Dᵐᵒᵖ M]
    {η : CStarAlgebraAction Unit D}
    (V : EquivariantHilbertModule η M) (g : Unit) (x : M) :
    V.action g x = x := by
  have hg : g = (1 : Unit) := Subsingleton.elim g 1
  exact (congrArg (fun h : Unit => V.action h x) hg).trans (V.one_apply x)

omit [TopologicalSpace.SeparableSpace B] in
private theorem productDescent_original_grading_selector_aux
    (x : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    (descendedOriginalTensorCycle α β γ c d R hR).grading.grading x =
      (moduleGrading γ δC d.coefficientAction_preservesGrading
        (c.grading.interiorTensor d.grading d.representation_graded)).grading x :=
  rfl

private theorem productDescent_tensor_grading_selector_aux
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)) :
    (gradedKasparovTensorGrading (gradedCycle β α c) (gradedCycle γ β d)).grading u =
      (((moduleGrading β δB d.sourceAction_preservesGrading c.grading).interiorTensor
        (moduleGrading γ δC d.coefficientAction_preservesGrading d.grading)
        (fun z v => reducedSourceRepresentation_graded γ β d z v)).grading u) :=
  rfl

omit [PartialOrder A] [StarOrderedRing A] [Countable Γ]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] in
private theorem productDescent_inverse_grading_native_aux
    (x : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm
        ((moduleGrading γ δC d.coefficientAction_preservesGrading
          (c.grading.interiorTensor d.grading d.representation_graded)).grading x) =
      (((moduleGrading β δB d.sourceAction_preservesGrading c.grading).interiorTensor
        (moduleGrading γ δC d.coefficientAction_preservesGrading d.grading)
        (fun z v => reducedSourceRepresentation_graded γ β d z v)).grading
        ((tensorComparison (E := E) β γ d.groupAction d.representation
          d.representation_equivariant).symm x)) :=
  productDescent_inverse_of_forward_aux
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant)
    (fun u => (((moduleGrading β δB d.sourceAction_preservesGrading c.grading).interiorTensor
      (moduleGrading γ δC d.coefficientAction_preservesGrading d.grading)
      (fun z v => reducedSourceRepresentation_graded γ β d z v)).grading u))
    (fun v => (moduleGrading γ δC d.coefficientAction_preservesGrading
      (c.grading.interiorTensor d.grading d.representation_graded)).grading v)
    (fun u => tensorComparison_grading β γ c.grading d u) x

private def productDescent_native_tensor_source_aux :=
  reducedSourceRepresentation γ (InteriorModuleTensor (E := E) d.representation) α
    (c.groupAction.interiorTensor d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant))
    (InteriorModuleTensorAssociator.rightRepresentation c.representation d.representation)
    (tensorComparison_tensorRepresentation_equivariant β γ d.groupAction d.representation
      d.representation_equivariant α c.groupAction c.representation c.representation_equivariant)

omit [TopologicalSpace.SeparableSpace B] in
private theorem productDescent_original_representation_selector_aux
    (z : ReducedCrossedProduct α)
    (x : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    (descendedOriginalTensorCycle α β γ c d R hR).representation z x =
      productDescent_native_tensor_source_aux α β γ c d z x :=
  rfl

private theorem productDescent_tensor_representation_selector_aux
    (z : ReducedCrossedProduct α)
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)) :
    gradedKasparovTensorRepresentation (gradedCycle β α c) (gradedCycle γ β d) z u =
      interiorModuleTensorOperator
        (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)
        (reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) u :=
  rfl

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] in
private theorem productDescent_inverse_representation_native_aux
    (z : ReducedCrossedProduct α)
    (x : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm
        (productDescent_native_tensor_source_aux α β γ c d z x) =
      interiorModuleTensorOperator
        (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)
        (reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z)
        ((tensorComparison (E := E) β γ d.groupAction d.representation
          d.representation_equivariant).symm x) :=
  productDescent_inverse_of_forward_aux
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant)
    (fun u => interiorModuleTensorOperator
      (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)
      (reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) u)
    (fun v => productDescent_native_tensor_source_aux α β γ c d z v)
    (fun u => tensorComparison_reducedSourceRepresentation β γ d.groupAction d.representation
      d.representation_equivariant α c.groupAction c.representation c.representation_equivariant z u) x

/-- Inverse comparison intertwines the actual full semilinear tensor gradings. -/
theorem productDescent_inverse_grading
    (x : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    (tensorComparison β γ d.groupAction d.representation d.representation_equivariant).symm
      ((descendedOriginalTensorCycle α β γ c d R hR).grading.grading x) =
      (gradedKasparovTensorGrading (gradedCycle β α c) (gradedCycle γ β d)).grading
        ((tensorComparison β γ d.groupAction d.representation d.representation_equivariant).symm x) := by
  let Q := tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant
  exact (congrArg
    (fun v : Module γ (InteriorModuleTensor (E := E) d.representation) => Q.symm v)
    (productDescent_original_grading_selector_aux α β γ c d R hR x)).trans
    ((productDescent_inverse_grading_native_aux α β γ c d x).trans
      (productDescent_tensor_grading_selector_aux α β γ c d (Q.symm x)).symm)

/-- Both actual target equivariance actions are trivial Unit actions. -/
theorem productDescent_inverse_action (g : Unit)
    (x : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    (tensorComparison β γ d.groupAction d.representation d.representation_equivariant).symm
      ((descendedOriginalTensorCycle α β γ c d R hR).groupAction.action g x) =
      (gradedKasparovTensorAction (gradedCycle β α c) (gradedCycle γ β d)).action g
        ((tensorComparison β γ d.groupAction d.representation d.representation_equivariant).symm x) := by
  let Q := tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant
  exact (congrArg
    (fun v : Module γ (InteriorModuleTensor (E := E) d.representation) => Q.symm v)
    (productDescent_unit_action_aux
      (descendedOriginalTensorCycle α β γ c d R hR).groupAction g x)).trans
    (productDescent_unit_action_aux
      (gradedKasparovTensorAction (gradedCycle β α c) (gradedCycle γ β d)) g (Q.symm x)).symm

/-- The inverse unitary intertwines the actual integrated source representation
with the canonical tensor representation of the actual descended cycles. -/
theorem productDescent_inverse_representation (z : ReducedCrossedProduct α)
    (x : Module γ (InteriorModuleTensor (E := E) d.representation)) :
    (tensorComparison β γ d.groupAction d.representation d.representation_equivariant).symm
      ((descendedOriginalTensorCycle α β γ c d R hR).representation z x) =
      gradedKasparovTensorRepresentation (gradedCycle β α c) (gradedCycle γ β d) z
        ((tensorComparison β γ d.groupAction d.representation d.representation_equivariant).symm x) := by
  let Q := tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant
  exact (congrArg
    (fun v : Module γ (InteriorModuleTensor (E := E) d.representation) => Q.symm v)
    (productDescent_original_representation_selector_aux α β γ c d R hR z x)).trans
    ((productDescent_inverse_representation_native_aux α β γ c d z x).trans
      (productDescent_tensor_representation_selector_aux α β γ c d z (Q.symm x)).symm)

include hR in
/-- Existing genuine cycle transport proves all five analytic/parity conditions
of the descended canonical tensor operator from the actual descended cycle. -/
theorem descended_product_cycleConditions :
    GradedKasparovTensorOperatorConditions (gradedCycle β α c) (gradedCycle γ β d)
      (descendedConnectionOperator β γ d.groupAction d.representation d.representation_equivariant R) :=
  transportedCycle_tensorConditions (gradedCycle β α c) (gradedCycle γ β d)
    (descendedOriginalTensorCycle α β γ c d R hR)
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm
    (productDescent_inverse_grading α β γ c d R hR)
    (productDescent_inverse_action α β γ c d R hR)
    (productDescent_inverse_representation α β γ c d R hR)

/-- The same actual whole-cycle transport supplies an isomorphism to the
canonical descended tensor cycle, intertwining every field exactly. -/
def descended_product_cycleIso :
    GradedKasparovCycleIso (descendedOriginalTensorCycle α β γ c d R hR)
      (gradedKasparovTensorCycleOfConditions (gradedCycle β α c) (gradedCycle γ β d)
        (descendedConnectionOperator β γ d.groupAction d.representation d.representation_equivariant R)
        (descended_product_cycleConditions α β γ c d R hR)) :=
  transportedCycle_tensorIso (gradedCycle β α c) (gradedCycle γ β d)
    (descendedOriginalTensorCycle α β γ c d R hR)
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm
    (productDescent_inverse_grading α β γ c d R hR)
    (productDescent_inverse_action α β γ c d R hR)
    (productDescent_inverse_representation α β γ c d R hR)

private theorem productDescent_inverse_transport_of_intertwine
    {D M N : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Dᵐᵒᵖ M]
    [CStarModule Dᵐᵒᵖ M]
    [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Dᵐᵒᵖ N]
    [CStarModule Dᵐᵒᵖ N]
    (u : HilbertModuleEquiv D M N)
    (S : AdjointableMap D M M) (T : AdjointableMap D N N)
    (h : ∀ x : M, u (S x) = T (u x)) :
    u.symm.transport T = S := by
  have hu : u.transport S = T := by
    apply AdjointableMap.ext
    intro y
    exact (u.transport_apply S y).trans
      ((h (u.symm y)).trans
        (congrArg (fun w : N => T w) (u.apply_symm_apply y)))
  exact (congrArg
    (fun W : AdjointableMap D N N => u.symm.transport W) hu).symm.trans
      (u.transport_symm S)

omit [PartialOrder A] [StarOrderedRing A] [Countable Γ]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] in
/-- The original first operator is genuinely intertwined by the whole unitary. -/
theorem productDescent_transport_firstOperator :
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm.transport
      (operatorHom γ (InteriorModuleTensor (E := E) d.representation)
        (interiorModuleTensorOperator d.representation c.operator)) =
      interiorModuleTensorOperator
        (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)
        (operatorHom β E c.operator) := by
  exact productDescent_inverse_transport_of_intertwine
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant)
    (interiorModuleTensorOperator
      (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)
      (operatorHom β E c.operator))
    (operatorHom γ (InteriorModuleTensor (E := E) d.representation)
      (interiorModuleTensorOperator d.representation c.operator))
    (tensorComparison_operator β γ d.groupAction d.representation d.representation_equivariant
      c.operator)

/-- Actual integrated source operators are transported to the actual canonical
source tensor operators; the target is not an auxiliary representation. -/
theorem productDescent_transport_representation (z : ReducedCrossedProduct α) :
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm.transport
      ((descendedOriginalTensorCycle α β γ c d R hR).representation z) =
      gradedKasparovTensorRepresentation (gradedCycle β α c) (gradedCycle γ β d) z :=
  transportedCycle_tensorRepresentation (gradedCycle β α c) (gradedCycle γ β d)
    (descendedOriginalTensorCycle α β γ c d R hR)
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm
    (productDescent_inverse_representation α β γ c d R hR) z

omit [TopologicalSpace.SeparableSpace B] in
private theorem productDescent_original_representation_selector (z : ReducedCrossedProduct α) :
    reducedSourceRepresentation γ (InteriorModuleTensor (E := E) d.representation) α
      (gradedKasparovTensorCycleOfConditions c d R hR).groupAction
      (gradedKasparovTensorCycleOfConditions c d R hR).representation
      (gradedKasparovTensorCycleOfConditions c d R hR).representation_equivariant z =
    (descendedOriginalTensorCycle α β γ c d R hR).representation z := rfl

private theorem productDescent_descended_firstOperator_selector :
    interiorModuleTensorOperator
      (reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant)
      (operatorHom β E c.operator) =
    interiorModuleTensorOperator (gradedCycle γ β d).representation
      (gradedCycle β α c).operator := rfl

private theorem productDescent_transport_original_representation (z : ReducedCrossedProduct α) :
    (tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant).symm.transport
      (reducedSourceRepresentation γ (InteriorModuleTensor (E := E) d.representation) α
        (gradedKasparovTensorCycleOfConditions c d R hR).groupAction
        (gradedKasparovTensorCycleOfConditions c d R hR).representation
        (gradedKasparovTensorCycleOfConditions c d R hR).representation_equivariant z) =
    gradedKasparovTensorRepresentation (gradedCycle β α c) (gradedCycle γ β d) z := by
  let Q := tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant
  exact (congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct γ)
      (Module γ (InteriorModuleTensor (E := E) d.representation))
      (Module γ (InteriorModuleTensor (E := E) d.representation)) => Q.symm.transport T)
    (productDescent_original_representation_selector α β γ c d R hR z)).trans
      (productDescent_transport_representation α β γ c d R hR z)

include hR in
/-- FULL crossed positivity is supplied by the coefficient-AU quadratic theorem
and preserved by the actual unitary star equivalence. It quantifies over every
completed crossed source element, not merely over generators. -/
theorem descended_product_positivity
    (hPositive : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator c d R a))
    (z : ReducedCrossedProduct α) :
    IsPositiveModuloModuleCompact
      (gradedKasparovProductPositivityOperator (gradedCycle β α c) (gradedCycle γ β d)
        (descendedConnectionOperator β γ d.groupAction d.representation d.representation_equivariant R) z) := by
  let p := gradedKasparovTensorCycleOfConditions c d R hR
  let Q := tensorComparison (E := E) β γ d.groupAction d.representation d.representation_equivariant
  have h := reducedSourceRepresentation_anticommutator_positive γ
    (InteriorModuleTensor (E := E) d.representation) α p.groupAction p.representation p.representation_equivariant
    (interiorModuleTensorOperator d.representation c.operator) R hPositive z
  have ht := h.transport Q.symm
  have hrep : Q.symm.transport
      (reducedSourceRepresentation γ (InteriorModuleTensor (E := E) d.representation) α
        p.groupAction p.representation p.representation_equivariant z) =
      gradedKasparovTensorRepresentation (gradedCycle β α c) (gradedCycle γ β d) z :=
    productDescent_transport_original_representation α β γ c d R hR z
  have hfirst : Q.symm.transport
      (operatorHom γ (InteriorModuleTensor (E := E) d.representation)
        (interiorModuleTensorOperator d.representation c.operator)) =
      interiorModuleTensorOperator (gradedCycle γ β d).representation
        (gradedCycle β α c).operator :=
    (productDescent_transport_firstOperator α β γ c d).trans
      (productDescent_descended_firstOperator_selector α β γ c d)
  simp only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_star, hrep, hfirst] at ht
  dsimp (config := { instances := true }) only [gradedCycle] at ht ⊢
  simpa only [gradedKasparovProductPositivityOperator, descendedConnectionOperator, Q] using ht

/-- Genuine graded product operators descend to genuine product operators for
the actual descended graded cycles. This is a theorem about the existing
analytic criterion, not a new operation or an assumed product structure. -/
theorem descended_isGradedProduct
    (hProduct : IsGradedKasparovProductOperator c d R) :
    IsGradedKasparovProductOperator (gradedCycle β α c) (gradedCycle γ β d)
      (descendedConnectionOperator β γ d.groupAction d.representation d.representation_equivariant R) where
  cycleConditions := descended_product_cycleConditions α β γ c d R hProduct.cycleConditions
  connection := descended_gradedConnection β γ α c d R hProduct.connection
  positivity := descended_product_positivity α β γ c d R hProduct.cycleConditions hProduct.positivity

end BC4lean.KKTheory.KasparovDescent
