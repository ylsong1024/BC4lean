import BC4lean.GradedTripleAnticommutatorConnection
import BC4lean.GradedKasparovTensorCycleTransport

/-! # Whole-cycle data and the genuine composed third connection

The actual tensor associator transports the right iterated cycle to the left
tensor, retaining both module gradings, group actions, the represented source
algebra and all localized cycle defects. The two original connections compose
on every completed first-pair vector and give all four original third-factor
connection laws. This constructs the cycle and connection data used before the
common-operator partition; it asserts no associativity or positivity conclusion.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open InteriorModuleTensorAssociator
open GradedTripleAnticommutatorConnection

variable {Γ A B C D E F G : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {χ : CStarAlgebraAction Γ D}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C} {δD : CStarGrading D}
  (c : GradedKasparovCycle α β δA δB E)
  (d : GradedKasparovCycle β γ δB δC F)
  (e : GradedKasparovCycle γ χ δC δD G)
  (Q : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
  (hQ : GradedKasparovTensorOperatorConditions c d Q)
  (T : AdjointableMap D (InteriorModuleTensor (E := F) e.representation)
    (InteriorModuleTensor (E := F) e.representation))
  (hT : GradedKasparovTensorOperatorConditions d e T)

abbrev firstPairCycle := gradedKasparovTensorCycleOfConditions c d Q hQ
abbrev secondPairCycle := gradedKasparovTensorCycleOfConditions d e T hT

theorem triple_grading_intertwine
    (u : LeftTensor (E := E) d.representation e.representation) :
    hilbertEquiv d.representation e.representation
      ((gradedKasparovTensorGrading (firstPairCycle c d Q hQ) e).grading u) =
    (gradedKasparovTensorGrading c (secondPairCycle d e T hT)).grading
      (hilbertEquiv d.representation e.representation u) :=
  hilbertEquiv_grading_intertwine d.representation e.representation c.grading d.grading e.grading
    d.representation_graded e.representation_graded u

theorem triple_action_intertwine (g : Γ)
    (u : LeftTensor (E := E) d.representation e.representation) :
    hilbertEquiv d.representation e.representation
      ((gradedKasparovTensorAction (firstPairCycle c d Q hQ) e).action g u) =
    (gradedKasparovTensorAction c (secondPairCycle d e T hT)).action g
      (hilbertEquiv d.representation e.representation u) :=
  hilbertEquiv_action_intertwine d.representation e.representation c.groupAction d.groupAction e.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    (e.groupAction.representationEquivariant_of_conjugate e.representation_equivariant) g u

theorem triple_representation_intertwine (a : A)
    (u : LeftTensor (E := E) d.representation e.representation) :
    hilbertEquiv d.representation e.representation
      (gradedKasparovTensorRepresentation (firstPairCycle c d Q hQ) e a u) =
    gradedKasparovTensorRepresentation c (secondPairCycle d e T hT) a
      (hilbertEquiv d.representation e.representation u) :=
  hilbertEquiv_representation_intertwine d.representation e.representation c.representation a u

variable (R : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
  (RightTensor (E := E) d.representation e.representation))
  (hR : GradedKasparovTensorOperatorConditions c (secondPairCycle d e T hT) R)

include hR in
theorem rightTriple_tensorConditions_onLeft :
    GradedKasparovTensorOperatorConditions (firstPairCycle c d Q hQ) e
      ((hilbertEquiv d.representation e.representation).symm.transport R) := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let k := gradedKasparovTensorCycleOfConditions c (secondPairCycle d e T hT) R hR
  have hgrade (w : RightTensor (E := E) d.representation e.representation) :
      Ω.symm (k.grading.grading w) =
        (gradedKasparovTensorGrading (firstPairCycle c d Q hQ) e).grading (Ω.symm w) := by
    have h := triple_grading_intertwine c d e Q hQ T hT (Ω.symm w)
    have hc : k.grading.grading (Ω (Ω.symm w)) = k.grading.grading w :=
      congrArg (fun z : RightTensor (E := E) d.representation e.representation => k.grading.grading z)
        (Ω.apply_symm_apply w)
    have hf : Ω ((gradedKasparovTensorGrading (firstPairCycle c d Q hQ) e).grading (Ω.symm w)) = k.grading.grading w := h.trans hc
    exact (congrArg (fun z : RightTensor (E := E) d.representation e.representation => Ω.symm z) hf).symm.trans
      (Ω.symm_apply_apply _)
  have haction (g : Γ) (w : RightTensor (E := E) d.representation e.representation) :
      Ω.symm (k.groupAction.action g w) =
        (gradedKasparovTensorAction (firstPairCycle c d Q hQ) e).action g (Ω.symm w) := by
    have h := triple_action_intertwine c d e Q hQ T hT g (Ω.symm w)
    have hc : k.groupAction.action g (Ω (Ω.symm w)) = k.groupAction.action g w :=
      congrArg (fun z : RightTensor (E := E) d.representation e.representation => k.groupAction.action g z)
        (Ω.apply_symm_apply w)
    have hf : Ω ((gradedKasparovTensorAction (firstPairCycle c d Q hQ) e).action g (Ω.symm w)) = k.groupAction.action g w := h.trans hc
    exact (congrArg (fun z : RightTensor (E := E) d.representation e.representation => Ω.symm z) hf).symm.trans
      (Ω.symm_apply_apply _)
  have hrep (a : A) (w : RightTensor (E := E) d.representation e.representation) :
      Ω.symm (k.representation a w) =
        gradedKasparovTensorRepresentation (firstPairCycle c d Q hQ) e a (Ω.symm w) := by
    have h := triple_representation_intertwine c d e Q hQ T hT a (Ω.symm w)
    have hc : k.representation a (Ω (Ω.symm w)) = k.representation a w :=
      congrArg (fun z : RightTensor (E := E) d.representation e.representation => k.representation a z)
        (Ω.apply_symm_apply w)
    have hf : Ω (gradedKasparovTensorRepresentation (firstPairCycle c d Q hQ) e a (Ω.symm w)) = k.representation a w := h.trans hc
    exact (congrArg (fun z : RightTensor (E := E) d.representation e.representation => Ω.symm z) hf).symm.trans
      (Ω.symm_apply_apply _)
  exact transportedCycle_tensorConditions (firstPairCycle c d Q hQ) e k Ω.symm hgrade haction hrep

/-- Both original connection and adjoint connection laws survive the
actual completion and associator; the first-pair operator need not be used. -/
theorem rightTriple_connection_onLeft
    (hRconnection : GradedKasparovConnection c (secondPairCycle d e T hT) R)
    (hTconnection : GradedKasparovConnection d e T) :
    GradedKasparovConnection (firstPairCycle c d Q hQ) e
      ((hilbertEquiv d.representation e.representation).symm.transport R) := by
  have hRsigned : IsSignedModuleConnection c.grading
      (rightRepresentation d.representation e.representation) T R :=
    ⟨hRconnection.creation_defect, hRconnection.creation_adjoint_defect⟩
  have hTsigned : IsSignedModuleConnection d.grading e.representation e.operator T :=
    ⟨hTconnection.creation_defect, hTconnection.creation_adjoint_defect⟩
  have hcomp := composed_isSignedModuleConnection d.representation e.representation c.grading d.grading
    d.representation_graded R T e.operator hRsigned hTsigned
  exact hcomp.gradedKasparovConnection (firstPairCycle c d Q hQ) e

end BC4lean.KKTheory.KasparovTriple
