import BC4lean.KasparovProductDefectAlgebra

/-! # Actual connection defects with an independent odd first operator

The first module's representation, grading and action determine the square,
source commutator and action defects of a genuine connection. The first
anticommutator calculation only needs an actual odd first operator. Keeping
that operator independent lets the triple argument use the twice-lifted
original first operator on the first-pair module, whose cycle operator is
instead the actual first-pair product.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter TopologicalSpace
open scoped Topology

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
  (G : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
  (O : AdjointableMap B E E)

def connectionDefectGeneratorsWithFirst : Set
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :=
  (({G * G - 1} ∪
    {interiorModuleTensorOperator d.representation O * G + G * interiorModuleTensorOperator d.representation O}) ∪
    Set.range (fun a : A => G * gradedKasparovTensorRepresentation c d a -
      gradedKasparovTensorRepresentation c d (δA.automorphism a) * G)) ∪
    Set.range (fun g : Γ => (gradedKasparovTensorAction c d).conjugateOperator g G - G)

def connectionDefectAlgebraWithFirst : NonUnitalStarSubalgebra ℂ
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :=
  closedNonUnitalStarAdjoin (connectionDefectGeneratorsWithFirst c d G O ∪
    (gradedKasparovTensorGrading c d).conjugateOperator '' connectionDefectGeneratorsWithFirst c d G O)

theorem connectionDefectAlgebraWithFirst_isClosed :
    IsClosed (connectionDefectAlgebraWithFirst c d G O : Set
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation))) := closedNonUnitalStarAdjoin_isClosed _

theorem connectionDefectGeneratorsWithFirst_creationLocallyCompact
    (hdsa : IsSelfAdjoint d.operator) (hGsa : IsSelfAdjoint G)
    (hG : GradedKasparovConnection c d G) (hO : c.grading.IsOdd c.grading O) :
    ∀ T ∈ connectionDefectGeneratorsWithFirst c d G O, IsCreationLocallyCompact d.representation T := by
  intro T hT
  rcases hT with ((hT | hT) | hT) | hT
  · have h : T = G * G - 1 := hT
    rw [h]
    exact hG.square_creation_locallyCompact hGsa hdsa
  · have h : T = interiorModuleTensorOperator d.representation O * G + G * interiorModuleTensorOperator d.representation O := hT
    rw [h]
    intro x
    constructor
    · exact oddTensorAnticommutator_comp_creation c.grading d.representation d.operator G
        hG.creation_defect O hO x
    · have heq : (interiorModuleTensorOperator d.representation O * G +
          G * interiorModuleTensorOperator d.representation O).adjoint =
          interiorModuleTensorOperator d.representation O.adjoint * G +
            G * interiorModuleTensorOperator d.representation O.adjoint := by
        change star (_ + _) = _
        simp only [star_add, star_mul, AdjointableMap.star_eq_adjoint,
          interiorModuleTensorOperator_adjoint, show G.adjoint = G from hGsa.star_eq]
        exact add_comm _ _
      rw [heq]
      exact oddTensorAnticommutator_comp_creation c.grading d.representation d.operator G
        hG.creation_defect O.adjoint hO.adjoint x
  · obtain ⟨a, rfl⟩ := hT
    exact hG.source_commutator_creation_locallyCompact hGsa a
  · obtain ⟨g, rfl⟩ := hT
    exact hG.action_defect_creation_locallyCompact hGsa hdsa g

theorem connectionDefectAlgebraWithFirst_creationLocallyCompact
    (hdsa : IsSelfAdjoint d.operator) (hGsa : IsSelfAdjoint G)
    (hG : GradedKasparovConnection c d G) (hO : c.grading.IsOdd c.grading O) :
    connectionDefectAlgebraWithFirst c d G O ≤ creationLocallyCompactAlgebra (E := E) d.representation := by
  apply closedNonUnitalStarAdjoin_le _ _ (creationLocallyCompactAlgebra_isClosed d.representation)
  intro T hT
  rcases hT with hT | hT
  · exact connectionDefectGeneratorsWithFirst_creationLocallyCompact c d G O hdsa hGsa hG hO T hT
  · obtain ⟨S, hS, rfl⟩ := hT
    exact grading_preserves_creationLocallyCompactAlgebra d.representation c.grading d.grading
      d.representation_graded
      (connectionDefectGeneratorsWithFirst_creationLocallyCompact c d G O hdsa hGsa hG hO S hS)

theorem connectionDefectAlgebraWithFirst_eq_productSecondDefectAlgebra :
    connectionDefectAlgebraWithFirst c d G c.operator = productSecondDefectAlgebra c d G := rfl

end BC4lean.KKTheory
