import BC4lean.KasparovTripleWeightedProduct
import BC4lean.KasparovTripleNormalizerDerivation
import BC4lean.KasparovTripleRightFirstAlgebra
import BC4lean.KasparovDiscreteTechnicalTheorem

/-! # A constructed common product on both associations

The original first compact approximate unit is transported to the right
triple. Every first-algebra, second-algebra and normalizer hypothesis of the
technical theorem is derived from the actual input cycles and the actual
three supplied products. The resulting weighted operator meets both complete
product criteria; this source assumes no common operator or associativity.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open Filter TopologicalSpace
open scoped Topology
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
  (R : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation))


local instance kasparovTripleTechnicalConstructionLocalInstance1 : PartialOrder (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleTechnicalConstructionLocalInstance2 : StarOrderedRing (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrderedRing _

set_option maxHeartbeats 2000000 in
/-- An actual common weighted operator is constructed by the technical
partition, with both full genuine product criteria. The adjoint assumptions
are used only by the analytic construction and will be removed by full
normalization and the independently constructed input descent. -/
theorem exists_actualCommonTripleProduct
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [SeparableSpace D] [Countable Γ]
    (hQproduct : IsGradedKasparovProductOperator c d Q)
    (hTproduct : IsGradedKasparovProductOperator d e T)
    (hRproduct : IsGradedKasparovProductOperator c (secondPairCycle d e T hT) R)
    (hcsa : IsSelfAdjoint c.operator) (hdsa : IsSelfAdjoint d.operator)
    (hesa : IsSelfAdjoint e.operator) (hQsa : IsSelfAdjoint Q)
    (hTsa : IsSelfAdjoint T) (hRsa : IsSelfAdjoint R) :
    ∃ P : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation),
      IsGradedKasparovProductOperator c (secondPairCycle d e T hT) P ∧
      IsGradedKasparovProductOperator (firstPairCycle c d Q hQ) e
        ((hilbertEquiv d.representation e.representation).symm.transport P) := by
  classical
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let c₁₂ := firstPairCycle c d Q hQ
  let c₂₃ := secondPairCycle d e T hT
  let JL : GradedHilbertModule δD
      (LeftTensor (E := E) d.representation e.representation) := gradedKasparovTensorGrading c₁₂ e
  let JR : GradedHilbertModule δD
      (RightTensor (E := E) d.representation e.representation) := gradedKasparovTensorGrading c c₂₃
  let UL : EquivariantHilbertModule χ
      (LeftTensor (E := E) d.representation e.representation) := gradedKasparovTensorAction c₁₂ e
  let UR : EquivariantHilbertModule χ
      (RightTensor (E := E) d.representation e.representation) := gradedKasparovTensorAction c c₂₃
  let L₁ := normalizerFirstAlgebra (E := E) d.representation e.representation d.operator e.operator T
  let E₁ := rightCoordinateFirstAlgebra (E := E) d.representation e.representation d.operator e.operator T
  let E₂ := secondAlgebra c d e Q T hT R
  let Δ : Set (AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)) :=
    productNormalizerTests c c₂₃ R ∪ {pairLift d.representation e.representation Q}
  let f : ℕ → AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := fun _ => 0
  let : IsClosed (E₁ : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) := rightCoordinateFirstAlgebra_isClosed (E := E)
    d.representation e.representation d.operator e.operator T
  let : IsClosed (E₂ : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) := secondAlgebra_isClosed c d e Q T hT R
  obtain ⟨q₁, hq₁left, hq₁right⟩ := exists_rightCoordinateFirstAlgebra_approximateUnit
    d.representation e.representation d.operator e.operator T c.countablyGenerated
  obtain ⟨q₂, hq₂left, hq₂right⟩ := exists_secondAlgebra_approximateUnit c d e Q T hT R
  have hboth : ∀ b ∈ E₂,
      IsCreationLocallyCompact (E := E)
        (rightRepresentation d.representation e.representation) b ∧
      IsCreationLocallyCompact (E := InteriorModuleTensor (E := E) d.representation)
        e.representation (Ω.symm.transport b) :=
    secondAlgebra_creation_localities c d e Q hQ T hT R hQproduct hTproduct
      hRproduct.connection hQsa hdsa hTsa hRsa hesa
  have hideals : ∀ a ∈ E₁, ∀ b ∈ E₂, IsModuleCompact (a * b) := by
    intro a ha b hb
    apply (Ω.symm.transport_isModuleCompact_iff _).mp
    rw [HilbertModuleEquiv.transport_mul]
    have hbBoth : Ω.symm.transport b ∈
        bothCreationLocalAlgebra (E := E) d.representation e.representation := by
      change IsCreationLocallyCompact (E := E)
          (rightRepresentation d.representation e.representation)
          (Ω.transport (Ω.symm.transport b)) ∧
        IsCreationLocallyCompact (E := InteriorModuleTensor (E := E) d.representation)
          e.representation (Ω.symm.transport b)
      rw [Ω.transport_symm_symm b]
      exact hboth b hb
    have haLeft : Ω.symm.transport a ∈ L₁ :=
      (mem_rightCoordinateFirstAlgebra (E := E) d.representation e.representation
        d.operator e.operator T a).mp ha
    exact (normalizerFirstAlgebra_products_compact (E := E)
      d.representation e.representation d.operator e.operator T
      (L := Ω.symm.transport a) (T := Ω.symm.transport b) haLeft hbBoth).1
  have hgradeL : ∀ a ∈ L₁, JL.conjugateOperator a ∈ L₁ :=
    grading_preserves_normalizerFirstAlgebra d.representation e.representation
      c.grading d.grading e.grading d.representation_graded e.representation_graded
      d.operator d.operator_odd e.operator e.operator_odd T hTproduct.cycleConditions.operator_odd
  have hactionBase := action_preserves_enlargedFirstAlgebra_of_firstProduct_controls
    d.representation e.representation e.operator T UL UR
      (triple_action_intertwine c d e Q hQ T hT)
      (action_preserves_firstProductAlgebra c₁₂ e hesa)
      (action_preserves_firstProductAlgebra c c₂₃ hTsa)
  have hactionL : ∀ g a, a ∈ L₁ → UL.conjugateOperator g a ∈ L₁ :=
    action_preserves_normalizerFirstAlgebra_of_pair_controls d.representation e.representation
      d.operator e.operator T c₁₂.groupAction e.groupAction
      (e.groupAction.representationEquivariant_of_conjugate e.representation_equivariant)
      (action_preserves_firstProductAlgebra c d hdsa) hactionBase
  have hE₁action : ∀ g a, a ∈ E₁ → UR.conjugateOperator g a ∈ E₁ :=
    action_preserves_rightCoordinateFirstAlgebra d.representation e.representation
      d.operator e.operator T UL UR (triple_action_intertwine c d e Q hQ T hT) hactionL
  have hE₁grade : ∀ a ∈ E₁, JR.conjugateOperator a ∈ E₁ :=
    grading_preserves_rightCoordinateFirstAlgebra d.representation e.representation
      d.operator e.operator T JL JR (triple_grading_intertwine c d e Q hQ T hT) hgradeL
  have hnormal : ∀ (X : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)), X ∈ Δ →
      ∀ (a : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)), a ∈ E₁ →
        X * a - a * X ∈ E₁ := by
    intro X hX
    have hleft : ∀ (b : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
        (LeftTensor (E := E) d.representation e.representation)), b ∈ L₁ →
        Ω.symm.transport X * b - b * Ω.symm.transport X ∈ L₁ := by
      rcases hX with hX | hX
      · rcases hX with (hX | hX) | hX
        · have hXeq : X = interiorModuleTensorOperator c₂₃.representation c.operator := hX
          rw [hXeq]
          have hfirst : Ω.symm.transport (interiorModuleTensorOperator c₂₃.representation c.operator) =
              doubleTensorOperator d.representation e.representation c.operator := by
            change Ω.symm.transport (interiorModuleTensorOperator
                (rightRepresentation d.representation e.representation) c.operator) =
              interiorModuleTensorOperator e.representation
                (interiorModuleTensorOperator d.representation c.operator)
            have h := congrArg Ω.symm.transport
              (hilbertEquiv_transport_operator d.representation e.representation c.operator)
            exact h.symm.trans (Ω.transport_symm
              (interiorModuleTensorOperator e.representation
                (interiorModuleTensorOperator d.representation c.operator)))
          rw [hfirst]
          exact doubleTensorOperator_normalizes_normalizerFirstAlgebra (E := E) d.representation e.representation
            d.operator e.operator T c.countablyGenerated c.operator
        · have hXeq : X = R := hX
          rw [hXeq]
          exact rightConnection_normalizes_normalizerFirstAlgebra (E := E) d.representation e.representation
            d.operator e.operator T c.countablyGenerated c.grading R
              ⟨hRproduct.connection.creation_defect, hRproduct.connection.creation_adjoint_defect⟩ hTsa
        · obtain ⟨a, rfl⟩ := hX
          have hfirst : Ω.symm.transport (gradedKasparovTensorRepresentation c c₂₃ a) =
              doubleTensorOperator d.representation e.representation (c.representation a) := by
            change Ω.symm.transport (interiorModuleTensorOperator
                (rightRepresentation d.representation e.representation) (c.representation a)) =
              interiorModuleTensorOperator e.representation
                (interiorModuleTensorOperator d.representation (c.representation a))
            have h := congrArg Ω.symm.transport
              (hilbertEquiv_transport_operator d.representation e.representation (c.representation a))
            exact h.symm.trans (Ω.transport_symm
              (interiorModuleTensorOperator e.representation
                (interiorModuleTensorOperator d.representation (c.representation a))))
          rw [hfirst]
          exact doubleTensorOperator_normalizes_normalizerFirstAlgebra (E := E) d.representation e.representation
            d.operator e.operator T c.countablyGenerated (c.representation a)
      · have hXeq : X = pairLift d.representation e.representation Q := hX
        rw [hXeq]
        have hlift : Ω.symm.transport (pairLift d.representation e.representation Q) =
            interiorModuleTensorOperator e.representation Q := by
          change Ω.symm.transport (Ω.transport (interiorModuleTensorOperator e.representation Q)) =
            interiorModuleTensorOperator e.representation Q
          exact Ω.transport_symm _
        rw [hlift]
        exact pairTensorConnection_normalizes_normalizerFirstAlgebra (E := E) d.representation e.representation
          d.operator e.operator T c.countablyGenerated c.grading Q
            ⟨hQproduct.connection.creation_defect, hQproduct.connection.creation_adjoint_defect⟩ hdsa
    exact normalizes_rightCoordinateFirstAlgebra (E := E) d.representation e.representation
      d.operator e.operator T X hleft
  have hSecondCountablyGenerated : IsCountablyGeneratedModule D
      (InteriorModuleTensor (E := F) e.representation) :=
    d.countablyGenerated.interiorTensor e.countablyGenerated e.representation
  have hRightCountablyGenerated : IsCountablyGeneratedModule D
      (RightTensor (E := E) d.representation e.representation) :=
    c.countablyGenerated.interiorTensor hSecondCountablyGenerated
      (rightRepresentation d.representation e.representation)
  have hZeroFamily : ∀ k (a : AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)), a ∈ E₁ →
      IsModuleCompact (a * f k) ∧ IsModuleCompact (f k * a) := by
    intro k a _
    dsimp only [f]
    simpa only [mul_zero, zero_mul] using!
      (show IsModuleCompact (0 : AdjointableMap D
          (RightTensor (E := E) d.representation e.representation)
          (RightTensor (E := E) d.representation e.representation)) ∧
        IsModuleCompact (0 : AdjointableMap D
          (RightTensor (E := E) d.representation e.representation)
          (RightTensor (E := E) d.representation e.representation)) from
        ⟨IsModuleCompact.zero, IsModuleCompact.zero⟩)
  obtain ⟨p⟩ := exists_kasparovDiscreteTechnicalPartition
    (B := D) (E := RightTensor (E := E) d.representation e.representation)
    (β := δD) (α := χ)
    hRightCountablyGenerated
    JR UR (gradedKasparovTensorAction_preservesGrading c c₂₃) E₁ E₂ q₁ q₂
    hq₁left hq₁right hq₂left hq₂right hideals hE₁action hE₁grade
    (grading_preserves_secondAlgebra c d e Q T hT R)
    Δ ((productNormalizerTests_isSeparable c c₂₃ R).union
      (Set.finite_singleton (pairLift d.representation e.representation Q)).isSeparable) hnormal
    f ⟨0, fun _ => by
      change ‖(0 : AdjointableMap D
        (RightTensor (E := E) d.representation e.representation)
        (RightTensor (E := E) d.representation e.representation))‖ ≤ 0
      exact le_of_eq (norm_zero)⟩
    hZeroFamily
  have hfirstBase : firstProductAlgebra c₂₃.representation c₂₃.operator ≤ E₁ :=
    firstProductAlgebra_le_rightCoordinateFirstAlgebra d.representation e.representation
      d.operator e.operator T
  have hsecondBase := productSecondDefectAlgebra_le_secondAlgebra c d e Q T hT R
  have hb := actualKasparovProductTechnicalInputs c c₂₃ R
  have inputs : KasparovProductTechnicalInputs c c₂₃ R E₁ E₂ Δ := {
    first_mem := Or.inl hb.first_mem
    connection_mem := Or.inl hb.connection_mem
    representation_mem a := Or.inl (hb.representation_mem a)
    creation_square_mem x := hfirstBase (hb.creation_square_mem x)
    first_square_mem a := hfirstBase (hb.first_square_mem a)
    first_commutator_mem a := hfirstBase (hb.first_commutator_mem a)
    first_equivariance_mem g a := hfirstBase (hb.first_equivariance_mem g a)
    second_square_mem := hsecondBase hb.second_square_mem
    second_commutator_mem a := hsecondBase (hb.second_commutator_mem a)
    second_equivariance_mem g := hsecondBase (hb.second_equivariance_mem g)
    anticommutator_mem := hsecondBase hb.anticommutator_mem }
  have hpair : ∀ K : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation), IsModuleCompact K →
        Ω.transport (interiorModuleTensorOperator e.representation K) ∈ E₁ := by
    intro K hK
    exact pairTensorCompact_mem_rightCoordinateFirstAlgebra d.representation e.representation
      d.operator e.operator T hK
  have hthird : ∀ u : InteriorModuleTensor (E := E) d.representation,
      Ω.transport ((moduleCreationMap e.representation u).comp
        (moduleCreationMap e.representation u).adjoint) ∈ E₁ := by
    intro u
    exact thirdCreationSquare_mem_rightCoordinateFirstAlgebra d.representation e.representation
      d.operator e.operator T u
  let P : AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    kasparovTechnicalProductOperator (c := c) (d := c₂₃) R p
  have hP : IsGradedKasparovProductOperator c c₂₃ P ∧
      IsGradedKasparovProductOperator c₁₂ e (Ω.symm.transport P) :=
    weighted_operator_isProduct_onBothSides
      (Γ := Γ) (A := A) (B := B) (C := C) (D := D) (E := E) (F := F) (G := G)
      (α := α) (β := β) (γ := γ) (χ := χ)
      (δA := δA) (δB := δB) (δC := δC) (δD := δD)
      (E₁ := E₁) (E₂ := E₂) (Δ := Δ) (f := f)
      c d e Q hQ T hT R p inputs hQproduct hTproduct
      hcsa hQsa hRsa hesa hRproduct.cycleConditions.operator_odd hRproduct.connection
      (Or.inr rfl) (tripleResidual_mem_secondAlgebra c d e Q T hT R) hpair hthird
  exact ⟨P, hP⟩

end BC4lean.KKTheory.KasparovTriple
