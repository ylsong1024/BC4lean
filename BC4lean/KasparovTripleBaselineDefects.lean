import BC4lean.KasparovTripleCycleData
import BC4lean.GradedConnectionDefectsWithFirstOperator
import BC4lean.KasparovTripleLocalAlgebra

/-! # Both creation localities of the actual baseline triple defects

The right iterated product's baseline technical defects are transported by
the actual associator. On the left they are the square, source and action
defects of the genuinely composed third connection, and the anticommutator
with the actual twice-lifted original first operator. The independent-operator
defect theorem therefore proves their first-pair locality as well as the
existing original-first locality. No positivity for the desired left product
is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open InteriorModuleTensorAssociator

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

set_option maxHeartbeats 1200000 in
theorem transport_productSecondDefectGeneratorsWithFirst
    {S : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)}
    (hS : S ∈ productSecondDefectGenerators c (secondPairCycle d e T hT) R) :
    (hilbertEquiv d.representation e.representation).symm.transport S ∈
      connectionDefectGeneratorsWithFirst (firstPairCycle c d Q hQ) e
        ((hilbertEquiv d.representation e.representation).symm.transport R)
        (interiorModuleTensorOperator d.representation c.operator) := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let UL : EquivariantHilbertModule χ (LeftTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorAction (firstPairCycle c d Q hQ) e
  let UR : EquivariantHilbertModule χ (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorAction c (secondPairCycle d e T hT)
  have hΩ (g : Γ) (u : LeftTensor (E := E) d.representation e.representation) :
      Ω (UL.action g u) = UR.action g (Ω u) :=
    triple_action_intertwine c d e Q hQ T hT g u
  have hop (O : AdjointableMap B E E) :
      Ω.symm.transport (interiorModuleTensorOperator (rightRepresentation d.representation e.representation) O) =
        interiorModuleTensorOperator e.representation (interiorModuleTensorOperator d.representation O) := by
    have h := congrArg Ω.symm.transport (hilbertEquiv_transport_operator d.representation e.representation O)
    exact h.symm.trans (Ω.transport_symm
      (interiorModuleTensorOperator e.representation (interiorModuleTensorOperator d.representation O)))
  have hact (g : Γ) : Ω.symm.transport (UR.conjugateOperator g R) =
      UL.conjugateOperator g (Ω.symm.transport R) := by
    apply Ω.transportStarAlgEquiv.injective
    change Ω.transport (Ω.symm.transport (UR.conjugateOperator g R)) =
      Ω.transport (UL.conjugateOperator g (Ω.symm.transport R))
    rw [HilbertModuleEquiv.transport_symm_symm,
      HilbertModuleEquiv.transport_conjugateAction Ω UL UR hΩ,
      HilbertModuleEquiv.transport_symm_symm]
  change S ∈ (({R * R - 1} ∪
    {interiorModuleTensorOperator (rightRepresentation d.representation e.representation) c.operator * R +
      R * interiorModuleTensorOperator (rightRepresentation d.representation e.representation) c.operator}) ∪
    Set.range (fun a : A =>
      R * interiorModuleTensorOperator (rightRepresentation d.representation e.representation) (c.representation a) -
        interiorModuleTensorOperator (rightRepresentation d.representation e.representation)
          (c.representation (δA.automorphism a)) * R)) ∪
    Set.range (fun g : Γ => UR.conjugateOperator g R - R) at hS
  change Ω.symm.transport S ∈ (({Ω.symm.transport R * Ω.symm.transport R - 1} ∪
    {interiorModuleTensorOperator e.representation (interiorModuleTensorOperator d.representation c.operator) *
        Ω.symm.transport R + Ω.symm.transport R *
          interiorModuleTensorOperator e.representation (interiorModuleTensorOperator d.representation c.operator)}) ∪
    Set.range (fun a : A => Ω.symm.transport R *
      interiorModuleTensorOperator e.representation (interiorModuleTensorOperator d.representation (c.representation a)) -
        interiorModuleTensorOperator e.representation
          (interiorModuleTensorOperator d.representation (c.representation (δA.automorphism a))) *
            Ω.symm.transport R)) ∪
    Set.range (fun g : Γ => UL.conjugateOperator g (Ω.symm.transport R) - Ω.symm.transport R)
  rcases hS with ((hS | hS) | hS) | hS
  · have h : S = R * R - 1 := hS
    rw [h, HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_one]
    exact Or.inl (Or.inl (Or.inl rfl))
  · have h : S = interiorModuleTensorOperator
        (rightRepresentation d.representation e.representation) c.operator * R +
        R * interiorModuleTensorOperator (rightRepresentation d.representation e.representation) c.operator := hS
    rw [h, HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_mul, hop]
    exact Or.inl (Or.inl (Or.inr rfl))
  · obtain ⟨a, rfl⟩ := hS
    rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_mul, hop, hop]
    exact Or.inl (Or.inr ⟨a, rfl⟩)
  · obtain ⟨g, rfl⟩ := hS
    rw [HilbertModuleEquiv.transport_sub, hact]
    exact Or.inr ⟨g, rfl⟩

include hQ in
/-- The baseline defect algebra's first-pair locality is derived using
the actual composed third connection and localized third-cycle defects. -/
theorem productSecondDefectAlgebra_pairCreationLocallyCompact
    (hRconnection : GradedKasparovConnection c (secondPairCycle d e T hT) R)
    (hTconnection : GradedKasparovConnection d e T)
    (hRsa : IsSelfAdjoint R) (hesa : IsSelfAdjoint e.operator) :
    ∀ S ∈ productSecondDefectAlgebra c (secondPairCycle d e T hT) R,
      IsCreationLocallyCompact e.representation
        ((hilbertEquiv d.representation e.representation).symm.transport S) := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let c₁₂ := firstPairCycle c d Q hQ
  let c₂₃ := secondPairCycle d e T hT
  let Rₗ := Ω.symm.transport R
  let O := interiorModuleTensorOperator d.representation c.operator
  have hleftConnection : GradedKasparovConnection c₁₂ e Rₗ :=
    rightTriple_connection_onLeft c d e Q hQ T hT R hRconnection hTconnection
  have hleftSA : IsSelfAdjoint Rₗ := by
    change star (Ω.symm.transport R) = _
    rw [← HilbertModuleEquiv.transport_star, hRsa.star_eq]
  have hOodd : c₁₂.grading.IsOdd c₁₂.grading O :=
    c.operator_odd.interiorModuleTensorOperator d.grading d.representation_graded
  let P : NonUnitalStarSubalgebra ℂ
      (AdjointableMap D (RightTensor (E := E) d.representation e.representation)
        (RightTensor (E := E) d.representation e.representation)) :=
    (creationLocallyCompactAlgebra (E := InteriorModuleTensor (E := E) d.representation)
      e.representation).comap Ω.symm.transportStarAlgEquiv.toNonUnitalStarAlgHom
  have hP : IsClosed (P : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) := by
    change IsClosed (Ω.symm.transportStarAlgEquiv ⁻¹'
      (creationLocallyCompactAlgebra (E := InteriorModuleTensor (E := E) d.representation)
        e.representation : Set (AdjointableMap D
          (LeftTensor (E := E) d.representation e.representation)
          (LeftTensor (E := E) d.representation e.representation))))
    exact (creationLocallyCompactAlgebra_isClosed
      (E := InteriorModuleTensor (E := E) d.representation) e.representation).preimage
        (StarAlgEquiv.isometry Ω.symm.transportStarAlgEquiv).continuous
  have hbase : ∀ S ∈ productSecondDefectGenerators c c₂₃ R, Ω.symm.transport S ∈
      creationLocallyCompactAlgebra e.representation := by
    intro S hS
    exact connectionDefectGeneratorsWithFirst_creationLocallyCompact c₁₂ e Rₗ O
      hesa hleftSA hleftConnection hOodd _
      (transport_productSecondDefectGeneratorsWithFirst c d e Q hQ T hT R hS)
  apply closedNonUnitalStarAdjoin_le _ P hP
  intro S hS
  rcases hS with hS | hS
  · exact hbase S hS
  · obtain ⟨V, hV, rfl⟩ := hS
    let V' : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
        (RightTensor (E := E) d.representation e.representation) := V
    let JL : GradedHilbertModule δD (LeftTensor (E := E) d.representation e.representation) :=
      gradedKasparovTensorGrading c₁₂ e
    let JR : GradedHilbertModule δD (RightTensor (E := E) d.representation e.representation) :=
      gradedKasparovTensorGrading c c₂₃
    have hΩ (u : LeftTensor (E := E) d.representation e.representation) :
        Ω (JL.grading u) = JR.grading (Ω u) :=
      triple_grading_intertwine c d e Q hQ T hT u
    have hconvert : Ω.symm.transport (JR.conjugateOperator V') =
        JL.conjugateOperator (Ω.symm.transport V') := by
      apply Ω.transportStarAlgEquiv.injective
      change Ω.transport (Ω.symm.transport (JR.conjugateOperator V')) =
        Ω.transport (JL.conjugateOperator (Ω.symm.transport V'))
      rw [HilbertModuleEquiv.transport_symm_symm,
        HilbertModuleEquiv.transport_conjugateGrading Ω JL JR hΩ]
      exact congrArg JR.conjugateOperator (Ω.transport_symm_symm V').symm
    change Ω.symm.transport (JR.conjugateOperator V') ∈
      creationLocallyCompactAlgebra e.representation
    rw [hconvert]
    exact grading_preserves_creationLocallyCompactAlgebra e.representation c₁₂.grading e.grading
      e.representation_graded (hbase V' hV)

end BC4lean.KKTheory.KasparovTriple
