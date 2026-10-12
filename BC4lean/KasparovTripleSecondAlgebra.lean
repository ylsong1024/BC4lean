import BC4lean.KasparovTripleBaselineDefects

/-! # The actual second technical algebra for the common triple operator

The second algebra contains the right product's genuine baseline cycle
defects and the actual first-pair anticommutator's positive-part residual,
together with its grading image. Both creation localities are proved from
the supplied genuine product criteria. Separability and a countable actual
approximate unit are then derived from source separability and countability
of the acting group, without separability of all endomorphisms.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open Filter TopologicalSpace
open scoped Topology
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

local instance kasparovTripleSecondAlgebraLocalInstance1 : PartialOrder (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleSecondAlgebraLocalInstance2 : StarOrderedRing (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrderedRing _

def tripleResidual : AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation) :=
  tripleAnticommutator d.representation e.representation Q R -
    (tripleAnticommutator d.representation e.representation Q R)⁺

def secondGenerators : Set (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) :=
  let baseline : NonUnitalStarSubalgebra ℂ (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)) :=
    productSecondDefectAlgebra c (secondPairCycle d e T hT) R
  (baseline : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) ∪
    {tripleResidual d e Q R} ∪
    {(gradedKasparovTensorGrading c (secondPairCycle d e T hT)).conjugateOperator (tripleResidual d e Q R)}

def secondAlgebra : NonUnitalStarSubalgebra ℂ (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) :=
  closedNonUnitalStarAdjoin (secondGenerators c d e Q T hT R)

theorem secondAlgebra_isClosed : IsClosed (secondAlgebra c d e Q T hT R : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) :=
  closedNonUnitalStarAdjoin_isClosed _

theorem productSecondDefectAlgebra_le_secondAlgebra :
    productSecondDefectAlgebra c (secondPairCycle d e T hT) R ≤ secondAlgebra c d e Q T hT R :=
  fun _ h => subset_closedNonUnitalStarAdjoin _ (Or.inl (Or.inl h))

theorem tripleResidual_mem_secondAlgebra : tripleResidual d e Q R ∈ secondAlgebra c d e Q T hT R :=
  subset_closedNonUnitalStarAdjoin _ (Or.inl (Or.inr rfl))

theorem grading_preserves_secondAlgebra :
    ∀ S ∈ secondAlgebra c d e Q T hT R,
      (gradedKasparovTensorGrading c (secondPairCycle d e T hT)).conjugateOperator S ∈
        secondAlgebra c d e Q T hT R := by
  let J : GradedHilbertModule δD (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorGrading c (secondPairCycle d e T hT)
  apply maps_closedNonUnitalStarAdjoin _ J.conjugateOperatorStarAlgEquiv
  intro S hS
  change J.conjugateOperator S ∈ secondAlgebra c d e Q T hT R
  rcases hS with (hS | hS) | hS
  · exact productSecondDefectAlgebra_le_secondAlgebra c d e Q T hT R
      (grading_preserves_productSecondDefectAlgebra c (secondPairCycle d e T hT) R S hS)
  · have hs : S = tripleResidual d e Q R := hS
    rw [hs]
    exact subset_closedNonUnitalStarAdjoin _ (Or.inr rfl)
  · have hs : S = J.conjugateOperator (tripleResidual d e Q R) := hS
    rw [hs, J.conjugateOperator_involutive]
    exact tripleResidual_mem_secondAlgebra c d e Q T hT R

theorem secondAlgebra_isSeparable [SeparableSpace A] [Countable Γ] :
    IsSeparable (secondAlgebra c d e Q T hT R : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) := by
  let baseline : NonUnitalStarSubalgebra ℂ (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)) :=
    productSecondDefectAlgebra c (secondPairCycle d e T hT) R
  have hbaseline : IsSeparable (baseline : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) :=
    productSecondDefectAlgebra_isSeparable c (secondPairCycle d e T hT) R
  apply closedNonUnitalStarAdjoin_isSeparable
  exact (hbaseline.union
    (Set.finite_singleton (tripleResidual d e Q R)).isSeparable).union
      (Set.finite_singleton
        ((gradedKasparovTensorGrading c (secondPairCycle d e T hT)).conjugateOperator
          (tripleResidual d e Q R))).isSeparable

theorem exists_secondAlgebra_approximateUnit [SeparableSpace A] [Countable Γ] :
    ∃ q : ℕ → secondAlgebra c d e Q T hT R,
      (∀ S, Tendsto (fun n => S * q n) atTop (𝓝 S)) ∧
      (∀ S, Tendsto (fun n => q n * S) atTop (𝓝 S)) := by
  let : IsClosed (secondAlgebra c d e Q T hT R : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) := secondAlgebra_isClosed c d e Q T hT R
  let : SeparableSpace (secondAlgebra c d e Q T hT R) :=
    (secondAlgebra_isSeparable c d e Q T hT R).separableSpace
  let : PartialOrder (secondAlgebra c d e Q T hT R) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (secondAlgebra c d e Q T hT R) := CStarAlgebra.spectralOrderedRing _
  obtain ⟨q, _, _, _, _, _, hleft, hright⟩ :=
    exists_separable_increasing_approximateUnit (J := secondAlgebra c d e Q T hT R)
  exact ⟨q, hleft, hright⟩

include hQ in
/-- Every actual second-algebra element has both concrete creation
localities, from the original genuine product witnesses. -/
theorem secondAlgebra_creation_localities
    (hQproduct : IsGradedKasparovProductOperator c d Q)
    (hTproduct : IsGradedKasparovProductOperator d e T)
    (hRconnection : GradedKasparovConnection c (secondPairCycle d e T hT) R)
    (hQsa : IsSelfAdjoint Q) (hdsa : IsSelfAdjoint d.operator)
    (hTsa : IsSelfAdjoint T) (hRsa : IsSelfAdjoint R) (hesa : IsSelfAdjoint e.operator) :
    ∀ S ∈ secondAlgebra c d e Q T hT R,
      IsCreationLocallyCompact (rightRepresentation d.representation e.representation) S ∧
      IsCreationLocallyCompact e.representation
        ((hilbertEquiv d.representation e.representation).symm.transport S) := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let c₁₂ := firstPairCycle c d Q hQ
  let c₂₃ := secondPairCycle d e T hT
  let JL : GradedHilbertModule δD (LeftTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorGrading c₁₂ e
  let JR : GradedHilbertModule δD (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorGrading c c₂₃
  have hΩ (u : LeftTensor (E := E) d.representation e.representation) :
      Ω (JL.grading u) = JR.grading (Ω u) :=
    triple_grading_intertwine c d e Q hQ T hT u
  let P : NonUnitalStarSubalgebra ℂ (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)) :=
    (bothCreationLocalAlgebra (E := E) d.representation e.representation).comap
      Ω.symm.transportStarAlgEquiv.toNonUnitalStarAlgHom
  have hP : IsClosed (P : Set (AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))) := by
    change IsClosed (Ω.symm.transportStarAlgEquiv ⁻¹'
      (bothCreationLocalAlgebra (E := E) d.representation e.representation :
        Set (AdjointableMap D
          (LeftTensor (E := E) d.representation e.representation)
          (LeftTensor (E := E) d.representation e.representation))))
    exact (bothCreationLocalAlgebra_isClosed (E := E) d.representation e.representation).preimage
      (StarAlgEquiv.isometry Ω.symm.transportStarAlgEquiv).continuous
  have hPiff (S : AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation)) :
      S ∈ P ↔
        IsCreationLocallyCompact (rightRepresentation d.representation e.representation) S ∧
        IsCreationLocallyCompact e.representation (Ω.symm.transport S) := by
    change (IsCreationLocallyCompact (rightRepresentation d.representation e.representation)
      (Ω.transport (Ω.symm.transport S)) ∧
      IsCreationLocallyCompact e.representation (Ω.symm.transport S)) ↔ _
    rw [Ω.transport_symm_symm S]
  have hbase (S : AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation))
      (hS : S ∈ productSecondDefectAlgebra c c₂₃ R) : S ∈ P := by
    apply (hPiff S).mpr
    constructor
    · exact productSecondDefectAlgebra_creationLocallyCompact c c₂₃ R hTsa hRsa hRconnection S hS
    · exact productSecondDefectAlgebra_pairCreationLocallyCompact c d e Q hQ T hT R
        hRconnection hTproduct.connection hRsa hesa S hS
  have hrawQ : IsSignedModuleConnection c.grading d.representation d.operator Q :=
    ⟨hQproduct.connection.creation_defect, hQproduct.connection.creation_adjoint_defect⟩
  have hrawT : IsSignedModuleConnection d.grading e.representation e.operator T :=
    ⟨hTproduct.connection.creation_defect, hTproduct.connection.creation_adjoint_defect⟩
  have hrawR : IsSignedModuleConnection c.grading (rightRepresentation d.representation e.representation) T R :=
    ⟨hRconnection.creation_defect, hRconnection.creation_adjoint_defect⟩
  let V : AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := tripleResidual d e Q R
  have hresid : V ∈ P := by
    apply (hPiff V).mpr
    exact residual_creation_localities d.representation e.representation c.grading d.grading
      d.representation_graded Q d.operator R T e.operator hrawQ hrawR hrawT
      hQproduct.cycleConditions.operator_odd d.operator_odd hQsa hdsa hRsa hTsa
      d.commutator_compact hTproduct.cycleConditions.commutator_compact hTproduct.positivity
  have hresidLocal := (hPiff V).mp hresid
  have hgradedResid : JR.conjugateOperator V ∈ P := by
    apply (hPiff (JR.conjugateOperator V)).mpr
    constructor
    · exact grading_preserves_creationLocallyCompactAlgebra (rightRepresentation d.representation e.representation)
        c.grading c₂₃.grading c₂₃.representation_graded hresidLocal.1
    · have heq : Ω.symm.transport (JR.conjugateOperator V) =
          JL.conjugateOperator (Ω.symm.transport V) := by
        apply Ω.transportStarAlgEquiv.injective
        change Ω.transport (Ω.symm.transport (JR.conjugateOperator V)) =
          Ω.transport (JL.conjugateOperator (Ω.symm.transport V))
        rw [HilbertModuleEquiv.transport_symm_symm,
          HilbertModuleEquiv.transport_conjugateGrading Ω JL JR hΩ]
        exact congrArg JR.conjugateOperator (Ω.transport_symm_symm V).symm
      rw [heq]
      exact grading_preserves_creationLocallyCompactAlgebra e.representation c₁₂.grading e.grading
        e.representation_graded hresidLocal.2
  have hle : secondAlgebra c d e Q T hT R ≤ P := by
    apply closedNonUnitalStarAdjoin_le _ P hP
    intro S hS
    rcases hS with (hS | hS) | hS
    · exact hbase S hS
    · have hs : S = V := hS
      subst S
      exact hresid
    · have hs : S = JR.conjugateOperator V := hS
      subst S
      exact hgradedResid
  intro S hS
  exact (hPiff S).mp (hle hS)

end BC4lean.KKTheory.KasparovTriple
