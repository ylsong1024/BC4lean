import BC4lean.KasparovComparisonPositivity

/-! # Constructing an actual common positive comparison product

The genuine discrete technical theorem is applied to a concrete enlarged
creation-local defect algebra for two given product operators. Its genuine
countable AU is constructed from separability, and every extra normalizer
condition follows from an actual connection. The result is an actual
product with positive localized anticommutators against both products.
This comparison result does not assert a homotopy.
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
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
  (G R₀ R₁ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))

def productComparisonDefectSources : Set
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :=
  ((productSecondDefectAlgebra c d G : Set _) ∪ {R₀ * G + G * R₀ - 2}) ∪
    {R₁ * G + G * R₁ - 2}

def productComparisonDefectAlgebra : NonUnitalStarSubalgebra ℂ
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :=
  closedNonUnitalStarAdjoin (productComparisonDefectSources c d G R₀ R₁ ∪
    (gradedKasparovTensorGrading c d).conjugateOperator ''
      productComparisonDefectSources c d G R₀ R₁)

theorem productComparisonDefectAlgebra_isClosed :
    IsClosed (productComparisonDefectAlgebra c d G R₀ R₁ : Set
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation))) :=
  closedNonUnitalStarAdjoin_isClosed _

theorem productSecondDefectAlgebra_le_comparison :
    productSecondDefectAlgebra c d G ≤ productComparisonDefectAlgebra c d G R₀ R₁ :=
  fun _ hT => subset_closedNonUnitalStarAdjoin _ (Or.inl (Or.inl (Or.inl hT)))

theorem comparisonDefect_zero_mem :
    R₀ * G + G * R₀ - 2 ∈ productComparisonDefectAlgebra c d G R₀ R₁ :=
  subset_closedNonUnitalStarAdjoin _ (Or.inl (Or.inl (Or.inr rfl)))

theorem comparisonDefect_one_mem :
    R₁ * G + G * R₁ - 2 ∈ productComparisonDefectAlgebra c d G R₀ R₁ :=
  subset_closedNonUnitalStarAdjoin _ (Or.inl (Or.inr rfl))

theorem productComparisonDefectAlgebra_creationLocallyCompact
    (hdsa : IsSelfAdjoint d.operator) (hGsa : IsSelfAdjoint G)
    (hG : GradedKasparovConnection c d G)
    (hR₀ : GradedKasparovConnection c d R₀) (hR₁ : GradedKasparovConnection c d R₁) :
    productComparisonDefectAlgebra c d G R₀ R₁ ≤
      creationLocallyCompactAlgebra (E := E) d.representation := by
  have hs : ∀ T ∈ productComparisonDefectSources c d G R₀ R₁,
      IsCreationLocallyCompact d.representation T := by
    intro T hT
    rcases hT with (hT | hT) | hT
    · exact productSecondDefectAlgebra_creationLocallyCompact c d G hdsa hGsa hG T hT
    · have heq : T = R₀ * G + G * R₀ - 2 := hT
      rw [heq]
      exact hR₀.comparison_anticommutator_creationLocallyCompact hG hGsa hdsa
    · have heq : T = R₁ * G + G * R₁ - 2 := hT
      rw [heq]
      exact hR₁.comparison_anticommutator_creationLocallyCompact hG hGsa hdsa
  apply closedNonUnitalStarAdjoin_le _ _ (creationLocallyCompactAlgebra_isClosed d.representation)
  intro T hT
  rcases hT with hT | hT
  · exact hs T hT
  · obtain ⟨S, hS, rfl⟩ := hT
    exact grading_preserves_creationLocallyCompactAlgebra d.representation
      c.grading d.grading d.representation_graded (hs S hS)

theorem grading_preserves_productComparisonDefectAlgebra :
    ∀ T ∈ productComparisonDefectAlgebra c d G R₀ R₁,
      (gradedKasparovTensorGrading c d).conjugateOperator T ∈
        productComparisonDefectAlgebra c d G R₀ R₁ := by
  let J := gradedKasparovTensorGrading c d
  apply maps_closedNonUnitalStarAdjoin _ J.conjugateOperatorStarAlgEquiv
  intro T hT
  rcases hT with hT | hT
  · exact subset_closedNonUnitalStarAdjoin _ (Or.inr ⟨T, hT, rfl⟩)
  · obtain ⟨S, hS, rfl⟩ := hT
    change J.conjugateOperator (J.conjugateOperator S) ∈ _
    rw [J.conjugateOperator_involutive]
    exact subset_closedNonUnitalStarAdjoin _ (Or.inl hS)

theorem productComparisonDefectAlgebra_isSeparable [SeparableSpace A] [Countable Γ] :
    IsSeparable (productComparisonDefectAlgebra c d G R₀ R₁ : Set
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation))) := by
  have hs : IsSeparable (productComparisonDefectSources c d G R₀ R₁) :=
    ((productSecondDefectAlgebra_isSeparable c d G).union
      (Set.finite_singleton (R₀ * G + G * R₀ - 2)).isSeparable).union
      (Set.finite_singleton (R₁ * G + G * R₁ - 2)).isSeparable
  exact closedNonUnitalStarAdjoin_isSeparable _
    (hs.union (hs.image (StarAlgEquiv.isometry ((gradedKasparovTensorGrading c d).conjugateOperatorStarAlgEquiv)).continuous))

theorem exists_productComparisonDefectAlgebra_approximateUnit
    [SeparableSpace A] [Countable Γ] :
    ∃ q : ℕ → productComparisonDefectAlgebra c d G R₀ R₁,
      (∀ a, Tendsto (fun n => a * q n) atTop (𝓝 a)) ∧
        (∀ a, Tendsto (fun n => q n * a) atTop (𝓝 a)) := by
  let : IsClosed (productComparisonDefectAlgebra c d G R₀ R₁ : Set
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation))) :=
    productComparisonDefectAlgebra_isClosed c d G R₀ R₁
  let : SeparableSpace (productComparisonDefectAlgebra c d G R₀ R₁) :=
    (productComparisonDefectAlgebra_isSeparable c d G R₀ R₁).separableSpace
  let : PartialOrder (productComparisonDefectAlgebra c d G R₀ R₁) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (productComparisonDefectAlgebra c d G R₀ R₁) :=
    CStarAlgebra.spectralOrderedRing _
  obtain ⟨q, _, _, _, _, _, hleft, hright⟩ :=
    exists_separable_increasing_approximateUnit (J := productComparisonDefectAlgebra c d G R₀ R₁)
  exact ⟨q, hleft, hright⟩

def productComparisonNormalizerTests : Set
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :=
  (productNormalizerTests c d G ∪ {R₀}) ∪ {R₁}

theorem productComparisonNormalizerTests_isSeparable [SeparableSpace A] :
    IsSeparable (productComparisonNormalizerTests c d G R₀ R₁) :=
  ((productNormalizerTests_isSeparable c d G).union (Set.finite_singleton R₀).isSeparable).union
    (Set.finite_singleton R₁).isSeparable

theorem productComparisonNormalizerTests_normalize_firstProductAlgebra
    (hdsa : IsSelfAdjoint d.operator) (hGsa : IsSelfAdjoint G)
    (hR₀sa : IsSelfAdjoint R₀) (hR₁sa : IsSelfAdjoint R₁)
    (hG : GradedKasparovConnection c d G)
    (hR₀ : GradedKasparovConnection c d R₀) (hR₁ : GradedKasparovConnection c d R₁) :
    ∀ T ∈ productComparisonNormalizerTests c d G R₀ R₁,
      ∀ a ∈ firstProductAlgebra d.representation d.operator,
        T * a - a * T ∈ firstProductAlgebra d.representation d.operator := by
  intro T hT
  rcases hT with (hT | hT) | hT
  · exact productNormalizerTests_normalize_firstProductAlgebra c d G hdsa hGsa hG T hT
  · have heq : T = R₀ := hT
    rw [heq]
    exact hR₀.normalizes_firstProductAlgebra hR₀sa hdsa
  · have heq : T = R₁ := hT
    rw [heq]
    exact hR₁.normalizes_firstProductAlgebra hR₁sa hdsa

/-- This constructs the common comparison operator by the genuine
discrete technical theorem. The given products supply comparison
positivity; they do not supply the technical partition or a homotopy. -/
theorem exists_actualCommonPositiveComparisonProduct
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (hcsa : IsSelfAdjoint c.operator) (hdsa : IsSelfAdjoint d.operator)
    (hdnorm : ‖d.operator‖ ≤ 1)
    (hR₀sa : IsSelfAdjoint R₀) (hR₁sa : IsSelfAdjoint R₁)
    (hR₀ : IsGradedKasparovProductOperator c d R₀)
    (hR₁ : IsGradedKasparovProductOperator c d R₁) :
    ∃ P : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation),
      IsGradedKasparovProductOperator c d P ∧
      (∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
        (R₀ * P + P * R₀) * star (gradedKasparovTensorRepresentation c d a))) ∧
      (∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
        (R₁ * P + P * R₁) * star (gradedKasparovTensorRepresentation c d a))) := by
  classical
  obtain ⟨G, hGodd, hGsa, _, hG⟩ :=
    exists_odd_selfadjoint_contractive_gradedKasparovConnection c d hdsa hdnorm
  let E₁ := firstProductAlgebra (E := E) d.representation d.operator
  let E₂ := productComparisonDefectAlgebra c d G R₀ R₁
  let Δ := productComparisonNormalizerTests c d G R₀ R₁
  let f : ℕ → AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) := fun _ => 0
  let J := gradedKasparovTensorGrading c d
  let U := gradedKasparovTensorAction c d
  let : IsClosed (E₁ : Set
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation))) := firstProductAlgebra_isClosed (E := E) _ _
  let : IsClosed (E₂ : Set
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation))) := productComparisonDefectAlgebra_isClosed _ _ _ _ _
  obtain ⟨q₁, hq₁left, hq₁right⟩ :=
    exists_firstProductAlgebra_approximateUnit d.representation d.operator c.countablyGenerated
  obtain ⟨q₂, hq₂left, hq₂right⟩ :=
    exists_productComparisonDefectAlgebra_approximateUnit c d G R₀ R₁
  have h₂local : E₂ ≤ creationLocallyCompactAlgebra (E := E) d.representation :=
    productComparisonDefectAlgebra_creationLocallyCompact c d G R₀ R₁ hdsa hGsa hG
      hR₀.connection hR₁.connection
  obtain ⟨p⟩ := exists_kasparovDiscreteTechnicalPartition
    (c.countablyGenerated.interiorTensor d.countablyGenerated d.representation)
    J U (gradedKasparovTensorAction_preservesGrading c d) E₁ E₂ q₁ q₂
    hq₁left hq₁right hq₂left hq₂right
    (fun a ha b hb => (firstProductAlgebra_products_compact d.representation d.operator ha (h₂local hb)).1)
    (action_preserves_firstProductAlgebra c d hdsa)
    (grading_preserves_firstProductAlgebra d.representation c.grading d.grading
      d.representation_graded d.operator d.operator_odd)
    (grading_preserves_productComparisonDefectAlgebra c d G R₀ R₁)
    Δ (productComparisonNormalizerTests_isSeparable c d G R₀ R₁)
    (productComparisonNormalizerTests_normalize_firstProductAlgebra c d G R₀ R₁
      hdsa hGsa hR₀sa hR₁sa hG hR₀.connection hR₁.connection)
    f ⟨0, fun _ => by simp [f]⟩
    (fun _ a _ => by
      change IsModuleCompact (a * 0) ∧ IsModuleCompact (0 * a)
      rw [mul_zero, zero_mul]
      exact ⟨IsModuleCompact.zero, IsModuleCompact.zero⟩)
  have hb := actualKasparovProductTechnicalInputs c d G
  have h₂base : productSecondDefectAlgebra c d G ≤ E₂ :=
    productSecondDefectAlgebra_le_comparison c d G R₀ R₁
  have inputs : KasparovProductTechnicalInputs c d G E₁ E₂ Δ := {
    first_mem := Or.inl (Or.inl hb.first_mem)
    connection_mem := Or.inl (Or.inl hb.connection_mem)
    representation_mem := fun a => Or.inl (Or.inl (hb.representation_mem a))
    creation_square_mem := hb.creation_square_mem
    first_square_mem := hb.first_square_mem
    first_commutator_mem := hb.first_commutator_mem
    first_equivariance_mem := hb.first_equivariance_mem
    second_square_mem := h₂base hb.second_square_mem
    second_commutator_mem := fun a => h₂base (hb.second_commutator_mem a)
    second_equivariance_mem := fun g => h₂base (hb.second_equivariance_mem g)
    anticommutator_mem := h₂base hb.anticommutator_mem }
  let P := kasparovTechnicalProductOperator G p
  refine ⟨P, inputs.isGradedProduct p hcsa hGsa hGodd hG, ?_, ?_⟩
  · exact weightedTechnicalProduct_comparison_positive c d inputs p
      (Or.inl (Or.inr rfl)) (comparisonDefect_zero_mem c d G R₀ R₁) hR₀.positivity
  · exact weightedTechnicalProduct_comparison_positive c d inputs p
      (Or.inr rfl) (comparisonDefect_one_mem c d G R₀ R₁) hR₁.positivity

/-- Normalize the actually constructed common comparison product. The
comparison positivity is preserved by the actual localized perturbation,
so the preferred endpoint is exactly selfadjoint and contractive. -/
theorem exists_actualCommonSelfadjointPositiveComparisonProduct
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (hcsa : IsSelfAdjoint c.operator) (hdsa : IsSelfAdjoint d.operator)
    (hdnorm : ‖d.operator‖ ≤ 1)
    (hR₀sa : IsSelfAdjoint R₀) (hR₁sa : IsSelfAdjoint R₁)
    (hR₀ : IsGradedKasparovProductOperator c d R₀)
    (hR₁ : IsGradedKasparovProductOperator c d R₁) :
    ∃ P : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation),
      IsGradedKasparovProductOperator c d P ∧ IsSelfAdjoint P ∧ ‖P‖ ≤ 1 ∧
      (∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
        (R₀ * P + P * R₀) * star (gradedKasparovTensorRepresentation c d a))) ∧
      (∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
        (R₁ * P + P * R₁) * star (gradedKasparovTensorRepresentation c d a))) := by
  obtain ⟨P, hP, h₀, h₁⟩ := exists_actualCommonPositiveComparisonProduct c d R₀ R₁
    hcsa hdsa hdnorm hR₀sa hR₁sa hR₀ hR₁
  let q := gradedKasparovTensorCycleOfConditions c d P hP.cycleConditions
  have hright (a : A) : IsModuleCompact ((q.normalized.operator - P) *
      star (gradedKasparovTensorRepresentation c d a)) := by
    change IsModuleCompact ((q.normalizedOperator - q.operator) * star (q.representation a))
    simpa only [map_star] using q.normalizedOperator_sub_locallyCompact (star a)
  have hleft (a : A) : IsModuleCompact (gradedKasparovTensorRepresentation c d a *
      (q.normalized.operator - P)) :=
    q.locallyCompact_left_of_adjoint _ q.normalizedOperator_sub_adjoint_locallyCompact a
  refine ⟨q.normalized.operator, normalizedTensorCycle_isProduct c d hdsa hdnorm hP,
    q.normalized_selfadjoint, q.normalized_norm_le_one, ?_, ?_⟩
  · intro a
    exact localizedAnticommutator_positive_of_sub_compact
      (gradedKasparovTensorRepresentation c d a) R₀ P q.normalized.operator
      (hright a) (hleft a) (h₀ a)
  · intro a
    exact localizedAnticommutator_positive_of_sub_compact
      (gradedKasparovTensorRepresentation c d a) R₁ P q.normalized.operator
      (hright a) (hleft a) (h₁ a)

end BC4lean.KKTheory
