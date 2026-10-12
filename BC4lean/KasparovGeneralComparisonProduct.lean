import BC4lean.KasparovCommonComparisonProduct

/-! # Actual common comparisons retaining an arbitrary first operator

The genuine first normalization is used to construct a cycle, while its
original operator and anticommutator remain in the technical schedules.
The original product positivity is weighted before its normalization
error is removed. All memberships and normalizer hypotheses are proved
in the actual sandwich algebra. No original first selfadjointness is used.
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
  (R₀ R₁ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))

/-- Construct the comparison for an arbitrary actual first operator. The
second operator is a selfadjoint contraction; its defects stay localized. -/
theorem exists_actualCommonPositiveComparisonProduct_of_arbitrary_first
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (hdsa : IsSelfAdjoint d.operator) (hdnorm : ‖d.operator‖ ≤ 1)
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
  let cₙ := c.normalized
  obtain ⟨G, hGodd, hGsa, _, hG⟩ :=
    exists_odd_selfadjoint_contractive_gradedKasparovConnection cₙ d hdsa hdnorm
  have hGoriginal : GradedKasparovConnection c d G := {
    even := hG.even
    even_adjoint := hG.even_adjoint
    odd := hG.odd
    odd_adjoint := hG.odd_adjoint
  }
  have hR₀cn : GradedKasparovConnection cₙ d R₀ := {
    even := hR₀.connection.even
    even_adjoint := hR₀.connection.even_adjoint
    odd := hR₀.connection.odd
    odd_adjoint := hR₀.connection.odd_adjoint
  }
  have hR₁cn : GradedKasparovConnection cₙ d R₁ := {
    even := hR₁.connection.even
    even_adjoint := hR₁.connection.even_adjoint
    odd := hR₁.connection.odd
    odd_adjoint := hR₁.connection.odd_adjoint
  }
  -- Normalization retains the grading, representation and action. Rebuild
  -- the indexed conditions from those unchanged fields, rather than coercing
  -- an entire structure whose first-cycle index has changed.
  have hR₀cyclecn : GradedKasparovTensorOperatorConditions cₙ d R₀ := {
    operator_odd := hR₀.cycleConditions.operator_odd
    selfadjoint_mod_compact := hR₀.cycleConditions.selfadjoint_mod_compact
    square_mod_compact := hR₀.cycleConditions.square_mod_compact
    commutator_compact := hR₀.cycleConditions.commutator_compact
    equivariance_mod_compact := hR₀.cycleConditions.equivariance_mod_compact
  }
  have hR₁cyclecn : GradedKasparovTensorOperatorConditions cₙ d R₁ := {
    operator_odd := hR₁.cycleConditions.operator_odd
    selfadjoint_mod_compact := hR₁.cycleConditions.selfadjoint_mod_compact
    square_mod_compact := hR₁.cycleConditions.square_mod_compact
    commutator_compact := hR₁.cycleConditions.commutator_compact
    equivariance_mod_compact := hR₁.cycleConditions.equivariance_mod_compact
  }
  let E₁ := firstProductAlgebra (E := E) d.representation d.operator
  let E₂cmp := productComparisonDefectAlgebra cₙ d G R₀ R₁
  let E₂orig := productSecondDefectAlgebra c d G
  let E₂ := generatedClosedStarAlgebra E₂cmp E₂orig
  let Δ := productComparisonNormalizerTests cₙ d G R₀ R₁ ∪ productNormalizerTests c d G
  let f : ℕ → AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) := fun _ => 0
  let J := gradedKasparovTensorGrading cₙ d
  let U := gradedKasparovTensorAction cₙ d
  let : IsClosed (E₁ : Set (AdjointableMap C
      (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))) :=
    firstProductAlgebra_isClosed (E := E) d.representation d.operator
  let : IsClosed (E₂cmp : Set (AdjointableMap C
      (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))) :=
    productComparisonDefectAlgebra_isClosed (E := E) cₙ d G R₀ R₁
  let : IsClosed (E₂orig : Set (AdjointableMap C
      (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))) :=
    productSecondDefectAlgebra_isClosed (E := E) c d G
  let : IsClosed (E₂ : Set (AdjointableMap C
      (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))) :=
    generatedClosedStarAlgebra_isClosed E₂cmp E₂orig
  obtain ⟨q₁, hq₁left, hq₁right⟩ :=
    exists_firstProductAlgebra_approximateUnit d.representation d.operator c.countablyGenerated
  obtain ⟨q₂cmp, hq₂cmpleft, hq₂cmpright⟩ :=
    exists_productComparisonDefectAlgebra_approximateUnit cₙ d G R₀ R₁
  obtain ⟨q₂orig, hq₂origleft, hq₂origright⟩ :=
    exists_productSecondDefectAlgebra_approximateUnit c d G
  obtain ⟨q₂, _, _, _, _, _, hq₂left, hq₂right⟩ :=
    exists_generatedClosedStarAlgebra_approximateUnit E₂cmp E₂orig q₂cmp q₂orig
      hq₂cmpleft hq₂cmpright hq₂origleft hq₂origright
  have h₂local : E₂ ≤ creationLocallyCompactAlgebra (E := E) d.representation :=
    generatedClosedStarAlgebra_le E₂cmp E₂orig _
      (creationLocallyCompactAlgebra_isClosed d.representation)
      (productComparisonDefectAlgebra_creationLocallyCompact cₙ d G R₀ R₁ hdsa hGsa hG hR₀cn hR₁cn)
      (productSecondDefectAlgebra_creationLocallyCompact c d G hdsa hGsa hGoriginal)
  have hgrade₂ : ∀ a ∈ E₂, J.conjugateOperator a ∈ E₂ :=
    maps_generatedClosedStarAlgebra E₂cmp E₂orig J.conjugateOperatorStarAlgEquiv
      (grading_preserves_productComparisonDefectAlgebra cₙ d G R₀ R₁)
      (grading_preserves_productSecondDefectAlgebra c d G)
  have hnormal : ∀ T ∈ Δ, ∀ a ∈ E₁, T * a - a * T ∈ E₁ := by
    intro T hT
    rcases hT with hT | hT
    · exact productComparisonNormalizerTests_normalize_firstProductAlgebra cₙ d G R₀ R₁
        hdsa hGsa hR₀sa hR₁sa hG hR₀cn hR₁cn T hT
    · exact productNormalizerTests_normalize_firstProductAlgebra c d G hdsa hGsa hGoriginal T hT
  obtain ⟨p⟩ := exists_kasparovDiscreteTechnicalPartition
    (c.countablyGenerated.interiorTensor d.countablyGenerated d.representation)
    J U (gradedKasparovTensorAction_preservesGrading cₙ d) E₁ E₂ q₁ q₂
    hq₁left hq₁right hq₂left hq₂right
    (fun a ha b hb => (firstProductAlgebra_products_compact d.representation d.operator ha (h₂local hb)).1)
    (action_preserves_firstProductAlgebra cₙ d hdsa)
    (grading_preserves_firstProductAlgebra d.representation cₙ.grading d.grading
      d.representation_graded d.operator d.operator_odd)
    hgrade₂ Δ ((productComparisonNormalizerTests_isSeparable cₙ d G R₀ R₁).union
      (productNormalizerTests_isSeparable c d G)) hnormal
    f ⟨0, fun _ => by simp [f]⟩
    (fun _ a _ => by
      change IsModuleCompact (a * 0) ∧ IsModuleCompact (0 * a)
      rw [mul_zero, zero_mul]
      exact ⟨IsModuleCompact.zero, IsModuleCompact.zero⟩)
  have hb := actualKasparovProductTechnicalInputs cₙ d G
  have h₂base : productSecondDefectAlgebra cₙ d G ≤ E₂ :=
    (productSecondDefectAlgebra_le_comparison cₙ d G R₀ R₁).trans
      (le_generatedClosedStarAlgebra_left E₂cmp E₂orig)
  have inputs : KasparovProductTechnicalInputs cₙ d G E₁ E₂ Δ := {
    first_mem := Or.inl (Or.inl (Or.inl hb.first_mem))
    connection_mem := Or.inl (Or.inl (Or.inl hb.connection_mem))
    representation_mem := fun a => Or.inl (Or.inl (Or.inl (hb.representation_mem a)))
    creation_square_mem := hb.creation_square_mem
    first_square_mem := hb.first_square_mem
    first_commutator_mem := hb.first_commutator_mem
    first_equivariance_mem := hb.first_equivariance_mem
    second_square_mem := h₂base hb.second_square_mem
    second_commutator_mem := fun a => h₂base (hb.second_commutator_mem a)
    second_equivariance_mem := fun g => h₂base (hb.second_equivariance_mem g)
    anticommutator_mem := h₂base hb.anticommutator_mem
  }
  let P := kasparovTechnicalProductOperator G p
  let O := interiorModuleTensorOperator d.representation c.operator
  have hOΔ : O ∈ Δ := Or.inr (Or.inl (Or.inl rfl))
  have hOG : O * G + G * O ∈ E₂ :=
    le_generatedClosedStarAlgebra_right E₂cmp E₂orig
      (actualKasparovProductTechnicalInputs c d G).anticommutator_mem
  have hK (b : A) : (O - interiorModuleTensorOperator d.representation cₙ.operator) *
      gradedKasparovTensorRepresentation cₙ d b ∈ E₁ := by
    have hc := (c.normalizedOperator_sub_locallyCompact b).neg
    have heq : -((c.normalizedOperator - c.operator) * c.representation b) =
        (c.operator - cₙ.operator) * c.representation b := by
      change -((c.normalizedOperator - c.operator) * c.representation b) =
        (c.operator - c.normalizedOperator) * c.representation b
      noncomm_ring
    rw [heq] at hc
    have ht := tensorCompact_mem_firstProductAlgebra d.representation d.operator hc
    change interiorModuleTensorOperatorHom d.representation
      ((c.operator - cₙ.operator) * c.representation b) ∈ E₁ at ht
    change (interiorModuleTensorOperator d.representation c.operator -
      interiorModuleTensorOperator d.representation cₙ.operator) *
        interiorModuleTensorOperator d.representation (c.representation b) ∈ E₁
    simpa only [map_sub, map_mul, interiorModuleTensorOperatorHom_apply] using ht
  have hPn : IsGradedKasparovProductOperator cₙ d P :=
    inputs.isGradedProduct p c.normalized_selfadjoint hGsa hGodd hG
  have hP : IsGradedKasparovProductOperator c d P := {
    cycleConditions := {
      operator_odd := hPn.cycleConditions.operator_odd
      selfadjoint_mod_compact := hPn.cycleConditions.selfadjoint_mod_compact
      square_mod_compact := hPn.cycleConditions.square_mod_compact
      commutator_compact := hPn.cycleConditions.commutator_compact
      equivariance_mod_compact := hPn.cycleConditions.equivariance_mod_compact }
    connection := {
      even := hPn.connection.even
      even_adjoint := hPn.connection.even_adjoint
      odd := hPn.connection.odd
      odd_adjoint := hPn.connection.odd_adjoint }
    positivity := inputs.weighted_positivity_of_firstReplacement p O hOΔ hOG hK
  }
  have hR₀Δ : R₀ ∈ Δ := Or.inl (Or.inl (Or.inr rfl))
  have hR₁Δ : R₁ ∈ Δ := Or.inl (Or.inr rfl)
  have hR₀G : R₀ * G + G * R₀ - 2 ∈ E₂ :=
    le_generatedClosedStarAlgebra_left E₂cmp E₂orig (comparisonDefect_zero_mem cₙ d G R₀ R₁)
  have hR₁G : R₁ * G + G * R₁ - 2 ∈ E₂ :=
    le_generatedClosedStarAlgebra_left E₂cmp E₂orig (comparisonDefect_one_mem cₙ d G R₀ R₁)
  refine ⟨P, hP, ?_, ?_⟩
  · exact weightedTechnicalProduct_comparison_positive_of_firstReplacement cₙ d inputs p hR₀Δ hR₀G
      hR₀cyclecn (hR₀cn.normalizes_firstProductAlgebra hR₀sa hdsa) O hOΔ hK hR₀.positivity
  · exact weightedTechnicalProduct_comparison_positive_of_firstReplacement cₙ d inputs p hR₁Δ hR₁G
      hR₁cyclecn (hR₁cn.normalizes_firstProductAlgebra hR₁sa hdsa) O hOΔ hK hR₁.positivity

/-- Exact selfadjoint contractive comparison for an arbitrary first
operator, with both original comparison inequalities retained. -/
theorem exists_actualCommonSelfadjointPositiveComparisonProduct_of_arbitrary_first
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (hdsa : IsSelfAdjoint d.operator) (hdnorm : ‖d.operator‖ ≤ 1)
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
  obtain ⟨P, hP, h₀, h₁⟩ := exists_actualCommonPositiveComparisonProduct_of_arbitrary_first c d R₀ R₁
    hdsa hdnorm hR₀sa hR₁sa hR₀ hR₁
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
