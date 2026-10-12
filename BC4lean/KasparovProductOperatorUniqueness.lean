import BC4lean.KasparovCutoffProductPath
import BC4lean.KasparovGeneralComparisonProduct

/-! # Genuine single-interval comparison homotopies of product operators

The continuous cutoff path is joined to the actual localized compact
perturbation paths at its endpoints. Concatenation is a genuine continuous
operator path on the fixed complete module, hence yields a single full
interval-coefficient witness. The common comparison operator is constructed
by the actual discrete technical theorem rather than supplied as data.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval TopologicalSpace

section PathOperations
variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovOperatorHomotopy
variable {q : GradedKasparovCycle α β δA δB E} {T₀ T₁ T₂ : AdjointableMap B E E}

/-- Genuine path reversal retains every actual pointwise cycle condition. -/
def reversePath (h : GradedKasparovOperatorHomotopy q T₀ T₁) :
    GradedKasparovOperatorHomotopy q T₁ T₀ where
  path := h.path.symm
  conditions t := h.conditions (σ t)

/-- Genuine path concatenation retains all cycle conditions because its
range is the actual union of the two path ranges. -/
def concatenatePaths (h : GradedKasparovOperatorHomotopy q T₀ T₁)
    (k : GradedKasparovOperatorHomotopy q T₁ T₂) :
    GradedKasparovOperatorHomotopy q T₀ T₂ where
  path := h.path.trans k.path
  conditions t := by
    have hmem : (h.path.trans k.path) t ∈ Set.range h.path ∪ Set.range k.path := by
      rw [← Path.trans_range]
      exact Set.mem_range_self t
    rcases hmem with hmem | hmem
    · obtain ⟨u, hu⟩ := hmem
      rw [← hu]
      exact h.conditions u
    · obtain ⟨u, hu⟩ := hmem
      rw [← hu]
      exact k.conditions u

end GradedKasparovOperatorHomotopy
end PathOperations

section CompareProducts
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
  {R P : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}

/-- Actual localized compact endpoint perturbations and the normalized
convex comparison path give a genuine operator homotopy of endpoints. -/
def positiveComparisonProductOperatorHomotopy
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P)
    (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P)
    (hpos : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * P + P * R) * star (gradedKasparovTensorRepresentation c d a))) :
    GradedKasparovOperatorHomotopy (gradedKasparovTensorCycleOfConditions c d R hR) R P := by
  let q := gradedKasparovTensorCycleOfConditions c d R hR
  let hmid := quarterCutoffAffineProductHomotopy c d hR hP hRsa hPsa hpos
  let hsource : GradedKasparovOperatorHomotopy q R (moduleSquareCutoffNormalization (1 / 4) R) :=
    GradedKasparovOperatorHomotopy.compactPerturbation q _ hmid.source_conditions
      (fun a => moduleSquareCutoffNormalization_sub_mul_isModuleCompact
        (by norm_num) (by norm_num) R (q.representation a) hRsa (hR.square_mod_compact a))
  have hPq : q.OperatorConditions P := ⟨hP.operator_odd, hP.selfadjoint_mod_compact,
    hP.square_mod_compact, hP.commutator_compact, hP.equivariance_mod_compact⟩
  let qP := q.withOperator P hPq
  have htargetP : qP.OperatorConditions (moduleSquareCutoffNormalization (1 / 4) P) := {
    operator_odd := fun x => hmid.target_conditions.operator_odd x
    selfadjoint_mod_compact := fun a => hmid.target_conditions.selfadjoint_mod_compact a
    square_mod_compact := fun a => hmid.target_conditions.square_mod_compact a
    commutator_compact := fun a => hmid.target_conditions.commutator_compact a
    equivariance_mod_compact := fun g a => hmid.target_conditions.equivariance_mod_compact g a }
  let htarget : GradedKasparovOperatorHomotopy q P (moduleSquareCutoffNormalization (1 / 4) P) := {
    path := affineKasparovOperatorPath P (moduleSquareCutoffNormalization (1 / 4) P)
    conditions t := by
      have h := qP.operatorConditions_affine_compactPerturbation
        (moduleSquareCutoffNormalization (1 / 4) P) htargetP
          (fun a => moduleSquareCutoffNormalization_sub_mul_isModuleCompact
            (by norm_num) (by norm_num) P (q.representation a) hPsa (hP.square_mod_compact a)) (t : ℝ)
      exact ⟨h.operator_odd, h.selfadjoint_mod_compact, h.square_mod_compact,
        h.commutator_compact, h.equivariance_mod_compact⟩ }
  exact (hsource.concatenatePaths hmid).concatenatePaths htarget.reversePath

/-- This is a single genuine full interval witness, including actual
whole-cycle fibre isomorphisms at both endpoint product cycles. -/
def positiveComparisonFullProductHomotopy
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P)
    (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P)
    (hpos : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * P + P * R) * star (gradedKasparovTensorRepresentation c d a))) :
    FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d R hR))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d P hP)) := by
  let h := positiveComparisonProductOperatorHomotopy c d hR hP hRsa hPsa hpos
  have hs : (gradedKasparovTensorCycleOfConditions c d R hR).withOperator R h.source_conditions =
      gradedKasparovTensorCycleOfConditions c d R hR := rfl
  have ht : (gradedKasparovTensorCycleOfConditions c d R hR).withOperator P h.target_conditions =
      gradedKasparovTensorCycleOfConditions c d P hP := rfl
  simpa only [hs, ht] using h.fullHomotopy

/-- Arbitrary product operators for a selfadjoint first cycle and a
selfadjoint contractive second cycle are joined by one genuine full
interval homotopy. The products are normalized internally; the preferred
comparison and its partition are constructed by the technical theorem. -/
theorem exists_fullProductOperatorHomotopy_of_normalized_inputs
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (hcsa : IsSelfAdjoint c.operator) (hdsa : IsSelfAdjoint d.operator) (hdnorm : ‖d.operator‖ ≤ 1)
    {R₀ R₁ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR₀ : IsGradedKasparovProductOperator c d R₀)
    (hR₁ : IsGradedKasparovProductOperator c d R₁) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d R₀ hR₀.cycleConditions))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d R₁ hR₁.cycleConditions))) := by
  let q₀ := gradedKasparovTensorCycleOfConditions c d R₀ hR₀.cycleConditions
  let q₁ := gradedKasparovTensorCycleOfConditions c d R₁ hR₁.cycleConditions
  have h₀n := normalizedTensorCycle_isProduct c d hdsa hdnorm hR₀
  have h₁n := normalizedTensorCycle_isProduct c d hdsa hdnorm hR₁
  obtain ⟨P, hP, hPsa, _, h₀pos, h₁pos⟩ :=
    exists_actualCommonSelfadjointPositiveComparisonProduct c d q₀.normalized.operator q₁.normalized.operator
      hcsa hdsa hdnorm q₀.normalized_selfadjoint q₁.normalized_selfadjoint h₀n h₁n
  let h₀cmp := positiveComparisonProductOperatorHomotopy c d h₀n.cycleConditions hP.cycleConditions
    q₀.normalized_selfadjoint hPsa h₀pos
  let h₁cmp := positiveComparisonProductOperatorHomotopy c d h₁n.cycleConditions hP.cycleConditions
    q₁.normalized_selfadjoint hPsa h₁pos
  let hn₀ : GradedKasparovOperatorHomotopy q₀ R₀ q₀.normalized.operator := q₀.normalizationHomotopy
  let hc₀ : GradedKasparovOperatorHomotopy q₀ q₀.normalized.operator P := {
    path := h₀cmp.path
    conditions t := by
      have ht := h₀cmp.conditions t
      exact ⟨ht.operator_odd, ht.selfadjoint_mod_compact, ht.square_mod_compact,
        ht.commutator_compact, ht.equivariance_mod_compact⟩ }
  let hc₁ : GradedKasparovOperatorHomotopy q₀ q₁.normalized.operator P := {
    path := h₁cmp.path
    conditions t := by
      have ht := h₁cmp.conditions t
      exact ⟨ht.operator_odd, ht.selfadjoint_mod_compact, ht.square_mod_compact,
        ht.commutator_compact, ht.equivariance_mod_compact⟩ }
  let hn₁ : GradedKasparovOperatorHomotopy q₀ R₁ q₁.normalized.operator := {
    path := q₁.normalizationHomotopy.path
    conditions t := by
      have ht := q₁.normalizationHomotopy.conditions t
      exact ⟨ht.operator_odd, ht.selfadjoint_mod_compact, ht.square_mod_compact,
        ht.commutator_compact, ht.equivariance_mod_compact⟩ }
  let h := ((hn₀.concatenatePaths hc₀).concatenatePaths hc₁.reversePath).concatenatePaths hn₁.reversePath
  have hs : q₀.withOperator R₀ h.source_conditions = q₀ := rfl
  have ht : q₀.withOperator R₁ h.target_conditions = q₁ := rfl
  exact ⟨by simpa only [hs, ht] using h.fullHomotopy⟩

/-- The actual weighted original-first comparison removes first-operator
selfadjointness from the single-interval uniqueness construction. -/
theorem exists_fullProductOperatorHomotopy_of_selfadjoint_second
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (hdsa : IsSelfAdjoint d.operator) (hdnorm : ‖d.operator‖ ≤ 1)
    {R₀ R₁ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR₀ : IsGradedKasparovProductOperator c d R₀)
    (hR₁ : IsGradedKasparovProductOperator c d R₁) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d R₀ hR₀.cycleConditions))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d R₁ hR₁.cycleConditions))) := by
  let q₀ := gradedKasparovTensorCycleOfConditions c d R₀ hR₀.cycleConditions
  let q₁ := gradedKasparovTensorCycleOfConditions c d R₁ hR₁.cycleConditions
  have h₀n := normalizedTensorCycle_isProduct c d hdsa hdnorm hR₀
  have h₁n := normalizedTensorCycle_isProduct c d hdsa hdnorm hR₁
  obtain ⟨P, hP, hPsa, _, h₀pos, h₁pos⟩ :=
    exists_actualCommonSelfadjointPositiveComparisonProduct_of_arbitrary_first c d
      q₀.normalized.operator q₁.normalized.operator hdsa hdnorm
      q₀.normalized_selfadjoint q₁.normalized_selfadjoint h₀n h₁n
  let h₀cmp := positiveComparisonProductOperatorHomotopy c d h₀n.cycleConditions hP.cycleConditions
    q₀.normalized_selfadjoint hPsa h₀pos
  let h₁cmp := positiveComparisonProductOperatorHomotopy c d h₁n.cycleConditions hP.cycleConditions
    q₁.normalized_selfadjoint hPsa h₁pos
  let hn₀ : GradedKasparovOperatorHomotopy q₀ R₀ q₀.normalized.operator := q₀.normalizationHomotopy
  let hc₀ : GradedKasparovOperatorHomotopy q₀ q₀.normalized.operator P := {
    path := h₀cmp.path
    conditions t := by
      have ht := h₀cmp.conditions t
      exact ⟨ht.operator_odd, ht.selfadjoint_mod_compact, ht.square_mod_compact,
        ht.commutator_compact, ht.equivariance_mod_compact⟩ }
  let hc₁ : GradedKasparovOperatorHomotopy q₀ q₁.normalized.operator P := {
    path := h₁cmp.path
    conditions t := by
      have ht := h₁cmp.conditions t
      exact ⟨ht.operator_odd, ht.selfadjoint_mod_compact, ht.square_mod_compact,
        ht.commutator_compact, ht.equivariance_mod_compact⟩ }
  let hn₁ : GradedKasparovOperatorHomotopy q₀ R₁ q₁.normalized.operator := {
    path := q₁.normalizationHomotopy.path
    conditions t := by
      have ht := q₁.normalizationHomotopy.conditions t
      exact ⟨ht.operator_odd, ht.selfadjoint_mod_compact, ht.square_mod_compact,
        ht.commutator_compact, ht.equivariance_mod_compact⟩ }
  let h := ((hn₀.concatenatePaths hc₀).concatenatePaths hc₁.reversePath).concatenatePaths hn₁.reversePath
  have hs : q₀.withOperator R₀ h.source_conditions = q₀ := rfl
  have ht : q₀.withOperator R₁ h.target_conditions = q₁ := rfl
  exact ⟨by simpa only [hs, ht] using h.fullHomotopy⟩

/-- Genuine operator-product uniqueness for arbitrary actual graded
input cycles: one full interval-coefficient witness joins the actual
product cycles on the actual interior tensor. Both inputs are normalized
internally by their localized perturbations, and every technical
partition and comparison operator is constructed. -/
theorem exists_fullGradedKasparovProductOperatorHomotopy
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    {R₀ R₁ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR₀ : IsGradedKasparovProductOperator c d R₀)
    (hR₁ : IsGradedKasparovProductOperator c d R₁) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d R₀ hR₀.cycleConditions))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d R₁ hR₁.cycleConditions))) := by
  have h₀n := (isGradedKasparovProductOperator_iff_normalized_second c d R₀).1 hR₀
  have h₁n := (isGradedKasparovProductOperator_iff_normalized_second c d R₁).1 hR₁
  exact exists_fullProductOperatorHomotopy_of_selfadjoint_second c d.normalized
    d.normalized_selfadjoint d.normalized_norm_le_one h₀n h₁n

end CompareProducts
end BC4lean.KKTheory
