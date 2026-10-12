import BC4lean.GradedKasparovTripleAssociativity
import BC4lean.GradedKasparovFirstInputProductHomotopy
import BC4lean.GradedKasparovSecondInputProductHomotopy

/-! # Associativity for four arbitrary prescribed genuine products

Both endpoint associations are transported by the independently constructed
first- and second-input full product homotopies to normalized input cycles.
Actual products of the normalized input cycles are chosen and normalized
with their genuine criteria preserved. The constructed common triple product
then supplies associativity there. Actual matched-interval concatenation
returns one full witness with the four original prescribed products as data.
No endpoint product, nondegeneracy or associativity hypothesis is introduced.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open InteriorModuleTensorAssociator

section PairNormalization
variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)

/-- A prescribed original product and any prescribed product of the
normalized inputs are connected by genuine chosen-endpoint input descent. -/
theorem exists_fullProductPairNormalizationHomotopy
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] [Countable Γ]
    {Q : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    {Qn : AdjointableMap C (InteriorModuleTensor (E := E) d.normalized.representation)
      (InteriorModuleTensor (E := E) d.normalized.representation)}
    (hQ : IsGradedKasparovProductOperator c d Q)
    (hQn : IsGradedKasparovProductOperator c.normalized d.normalized Qn) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c d Q hQ.cycleConditions))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions
        c.normalized d.normalized Qn hQn.cycleConditions))) := by
  obtain ⟨W, hW⟩ := exists_actualGradedKasparovProductOperator c.normalized d
  obtain ⟨Hc⟩ := exists_fullGradedKasparovFirstInputProductHomotopy_of_full d c c.normalized
    c.fullNormalizationHomotopy hQ hW
  obtain ⟨Hd⟩ := exists_fullGradedKasparovSecondInputProductHomotopy_of_full c.normalized d d.normalized
    d.fullNormalizationHomotopy hW hQn
  exact ⟨Hc.trans Hd⟩
end PairNormalization

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


variable (L : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
  (LeftTensor (E := E) d.representation e.representation))

/-- Associativity for arbitrary input cycles and all four arbitrary
prescribed actual products, witnessed by a single arbitrary complete
countably generated interval cycle and whole-cycle endpoint isomorphisms. -/
theorem exists_fullGradedKasparovAssociativityHomotopy
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D] [Countable Γ]
    (hQproduct : IsGradedKasparovProductOperator c d Q)
    (hTproduct : IsGradedKasparovProductOperator d e T)
    (hLproduct : IsGradedKasparovProductOperator (firstPairCycle c d Q hQ) e L)
    (hRproduct : IsGradedKasparovProductOperator c (secondPairCycle d e T hT) R) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions
        (firstPairCycle c d Q hQ) e L hLproduct.cycleConditions))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions
        c (secondPairCycle d e T hT) R hRproduct.cycleConditions))) := by
  let cn := c.normalized
  let dn := d.normalized
  let en := e.normalized
  obtain ⟨Q₀, hQ₀⟩ := exists_actualGradedKasparovProductOperator cn dn
  let q₀ := gradedKasparovTensorCycleOfConditions cn dn Q₀ hQ₀.cycleConditions
  let Qn := q₀.normalized.operator
  have hQn : IsGradedKasparovProductOperator cn dn Qn := normalizedTensorCycle_isProduct cn dn
    d.normalized_selfadjoint d.normalized_norm_le_one hQ₀
  let cn₁₂ := firstPairCycle cn dn Qn hQn.cycleConditions
  obtain ⟨T₀, hT₀⟩ := exists_actualGradedKasparovProductOperator dn en
  let t₀ := gradedKasparovTensorCycleOfConditions dn en T₀ hT₀.cycleConditions
  let Tn := t₀.normalized.operator
  have hTn : IsGradedKasparovProductOperator dn en Tn := normalizedTensorCycle_isProduct dn en
    e.normalized_selfadjoint e.normalized_norm_le_one hT₀
  let cn₂₃ := secondPairCycle dn en Tn hTn.cycleConditions
  obtain ⟨Ln, hLn⟩ := exists_actualGradedKasparovProductOperator cn₁₂ en
  obtain ⟨R₀, hR₀⟩ := exists_actualGradedKasparovProductOperator cn cn₂₃
  let r₀ := gradedKasparovTensorCycleOfConditions cn cn₂₃ R₀ hR₀.cycleConditions
  let Rn := r₀.normalized.operator
  have hRn : IsGradedKasparovProductOperator cn cn₂₃ Rn := normalizedTensorCycle_isProduct cn cn₂₃
    t₀.normalized_selfadjoint t₀.normalized_norm_le_one hR₀
  obtain ⟨Hassoc⟩ := exists_fullGradedKasparovAssociativityHomotopy_of_selfadjoint_inputs
    cn dn en Qn hQn.cycleConditions Tn hTn.cycleConditions Rn Ln hQn hTn hLn hRn
    c.normalized_selfadjoint d.normalized_selfadjoint e.normalized_selfadjoint
    q₀.normalized_selfadjoint t₀.normalized_selfadjoint r₀.normalized_selfadjoint
  let c₁₂ := firstPairCycle c d Q hQ
  let c₂₃ := secondPairCycle d e T hT
  obtain ⟨HQ⟩ := exists_fullProductPairNormalizationHomotopy c d hQproduct hQn
  obtain ⟨TQ⟩ := exists_fullProductPairNormalizationHomotopy d e hTproduct hTn
  obtain ⟨L₁, hL₁⟩ := exists_actualGradedKasparovProductOperator cn₁₂ e
  obtain ⟨HLfirst⟩ := exists_fullGradedKasparovFirstInputProductHomotopy_of_full e c₁₂ cn₁₂
    HQ hLproduct hL₁
  obtain ⟨HLsecond⟩ := exists_fullGradedKasparovSecondInputProductHomotopy_of_full cn₁₂ e en
    e.fullNormalizationHomotopy hL₁ hLn
  obtain ⟨R₁, hR₁⟩ := exists_actualGradedKasparovProductOperator c cn₂₃
  obtain ⟨HRsecond⟩ := exists_fullGradedKasparovSecondInputProductHomotopy_of_full c c₂₃ cn₂₃
    TQ hRproduct hR₁
  obtain ⟨HRfirst⟩ := exists_fullGradedKasparovFirstInputProductHomotopy_of_full cn₂₃ c cn
    c.fullNormalizationHomotopy hR₁ hRn
  exact ⟨(((HLfirst.trans HLsecond).trans Hassoc).trans
    (HRsecond.trans HRfirst).symm)⟩

end BC4lean.KKTheory.KasparovTriple
