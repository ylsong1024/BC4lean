import BC4lean.LeftUnitIntervalEndpointConnections
import BC4lean.FullGradedKasparovHomotopyEquivalence
import BC4lean.KasparovProductOperatorUniqueness
import BC4lean.KasparovProductNormalization
import BC4lean.HeterogeneousFullGradedKasparovHomotopy

/-! # A genuine full left-unit witness for arbitrary representations

The nonunital ideal J gives the full interval module. The zero endpoint
is a compact perturbation of the internally normalized original cycle;
the one endpoint is an actual identity product on A tensor E. Actual
normalization, endpoint uniqueness and matched-module concatenation give
one full witness for every prescribed product. Degenerate representations
require no essential-range projection or complement.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

section IndependentCarrier

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] [Countable Γ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

theorem exists_fullGradedKasparovLeftUnitHomotopy
    (c : GradedKasparovCycle α β δA δB E)
    {R : AdjointableMap B (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation)
      (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation)}
    (hR : IsGradedKasparovProductOperator
      (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c R) :
    Nonempty (HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB,
      max uA uE, uE, max uA uE}
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions
        (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c R hR.cycleConditions))
      (BundledGradedKasparovCycle.of c)) := by
  let i := gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading
  let cₙ := c.normalized
  obtain ⟨ξ, p, ⟨P⟩, hξ⟩ := leftUnitIntervalIdeal_exists_homogeneousParsevalFrame δA
  let Z := cₙ.leftUnitZeroOperator P p
  let Q := cₙ.leftUnitOneOperator P p
  let hZ := cₙ.leftUnitZeroOperator_conditions P p hξ c.normalized_selfadjoint
  have hQₙ : IsGradedKasparovProductOperator i cₙ Q :=
    cₙ.leftUnitOneOperator_isProduct P p hξ c.normalized_selfadjoint
  have hQ : IsGradedKasparovProductOperator i c Q :=
    (isGradedKasparovProductOperator_iff_normalized_second i c Q).2 hQₙ
  let hpert := GradedKasparovOperatorHomotopy.compactPerturbation cₙ Z hZ
    (fun a => (cₙ.leftUnitZeroOperator_sub_compact P p hξ).comp_right (cₙ.representation a))
  have Hpert : FullGradedKasparovHomotopy (BundledGradedKasparovCycle.of cₙ)
      (BundledGradedKasparovCycle.of (cₙ.withOperator Z hZ)) := by
    simpa only [GradedKasparovCycle.withOperator_self] using hpert.fullHomotopy
  let Hint : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB,
      uE, max uA uE, max uA uE}
      (BundledGradedKasparovCycle.of (cₙ.withOperator Z hZ))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions i c Q hQ.cycleConditions)) := {
    intervalCycle := BundledGradedKasparovCycle.of
      (cₙ.leftUnitIntervalConnectionCycle P p hξ c.normalized_selfadjoint)
    sourceIso := cₙ.leftUnitZeroCycleIso P p hξ c.normalized_selfadjoint
    targetIso := cₙ.leftUnitOneCycleIso P p hξ c.normalized_selfadjoint }
  obtain ⟨Hunique⟩ := exists_fullGradedKasparovProductOperatorHomotopy i c hQ hR
  exact ⟨((((HeterogeneousFullGradedKasparovHomotopy.ofFull c.fullNormalizationHomotopy).trans
    (HeterogeneousFullGradedKasparovHomotopy.ofFull Hpert)).trans Hint).trans
      (HeterogeneousFullGradedKasparovHomotopy.ofFull Hunique)).symm⟩

end IndependentCarrier

section FixedUniverseCarrier

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type (max uA uE)} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] [Countable Γ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- The original fixed-universe left-unit target is recovered when its
carrier universe already contains the identity carrier universe. -/
theorem exists_fullGradedKasparovLeftUnitHomotopy_of_full
    (c : GradedKasparovCycle α β δA δB E)
    {R : AdjointableMap B (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation)
      (InteriorModuleTensor (E := Aᵐᵒᵖ) c.representation)}
    (hR : IsGradedKasparovProductOperator
      (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c R) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions
        (gradedStandardIdentityCycle α δA c.sourceAction_preservesGrading) c R hR.cycleConditions))
      (BundledGradedKasparovCycle.of c)) := by
  obtain ⟨H⟩ := exists_fullGradedKasparovLeftUnitHomotopy c hR
  exact ⟨H.toFull⟩

end FixedUniverseCarrier
end BC4lean.KKTheory
