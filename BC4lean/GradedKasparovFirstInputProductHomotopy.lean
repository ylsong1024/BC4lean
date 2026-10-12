import BC4lean.GradedKasparovFirstFibreProduct
import BC4lean.KasparovProductExistence
import BC4lean.FullGradedKasparovHomotopyEquivalence
import BC4lean.GradedKasparovFirstIsoProduct
import BC4lean.KasparovProductOperatorUniqueness
import BC4lean.HeterogeneousFullGradedKasparovHomotopy
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # An actual product homotopy for an arbitrary first interval module

The fixed second cycle is lifted to its genuine continuous-section cycle,
then the generic product theorem is applied to the actual first interval
correspondence. The true endpoint tensor fibres give products, identified
by the constructed first-variable fibre unitaries.
-/

noncomputable section
universe uΓ uA uB uC uE uF uG uM uH
namespace BC4lean.KKTheory
open TopologicalSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC}
  {M : Type uM} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(unitInterval, B)ᵐᵒᵖ M]
  [CStarModule C(unitInterval, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α (β.continuousSections (X := unitInterval))
    δA δB.continuousSections M) (d : GradedKasparovCycle β γ δB δC F)

theorem exists_fullFirstFibreProductHomotopy
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ] :
    ∃ R₀ : AdjointableMap C (InteriorModuleTensor (E := HilbertModuleFibre B M (0 : unitInterval))
          d.representation)
        (InteriorModuleTensor (E := HilbertModuleFibre B M (0 : unitInterval)) d.representation),
      ∃ R₁ : AdjointableMap C (InteriorModuleTensor (E := HilbertModuleFibre B M (1 : unitInterval))
            d.representation)
          (InteriorModuleTensor (E := HilbertModuleFibre B M (1 : unitInterval)) d.representation),
        ∃ hR₀ : IsGradedKasparovProductOperator (c.fibre 0) d R₀,
          ∃ hR₁ : IsGradedKasparovProductOperator (c.fibre 1) d R₁,
            Nonempty (FullGradedKasparovHomotopy
              (BundledGradedKasparovCycle.of
                (gradedKasparovTensorCycleOfConditions (c.fibre 0) d R₀ hR₀.cycleConditions))
              (BundledGradedKasparovCycle.of
                (gradedKasparovTensorCycleOfConditions (c.fibre 1) d R₁ hR₁.cycleConditions))) := by
  obtain ⟨R, hR⟩ := exists_actualGradedKasparovProductOperator c d.continuousSections
  let R₀ := gradedKasparovFirstFibreProductOperator (E := M) d 0 R
  let R₁ := gradedKasparovFirstFibreProductOperator (E := M) d 1 R
  let hR₀ := gradedKasparovFirstFibreProduct_isProduct c d 0 hR
  let hR₁ := gradedKasparovFirstFibreProduct_isProduct c d 1 hR
  refine ⟨R₀, R₁, hR₀, hR₁, ⟨?_⟩⟩
  exact {
    intervalCycle := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c d.continuousSections R hR.cycleConditions)
    sourceIso := gradedKasparovFirstFibreProduct_cycleIso c d 0 hR
    targetIso := gradedKasparovFirstFibreProduct_cycleIso c d 1 hR }

section ChosenEndpoints

variable {E : Type uE} {G : Type uG}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]
  (c₀ : GradedKasparovCycle α β δA δB E) (c₁ : GradedKasparovCycle α β δA δB G)

/-- A genuine first-input full homotopy, with independent endpoint and
interval carrier universes, carries any specified endpoint
products to one actual full witness. The interior interval product and its
two fibre identifications are constructed before endpoint uniqueness is
used; the witnesses concatenate through the actual matched module. -/
theorem exists_fullGradedKasparovFirstInputProductHomotopy
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (h : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uG, uH} (BundledGradedKasparovCycle.of c₀)
      (BundledGradedKasparovCycle.of c₁))
    {R₀ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    {R₁ : AdjointableMap C (InteriorModuleTensor (E := G) d.representation)
      (InteriorModuleTensor (E := G) d.representation)}
    (hR₀ : IsGradedKasparovProductOperator c₀ d R₀)
    (hR₁ : IsGradedKasparovProductOperator c₁ d R₁) :
    Nonempty (HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uC,
      max uE uF, max uG uF, max (max (max uE uF) uG) uH}
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c₀ d R₀ hR₀.cycleConditions))
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c₁ d R₁ hR₁.cycleConditions))) := by
  let D := h.intervalCycle.cycle
  obtain ⟨S₀, S₁, hS₀, hS₁, ⟨H⟩⟩ := exists_fullFirstFibreProductHomotopy D d
  let P₀ := gradedKasparovFirstIsoProductOperator (D.fibre 0) c₀ d h.sourceIso S₀
  let P₁ := gradedKasparovFirstIsoProductOperator (D.fibre 1) c₁ d h.targetIso S₁
  have hP₀ : IsGradedKasparovProductOperator c₀ d P₀ :=
    gradedKasparovFirstIsoProduct_isProduct (D.fibre 0) c₀ d h.sourceIso hS₀
  have hP₁ : IsGradedKasparovProductOperator c₁ d P₁ :=
    gradedKasparovFirstIsoProduct_isProduct (D.fibre 1) c₁ d h.targetIso hS₁
  let H' := (HeterogeneousFullGradedKasparovHomotopy.ofFull H).changeEndpoints
    (e := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c₀ d P₀ hP₀.cycleConditions))
    (f := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c₁ d P₁ hP₁.cycleConditions))
    (gradedKasparovFirstIsoProduct_cycleIso (D.fibre 0) c₀ d h.sourceIso hS₀)
    (gradedKasparovFirstIsoProduct_cycleIso (D.fibre 1) c₁ d h.targetIso hS₁)
  obtain ⟨L⟩ := exists_fullGradedKasparovProductOperatorHomotopy c₀ d hR₀ hP₀
  obtain ⟨K⟩ := exists_fullGradedKasparovProductOperatorHomotopy c₁ d hP₁ hR₁
  exact ⟨((HeterogeneousFullGradedKasparovHomotopy.ofFull L).trans H').trans
    (HeterogeneousFullGradedKasparovHomotopy.ofFull K)⟩

end ChosenEndpoints

section FixedUniverseEndpoints

variable {E G : Type uE}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]
  (c₀ : GradedKasparovCycle α β δA δB E) (c₁ : GradedKasparovCycle α β δA δB G)

/-- A genuine first-input full homotopy carries any specified endpoint
products to one actual full witness. The interior interval product and its
two fibre identifications are constructed before endpoint uniqueness is
used; the witnesses concatenate through the actual matched module. -/
theorem exists_fullGradedKasparovFirstInputProductHomotopy_of_full
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (h : FullGradedKasparovHomotopy (BundledGradedKasparovCycle.of c₀)
      (BundledGradedKasparovCycle.of c₁))
    {R₀ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    {R₁ : AdjointableMap C (InteriorModuleTensor (E := G) d.representation)
      (InteriorModuleTensor (E := G) d.representation)}
    (hR₀ : IsGradedKasparovProductOperator c₀ d R₀)
    (hR₁ : IsGradedKasparovProductOperator c₁ d R₁) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c₀ d R₀ hR₀.cycleConditions))
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c₁ d R₁ hR₁.cycleConditions))) := by
  obtain ⟨H⟩ := exists_fullGradedKasparovFirstInputProductHomotopy d c₀ c₁
    (HeterogeneousFullGradedKasparovHomotopy.ofFull h) hR₀ hR₁
  exact ⟨H.toFull⟩

end FixedUniverseEndpoints
end BC4lean.KKTheory
