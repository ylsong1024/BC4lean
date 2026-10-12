import BC4lean.GradedKasparovSecondFibreProduct
import BC4lean.KasparovProductExistence
import BC4lean.FullGradedKasparovHomotopy
import BC4lean.FullGradedKasparovHomotopyEquivalence
import BC4lean.GradedKasparovSecondIsoProduct
import BC4lean.KasparovProductOperatorUniqueness
import BC4lean.HeterogeneousFullGradedKasparovHomotopy
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # An actual product homotopy for an arbitrary second interval module

Generic product existence is applied to the actual interval correspondence.
The resulting complete tensor module is the interval witness itself. Its
two true evaluated fibres are products by the four-law and positive-lift
fibre descent theorem, and are identified by the constructed tensor fibre
unitaries. No interpolation of arbitrary module representations is used.
-/

noncomputable section
universe uΓ uA uB uC uE uF uG uM uH
namespace BC4lean.KKTheory
open TopologicalSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC}
  {E : Type uE} {M : Type uM} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(unitInterval, C)ᵐᵒᵖ M]
  [CStarModule C(unitInterval, C)ᵐᵒᵖ M] [CompleteSpace E] [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E)
  (d : GradedKasparovCycle β (γ.continuousSections (X := unitInterval))
    δB δC.continuousSections M)

/-- The actual interval product supplies endpoint products and a single
full interval witness between them on the actual tensor fibres. -/
theorem exists_fullSecondFibreProductHomotopy
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ] :
    ∃ R₀ : AdjointableMap C (InteriorModuleTensor (E := E) (d.fibre 0).representation)
        (InteriorModuleTensor (E := E) (d.fibre 0).representation),
      ∃ R₁ : AdjointableMap C (InteriorModuleTensor (E := E) (d.fibre 1).representation)
          (InteriorModuleTensor (E := E) (d.fibre 1).representation),
        ∃ hR₀ : IsGradedKasparovProductOperator c (d.fibre 0) R₀,
          ∃ hR₁ : IsGradedKasparovProductOperator c (d.fibre 1) R₁,
            Nonempty (FullGradedKasparovHomotopy
              (BundledGradedKasparovCycle.of
                (gradedKasparovTensorCycleOfConditions c (d.fibre 0) R₀ hR₀.cycleConditions))
              (BundledGradedKasparovCycle.of
                (gradedKasparovTensorCycleOfConditions c (d.fibre 1) R₁ hR₁.cycleConditions))) := by
  obtain ⟨R, hR⟩ := exists_actualGradedKasparovProductOperator c d
  let R₀ := gradedKasparovSecondFibreProductOperator (E := E) d 0 R
  let R₁ := gradedKasparovSecondFibreProductOperator (E := E) d 1 R
  let hR₀ := gradedKasparovSecondFibreProduct_isProduct c d 0 hR
  let hR₁ := gradedKasparovSecondFibreProduct_isProduct c d 1 hR
  refine ⟨R₀, R₁, hR₀, hR₁, ⟨?_⟩⟩
  exact {
    intervalCycle := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions)
    sourceIso := gradedKasparovSecondFibreProduct_cycleIso c d 0 hR
    targetIso := gradedKasparovSecondFibreProduct_cycleIso c d 1 hR }

section ChosenEndpoints

variable {F : Type uF} {G : Type uG}
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G] [CompleteSpace G]
  (d₀ : GradedKasparovCycle β γ δB δC F) (d₁ : GradedKasparovCycle β γ δB δC G)

/-- Every genuine second-input full homotopy, with independent endpoint
and interval carrier universes, carries any two specified
endpoint products to one actual full homotopy. The interval product is
constructed, its fibre products are transported by the given endpoint
unitaries, and actual uniqueness and matched-module gluing finish the
endpoint identifications. -/
theorem exists_fullGradedKasparovSecondInputProductHomotopy
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (h : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uB, uC, uF, uG, uH} (BundledGradedKasparovCycle.of d₀)
      (BundledGradedKasparovCycle.of d₁))
    {R₀ : AdjointableMap C (InteriorModuleTensor (E := E) d₀.representation)
      (InteriorModuleTensor (E := E) d₀.representation)}
    {R₁ : AdjointableMap C (InteriorModuleTensor (E := E) d₁.representation)
      (InteriorModuleTensor (E := E) d₁.representation)}
    (hR₀ : IsGradedKasparovProductOperator c d₀ R₀)
    (hR₁ : IsGradedKasparovProductOperator c d₁ R₁) :
    Nonempty (HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uC,
      max uE uF, max uE uG, max (max (max uE uF) uG) uH}
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c d₀ R₀ hR₀.cycleConditions))
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c d₁ R₁ hR₁.cycleConditions))) := by
  let D := h.intervalCycle.cycle
  obtain ⟨S₀, S₁, hS₀, hS₁, ⟨H⟩⟩ := exists_fullSecondFibreProductHomotopy c D
  let P₀ := gradedKasparovSecondIsoProductOperator (D.fibre 0) d₀ h.sourceIso S₀
  let P₁ := gradedKasparovSecondIsoProductOperator (D.fibre 1) d₁ h.targetIso S₁
  have hP₀ : IsGradedKasparovProductOperator c d₀ P₀ :=
    gradedKasparovSecondIsoProduct_isProduct c (D.fibre 0) d₀ h.sourceIso hS₀
  have hP₁ : IsGradedKasparovProductOperator c d₁ P₁ :=
    gradedKasparovSecondIsoProduct_isProduct c (D.fibre 1) d₁ h.targetIso hS₁
  let H' := (HeterogeneousFullGradedKasparovHomotopy.ofFull H).changeEndpoints
    (e := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c d₀ P₀ hP₀.cycleConditions))
    (f := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c d₁ P₁ hP₁.cycleConditions))
    (gradedKasparovSecondIsoProduct_cycleIso c (D.fibre 0) d₀ h.sourceIso hS₀)
    (gradedKasparovSecondIsoProduct_cycleIso c (D.fibre 1) d₁ h.targetIso hS₁)
  obtain ⟨L⟩ := exists_fullGradedKasparovProductOperatorHomotopy c d₀ hR₀ hP₀
  obtain ⟨K⟩ := exists_fullGradedKasparovProductOperatorHomotopy c d₁ hP₁ hR₁
  exact ⟨((HeterogeneousFullGradedKasparovHomotopy.ofFull L).trans H').trans
    (HeterogeneousFullGradedKasparovHomotopy.ofFull K)⟩

end ChosenEndpoints

section FixedUniverseEndpoints

variable {F G : Type uF}
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G] [CompleteSpace G]
  (d₀ : GradedKasparovCycle β γ δB δC F) (d₁ : GradedKasparovCycle β γ δB δC G)

/-- Every genuine second-input full homotopy carries any two specified
endpoint products to one actual full homotopy. The interval product is
constructed, its fibre products are transported by the given endpoint
unitaries, and actual uniqueness and matched-module gluing finish the
endpoint identifications. -/
theorem exists_fullGradedKasparovSecondInputProductHomotopy_of_full
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (h : FullGradedKasparovHomotopy (BundledGradedKasparovCycle.of d₀)
      (BundledGradedKasparovCycle.of d₁))
    {R₀ : AdjointableMap C (InteriorModuleTensor (E := E) d₀.representation)
      (InteriorModuleTensor (E := E) d₀.representation)}
    {R₁ : AdjointableMap C (InteriorModuleTensor (E := E) d₁.representation)
      (InteriorModuleTensor (E := E) d₁.representation)}
    (hR₀ : IsGradedKasparovProductOperator c d₀ R₀)
    (hR₁ : IsGradedKasparovProductOperator c d₁ R₁) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c d₀ R₀ hR₀.cycleConditions))
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c d₁ R₁ hR₁.cycleConditions))) := by
  obtain ⟨H⟩ := exists_fullGradedKasparovSecondInputProductHomotopy c d₀ d₁
    (HeterogeneousFullGradedKasparovHomotopy.ofFull h) hR₀ hR₁
  exact ⟨H.toFull⟩

end FixedUniverseEndpoints
end BC4lean.KKTheory
