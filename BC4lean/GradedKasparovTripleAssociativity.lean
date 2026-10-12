import BC4lean.KasparovTripleTechnicalConstruction
import BC4lean.KasparovProductOperatorUniqueness
import BC4lean.FullGradedKasparovHomotopyEquivalence

/-! # A genuine full associativity witness from the common triple product

The common triple operator is constructed by the actual technical partition
and meets both genuine product criteria. Product uniqueness on the two actual
tensor modules and the associator's whole-cycle unitary are concatenated using
actual matched interval modules. The result is one full interval witness
between the two prescribed iterated products, retaining both endpoint cycles.
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


variable (L : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
  (LeftTensor (E := E) d.representation e.representation))

/-- The arbitrary prescribed left and right iterated products are joined
by one actual full interval homotopy after the analytic adjoint reduction.
The prescribed left product need not be selfadjoint. -/
theorem exists_fullGradedKasparovAssociativityHomotopy_of_selfadjoint_inputs
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D] [Countable Γ]
    (hQproduct : IsGradedKasparovProductOperator c d Q)
    (hTproduct : IsGradedKasparovProductOperator d e T)
    (hLproduct : IsGradedKasparovProductOperator (firstPairCycle c d Q hQ) e L)
    (hRproduct : IsGradedKasparovProductOperator c (secondPairCycle d e T hT) R)
    (hcsa : IsSelfAdjoint c.operator) (hdsa : IsSelfAdjoint d.operator)
    (hesa : IsSelfAdjoint e.operator) (hQsa : IsSelfAdjoint Q)
    (hTsa : IsSelfAdjoint T) (hRsa : IsSelfAdjoint R) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions
        (firstPairCycle c d Q hQ) e L hLproduct.cycleConditions))
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions
        c (secondPairCycle d e T hT) R hRproduct.cycleConditions))) := by
  obtain ⟨P, hPright, hPleft⟩ := exists_actualCommonTripleProduct c d e Q hQ T hT R
    hQproduct hTproduct hRproduct hcsa hdsa hesa hQsa hTsa hRsa
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let c₁₂ := firstPairCycle c d Q hQ
  let c₂₃ := secondPairCycle d e T hT
  let kL := gradedKasparovTensorCycleOfConditions c₁₂ e (Ω.symm.transport P) hPleft.cycleConditions
  let kR := gradedKasparovTensorCycleOfConditions c c₂₃ P hPright.cycleConditions
  let u : GradedKasparovCycleIso kL kR := {
    moduleEquiv := Ω
    grading_intertwine := triple_grading_intertwine c d e Q hQ T hT
    action_intertwine := triple_action_intertwine c d e Q hQ T hT
    representation_intertwine := triple_representation_intertwine c d e Q hQ T hT
    operator_intertwine x := by
      change Ω (Ω.symm.transport P x) = P (Ω x)
      simp only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_symm,
        HilbertModuleEquiv.apply_symm_apply] }
  obtain ⟨HL⟩ := exists_fullGradedKasparovProductOperatorHomotopy c₁₂ e hLproduct hPleft
  obtain ⟨HR⟩ := exists_fullGradedKasparovProductOperatorHomotopy c c₂₃ hPright hRproduct
  let HLeft : FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c₁₂ e L hLproduct.cycleConditions))
      (BundledGradedKasparovCycle.of kL) := HL
  let HMiddle : FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of kL) (BundledGradedKasparovCycle.of kR) :=
    FullGradedKasparovHomotopy.ofIso
      (c := BundledGradedKasparovCycle.of kL)
      (d := BundledGradedKasparovCycle.of kR) u
  let HRight : FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of kR)
      (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c c₂₃ R hRproduct.cycleConditions)) := HR
  exact ⟨(HLeft.trans HMiddle).trans HRight⟩

end BC4lean.KKTheory.KasparovTriple
