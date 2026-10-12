import BC4lean.GradedCompactCorrespondenceCycle
import BC4lean.GroupUniverseProduct

/-! # Actual compact correspondence class products across universes

The completed correspondence module has its actual zero-operator cycle.
The existing whole tensor cycle is its product by the proved full raw
criterion and genuine full uniqueness, with independent algebra and
module universes retained throughout.
-/

noncomputable section
universe uΓ uA uB uC uE uF
namespace BC4lean.KKTheory.GroupUniverseCompactCorrespondenceProduct
variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace F]
  (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (δB : CStarGrading B) (δC : CStarGrading C)
  (K : GradedHilbertModule δC F) (V : EquivariantHilbertModule γ F)
  (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
  (hV : V.PreservesGrading K)
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (hφJ : ModuleTensorRepresentationGraded (δB := δB) φ K)
  (hφU : ModuleTensorRepresentationEquivariant φ β V)
  (hφcompact : ∀ b, IsModuleCompact (φ b)) (hF : IsCountablyGeneratedModule C F)

variable [TopologicalSpace.SeparableSpace C]

def correspondenceClass : GradedKasparovHomotopyClass.{uΓ,uB,uC,uF} β γ δB δC :=
  GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
    (GradedCompactCorrespondenceCycle.cycle β γ δB δC K V hβ hγ hV
      φ hφJ hφU hφcompact hF))

variable {A : Type uA} {E : Type uE} [NonUnitalCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [Countable Γ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}
  (c : GradedKasparovCycle α β δA δB E)

/-- The actual full tensor cycle is right multiplication by the genuine
compact-correspondence class, in the true tensor universe `max uE uF`. -/
theorem tensorClass_eq_product :
    GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (GradedMatrixMoritaCycle.tensorWithCompactLeftAction c γ δC K V hγ hV
        φ hφJ hφU hφcompact hF)) =
    GroupUniverseProduct.product
      (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of c))
      (correspondenceClass β γ δB δC K V hβ hγ hV φ hφJ hφU hφcompact hF) := by
  let k := GradedCompactCorrespondenceCycle.cycle β γ δB δC K V hβ hγ hV
    φ hφJ hφU hφcompact hF
  have h := GradedCompactCorrespondenceCycle.isProduct β γ δB δC K V hβ hγ hV
    φ hφJ hφU hφcompact hF c
  calc
    _ = GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (gradedKasparovTensorCycleOfConditions c k
          (interiorModuleTensorOperator φ c.operator) h.cycleConditions)) :=
      GradedKasparovHomotopyClass.mk_eq_of_iso
        (c := BundledGradedKasparovCycle.of
          (GradedMatrixMoritaCycle.tensorWithCompactLeftAction c γ δC K V hγ hV
            φ hφJ hφU hφcompact hF))
        (d := BundledGradedKasparovCycle.of
          (gradedKasparovTensorCycleOfConditions c k
            (interiorModuleTensorOperator φ c.operator) h.cycleConditions))
        (GradedCompactCorrespondenceCycle.tensorCycleIso β γ δB δC K V hβ hγ hV
          φ hφJ hφU hφcompact hF c)
    _ = _ := (GroupUniverseProduct.product_mk_eq_of_isProduct
      (BundledGradedKasparovCycle.of c) (BundledGradedKasparovCycle.of k) h).symm

end BC4lean.KKTheory.GroupUniverseCompactCorrespondenceProduct
