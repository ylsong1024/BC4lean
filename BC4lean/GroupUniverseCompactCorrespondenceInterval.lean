import BC4lean.GradedMatrixMoritaFibreTensorCompatibility
import BC4lean.GradedMatrixMoritaFirstTensorUnitary
import BC4lean.FullGradedKasparovHomotopy

/-! # Independent-universe whole interval transport by a compact correspondence

The actual module universe is max(uE,uF). The interval module is the
actual completed tensor with continuous sections of the correspondence. Both endpoint identifications compose the proved
fibre/tensor unitary with the actual first-factor cycle unitary.
-/

noncomputable section
universe uΓ uA uB uC uE uF
namespace BC4lean.KKTheory.GroupUniverseCompactCorrespondenceInterval
open scoped InnerProductSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}
  (η : CStarAlgebraAction Γ C) (δC : CStarGrading C)
  (K : GradedHilbertModule δC F) (V : EquivariantHilbertModule η F)
  (hη : η.PreservesGrading δC) (hV : V.PreservesGrading K)
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (hφJ : ModuleTensorRepresentationGraded (δB := δB) φ K)
  (hφU : ModuleTensorRepresentationEquivariant φ β V)
  (hφcompact : ∀ b, IsModuleCompact (φ b)) (hF : IsCountablyGeneratedModule C F)

def tensor (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    BundledGradedKasparovCycle.{uΓ,uA,uC,max uE uF} α η δA δC :=
  .of (GradedMatrixMoritaCycle.tensorWithCompactLeftAction c.cycle η δC K V hη hV
    φ hφJ hφU hφcompact hF)

def intervalTensor
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (β.continuousSections (X := unitInterval)) δA (δB.continuousSections (X := unitInterval))) :
    BundledGradedKasparovCycle.{uΓ,uA,uC,max uE uF} α (η.continuousSections (X := unitInterval)) δA (δC.continuousSections (X := unitInterval)) :=
  .of (GradedMatrixMoritaCycle.tensorWithCompactLeftAction c.cycle (η.continuousSections (X := unitInterval))
    (δC.continuousSections (X := unitInterval)) (K.gradedContinuousSections (X := unitInterval)) (V.continuousSections (X := unitInterval))
    (CStarAlgebraAction.preservesGrading_continuousSections (X := unitInterval) hη)
    (GradedMatrixMoritaSectionRepresentation.action_preservesGrading (X := unitInterval) K V hV)
    (GradedMatrixMoritaSectionRepresentation.leftAction (X := unitInterval) φ)
    (GradedMatrixMoritaSectionRepresentation.leftAction_graded (X := unitInterval) φ K hφJ)
    (GradedMatrixMoritaSectionRepresentation.leftAction_equivariant (X := unitInterval) φ V hφU)
    (GradedMatrixMoritaSectionRepresentation.leftAction_compact (X := unitInterval) φ hφcompact)
    (continuousSection_isCountablyGenerated (X := unitInterval) hF))

set_option maxHeartbeats 1200000 in
/-- The same actual unitary intertwines all four evaluated cycle data. -/
def fibreIso
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (β.continuousSections (X := unitInterval)) δA (δB.continuousSections (X := unitInterval)))
    (t : unitInterval) : GradedKasparovCycleIso
      ((intervalTensor η δC K V hη hV φ hφJ hφU hφcompact hF c).cycle.fibre t)
      (GradedMatrixMoritaCycle.tensorWithCompactLeftAction (c.cycle.fibre t)
        η δC K V hη hV φ hφJ hφU hφcompact hF) where
  moduleEquiv := GradedMatrixMoritaFibreTensor.hilbertEquiv φ t
  grading_intertwine z := GradedMatrixMoritaFibreTensor.hilbertEquiv_grading φ t c.cycle.grading K hφJ z
  action_intertwine g z := GradedMatrixMoritaFibreTensor.hilbertEquiv_action φ t c.cycle.groupAction V hφU g z
  representation_intertwine a z := GradedMatrixMoritaFibreTensor.hilbertEquiv_operator φ t
    (c.cycle.representation a) z
  operator_intertwine z := GradedMatrixMoritaFibreTensor.hilbertEquiv_operator φ t c.cycle.operator z

/-- A single genuine interval witness produces a single genuine transported witness. -/
def full {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) : FullGradedKasparovHomotopy
      (tensor η δC K V hη hV φ hφJ hφU hφcompact hF c)
      (tensor η δC K V hη hV φ hφJ hφU hφcompact hF d) where
  intervalCycle := intervalTensor η δC K V hη hV φ hφJ hφU hφcompact hF h.intervalCycle
  sourceIso := (fibreIso η δC K V hη hV φ hφJ hφU hφcompact hF h.intervalCycle 0).trans
    (GradedMatrixMoritaFirstTensorUnitary.cycleIso φ η δC K V hη hV hφJ hφU hφcompact hF h.sourceIso)
  targetIso := (fibreIso η δC K V hη hV φ hφJ hφU hφcompact hF h.intervalCycle 1).trans
    (GradedMatrixMoritaFirstTensorUnitary.cycleIso φ η δC K V hη hV hφJ hφU hφcompact hF h.targetIso)

end BC4lean.KKTheory.GroupUniverseCompactCorrespondenceInterval
