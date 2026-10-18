import BC4lean.StarHomotopy
import BC4lean.GradedKasparovIntervalSectionsCycle
import BC4lean.GradedKasparovSourcePullbackClass

/-! # Actual source-algebra homotopies give full Kasparov homotopies

A point-norm homotopy is bundled as a homomorphism to the continuous
interval algebra. Pulling the genuine continuous-section cycle back along
this homomorphism supplies one full interval witness. Its endpoint
identifications use the completed section fibres and whole-cycle unitaries.
-/

noncomputable section
universe uΓ uA uB uC uE

namespace BC4lean.OperatorKTheory.StarHomotopy

variable {A : Type uA} {B : Type uB}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {f₀ f₁ : A →⋆ₙₐ[ℂ] B}

/-- A point-norm homotopy, viewed as an actual interval-algebra map. -/
def continuousSectionsHom (h : StarHomotopy f₀ f₁) : A →⋆ₙₐ[ℂ] C(unitInterval, B) where
  toFun a := ⟨fun t => h.toFun t a, h.continuous_apply a⟩
  map_zero' := by ext t; exact map_zero (h.toFun t)
  map_add' a b := by ext t; exact map_add (h.toFun t) a b
  map_mul' a b := by ext t; exact map_mul (h.toFun t) a b
  map_smul' z a := by ext t; exact map_smul (h.toFun t) z a
  map_star' a := by ext t; exact map_star (h.toFun t) a

@[simp] theorem continuousSectionsHom_apply (h : StarHomotopy f₀ f₁)
    (a : A) (t : unitInterval) : h.continuousSectionsHom a t = h.toFun t a := rfl

end BC4lean.OperatorKTheory.StarHomotopy

namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

attribute [local instance]
  GradedMatrixMoritaSectionRepresentation.sourceSpectralOrder
  GradedMatrixMoritaSectionRepresentation.sourceSpectralOrderedRing

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  {f₀ f₁ : A →⋆ₙₐ[ℂ] B}
  (hα : α.PreservesGrading δA) (h : StarHomotopy f₀ f₁)
  (hact : ∀ t g a, h.toFun t (α.automorphism g a) = β.automorphism g (h.toFun t a))
  (hgrade : ∀ t a, h.toFun t (δA.automorphism a) = δB.automorphism (h.toFun t a))

include hact in
theorem sourceHomotopy_sections_action (g : Γ) (a : A) :
    h.continuousSectionsHom (α.automorphism g a) =
      (β.continuousSections (X := unitInterval)).automorphism g (h.continuousSectionsHom a) := by
  ext t
  exact hact t g a

include hgrade in
theorem sourceHomotopy_sections_grading (a : A) :
    h.continuousSectionsHom (δA.automorphism a) =
      δB.continuousSections.automorphism (h.continuousSectionsHom a) := by
  ext t
  exact hgrade t a

section Raw
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Cᵐᵒᵖ E]
  [CStarModule Cᵐᵒᵖ E] [CompleteSpace E]

/-- Evaluation of the actual section cycle after source pullback agrees
with pointwise source pullback, by a whole-cycle unitary. -/
def GradedKasparovCycle.sourceHomotopyFibreIso
    (c : GradedKasparovCycle β γ δB δC E) (t : unitInterval) :
    GradedKasparovCycleIso
      (((c.continuousSections (X := unitInterval)).sourcePullback α δA hα
        h.continuousSectionsHom (sourceHomotopy_sections_action h hact)
        (sourceHomotopy_sections_grading h hgrade)).fibre t)
      (c.sourcePullback α δA hα (h.toFun t) (hact t) (hgrade t)) :=
  ((c.continuousSections (X := unitInterval)).sourcePullbackFibreIso α δA hα
    h.continuousSectionsHom (sourceHomotopy_sections_action h hact)
    (sourceHomotopy_sections_grading h hgrade) t).trans
    (((c.continuousSectionsFibreIso t).sourcePullback α δA hα h.continuousSectionsHom
      (sourceHomotopy_sections_action h hact) (sourceHomotopy_sections_grading h hgrade)).trans
      { moduleEquiv := HilbertModuleEquiv.refl
        grading_intertwine _ := rfl
        action_intertwine _ _ := rfl
        representation_intertwine _ _ := rfl
        operator_intertwine _ := rfl })

end Raw

/-- A genuine point-norm, equivariant, grading-preserving source homotopy
produces one actual full interval Kasparov homotopy. -/
def BundledGradedKasparovCycle.sourcePullbackHomotopy
    (c : BundledGradedKasparovCycle.{uΓ,uB,uC,uE} β γ δB δC)
    (hact₀ : ∀ g a, f₀ (α.automorphism g a) = β.automorphism g (f₀ a))
    (hact₁ : ∀ g a, f₁ (α.automorphism g a) = β.automorphism g (f₁ a))
    (hgrade₀ : ∀ a, f₀ (δA.automorphism a) = δB.automorphism (f₀ a))
    (hgrade₁ : ∀ a, f₁ (δA.automorphism a) = δB.automorphism (f₁ a)) :
    FullGradedKasparovHomotopy
      (c.sourcePullback α δA hα f₀ hact₀ hgrade₀)
      (c.sourcePullback α δA hα f₁ hact₁ hgrade₁) where
  intervalCycle := .of ((c.cycle.continuousSections (X := unitInterval)).sourcePullback
    α δA hα h.continuousSectionsHom (sourceHomotopy_sections_action h hact)
    (sourceHomotopy_sections_grading h hgrade))
  sourceIso := (c.cycle.sourceHomotopyFibreIso hα h hact hgrade 0).trans
    { moduleEquiv := HilbertModuleEquiv.refl
      grading_intertwine _ := rfl
      action_intertwine _ _ := rfl
      representation_intertwine a x := by
        change c.cycle.representation (h.toFun 0 a) x = c.cycle.representation (f₀ a) x
        rw [h.source]
      operator_intertwine _ := rfl }
  targetIso := (c.cycle.sourceHomotopyFibreIso hα h hact hgrade 1).trans
    { moduleEquiv := HilbertModuleEquiv.refl
      grading_intertwine _ := rfl
      action_intertwine _ _ := rfl
      representation_intertwine a x := by
        change c.cycle.representation (h.toFun 1 a) x = c.cycle.representation (f₁ a) x
        rw [h.target]
      operator_intertwine _ := rfl }

variable [TopologicalSpace.SeparableSpace C]

include h hact hgrade in
/-- Homotopic source maps act equally on the actual full graded quotient. -/
theorem GradedKasparovHomotopyClass.sourcePullback_homotopy
    (hact₀ : ∀ g a, f₀ (α.automorphism g a) = β.automorphism g (f₀ a))
    (hact₁ : ∀ g a, f₁ (α.automorphism g a) = β.automorphism g (f₁ a))
    (hgrade₀ : ∀ a, f₀ (δA.automorphism a) = δB.automorphism (f₀ a))
    (hgrade₁ : ∀ a, f₁ (δA.automorphism a) = δB.automorphism (f₁ a))
    (x : GradedKasparovHomotopyClass.{uΓ,uB,uC,uE} β γ δB δC) :
    GradedKasparovHomotopyClass.sourcePullback α δA hα f₀ hact₀ hgrade₀ x =
      GradedKasparovHomotopyClass.sourcePullback α δA hα f₁ hact₁ hgrade₁ x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact GradedKasparovHomotopyClass.mk_eq_of_full
    (c.sourcePullbackHomotopy hα h hact hgrade hact₀ hact₁ hgrade₀ hgrade₁)

end BC4lean.KKTheory
