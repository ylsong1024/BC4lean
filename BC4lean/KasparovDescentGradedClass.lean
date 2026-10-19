import BC4lean.KasparovDescentGradedFullHomotopy
import BC4lean.KasparovDescentGradedDirectSum
import BC4lean.GradedKasparovSourcePullbackClass
import Mathlib.Algebra.Group.Hom.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual fully graded descent on the genuine full-homotopy quotient

The construction imports the concrete graded raw cycle, whole-cycle
unitaries, arbitrary full interval transport and completed
tensor/direct-sum unitary.

The ambient action/grading compatibility proofs fix the two target induced
crossed-product gradings independently of each representative. The raw
cycle's stored compatibility proofs inhabit those same propositions, so
proof irrelevance supplies definitional agreement without a module or
grading transport. The actual full-witness relation is transported directly.

The general graded quotient presently has its actual direct-sum `Add`
structure. The bundled endpoint below is therefore an `AddHom`, using only
the proved direct-sum law. No monoid or group structure, zero law, product
compatibility, Clifford comparison, or parity comparison is assumed here.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.KasparovDescent

open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

variable (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
  {δA : CStarGrading A} {δB : CStarGrading B}
  (hα : α.PreservesGrading δA) (hβ : β.PreservesGrading δB)

/-- The concrete descended cycle has a fixed target type, using the specified
ambient compatibility proofs and the actual enlarged carrier universe. -/
def bundledGradedCycleFixed
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    BundledGradedKasparovCycle.{0,max uΓ uA,max uΓ uB,max uE (max uΓ uB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (reducedCrossedProductGrading α δA hα)
      (reducedCrossedProductGrading β δB hβ) :=
  bundledGradedCycle β α c

/-- The constructed arbitrary interval witness has the same fixed target
gradings; it does not replace the arbitrary interval carrier by a path. -/
def gradedFullHomotopyFixed
    {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB}
    (H : FullGradedKasparovHomotopy c d) :
    FullGradedKasparovHomotopy (bundledGradedCycleFixed β α hα hβ c)
      (bundledGradedCycleFixed β α hα hβ d) :=
  gradedFullHomotopy β α H

/-- The actual whole-cycle direct-sum unitary, expressed at the fixed target
gradings needed for a well-typed quotient map. -/
def bundledGradedDirectSumIso
    (c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    (bundledGradedCycleFixed β α hα hβ (c.directSum d)).Iso
      ((bundledGradedCycleFixed β α hα hβ c).directSum
        (bundledGradedCycleFixed β α hα hβ d)) :=
  gradedDirectSumIso β α c.cycle d.cycle

/-- The actual fully graded class map, lifted through the genuine full
arbitrary-module witness relation. Its codomain retains the actual induced
crossed gradings and the enlarged tensor-module universe. -/
def gradedClass : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB →
    GradedKasparovHomotopyClass.{0,max uΓ uA,max uΓ uB,max uE (max uΓ uB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (reducedCrossedProductGrading α δA hα)
      (reducedCrossedProductGrading β δB hβ) :=
  Quotient.lift
    (fun c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB =>
      GradedKasparovHomotopyClass.mk (bundledGradedCycleFixed β α hα hβ c))
    (by
      intro c d h
      obtain ⟨H⟩ := h
      exact GradedKasparovHomotopyClass.mk_eq_of_full
        (gradedFullHomotopyFixed β α hα hβ H))

@[simp] theorem gradedClass_mk
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    gradedClass β α hα hβ (GradedKasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (bundledGradedCycleFixed β α hα hβ c) := rfl

/-- Additivity comes from the actual graded tensor/distributivity unitary. -/
theorem gradedClass_add
    (x y : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) :
    gradedClass β α hα hβ (x + y) =
      gradedClass β α hα hβ x + gradedClass β α hα hβ y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  change GradedKasparovHomotopyClass.mk
      (bundledGradedCycleFixed β α hα hβ (c.directSum d)) =
    GradedKasparovHomotopyClass.mk (bundledGradedCycleFixed β α hα hβ c) +
      GradedKasparovHomotopyClass.mk (bundledGradedCycleFixed β α hα hβ d)
  rw [← GradedKasparovHomotopyClass.mk_directSum]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (bundledGradedDirectSumIso β α hα hβ c d)

/-- Bundle the proved additive map using precisely the additive structures
currently established for general graded full-homotopy quotients. -/
def gradedClassHom : AddHom
    (GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB)
    (GradedKasparovHomotopyClass.{0,max uΓ uA,max uΓ uB,max uE (max uΓ uB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (reducedCrossedProductGrading α δA hα)
      (reducedCrossedProductGrading β δB hβ)) where
  toFun := gradedClass β α hα hβ
  map_add' := gradedClass_add β α hα hβ

@[simp] theorem gradedClassHom_apply
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) :
    gradedClassHom β α hα hβ x = gradedClass β α hα hβ x := rfl

end BC4lean.KKTheory.KasparovDescent
