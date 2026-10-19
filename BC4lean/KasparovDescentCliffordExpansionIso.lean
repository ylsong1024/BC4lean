import BC4lean.KasparovDescentCliffordPair
import BC4lean.KasparovDescentPairCoefficientEquiv
import BC4lean.KasparovDescentEvenGradedCoherence
import BC4lean.CliffordParityCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Whole-cycle compatibility of actual descent with odd Clifford expansion



Both sides are actual raw cycle constructions. Source regrading uses the
proved trivial crossed-grading equality, coefficient change uses the actual
crossed-pair star equivalence, and the complete module unitary is the
concrete pair tensor map. Grading, action, completed source representation,
and the signed Fredholm operator are intertwined by that same unitary.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B E : Type*} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)

/-- Descend the actual original Clifford-expanded odd cycle, identify only
the provably trivial source grading, then apply the actual pair coefficient iso. -/
def descendedCliffordExpansion (c : OddKasparovCycle α β E) :=
  ((gradedCycle (cliffordCoefficientAction β) α c.cliffordExpansion).regrade
    (reducedCrossedProductGrading_trivial α) rfl).changeCoefficients
      (KasparovDescentPairCoefficientEquiv.equiv β)

private theorem cliffordExpansionDescentIso_grading_aux
    (c : OddKasparovCycle α β E) (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedCliffordExpansion β α c).grading.grading z) =
      (oddCycle β α c).cliffordExpansion.grading.grading (pairModuleEquiv (E := E) β z) := by
  let w : Module (cliffordCoefficientAction β) (CliffordPairModule B E) :=
    coefficientChangedToOriginal (ReducedCrossedProductPair.equiv β) z
  have h₁ := congrArg
    (fun v : Module (cliffordCoefficientAction β) (CliffordPairModule B E) =>
      pairModuleMap (E := E) β v)
    (GradedKasparovCycle.regrade_grading_apply
      (Γ := Unit) (A := ReducedCrossedProduct α)
      (B := ReducedCrossedProduct (cliffordCoefficientAction β))
      (E := Module (cliffordCoefficientAction β) (CliffordPairModule B E))
      (gradedCycle (E := CliffordPairModule B E) (cliffordCoefficientAction β) α
        c.cliffordExpansion)
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := A) α) rfl w)
  have h₂ := pairModuleMap_grading (Γ := Γ) (B := B) (E := E) β w
  exact h₁.trans h₂

private theorem cliffordExpansionDescentIso_action_aux
    (c : OddKasparovCycle α β E) (g : Unit) (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedCliffordExpansion β α c).groupAction.action g z) =
      (oddCycle β α c).cliffordExpansion.groupAction.action g (pairModuleEquiv (E := E) β z) := by
  have hg : g = (1 : Unit) := Subsingleton.elim _ _
  have hsource : (descendedCliffordExpansion β α c).groupAction.action g z = z :=
    (congrArg
      (fun k : Unit => (descendedCliffordExpansion β α c).groupAction.action k z) hg).trans
      (EquivariantHilbertModule.one_apply
        (descendedCliffordExpansion β α c).groupAction z)
  have htarget :
      (oddCycle β α c).cliffordExpansion.groupAction.action g (pairModuleEquiv (E := E) β z) =
        pairModuleEquiv (E := E) β z :=
    (congrArg
      (fun k : Unit => (oddCycle β α c).cliffordExpansion.groupAction.action k
        (pairModuleEquiv (E := E) β z)) hg).trans
      (EquivariantHilbertModule.one_apply
        (oddCycle β α c).cliffordExpansion.groupAction (pairModuleEquiv (E := E) β z))
  exact (congrArg
    (fun v : PairChangedModule (E := E) β => pairModuleEquiv (E := E) β v) hsource).trans
    htarget.symm

private theorem cliffordExpansionDescentIso_representation_aux
    (c : OddKasparovCycle α β E) (a : ReducedCrossedProduct α)
    (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedCliffordExpansion β α c).representation a z) =
      (oddCycle β α c).cliffordExpansion.representation a (pairModuleEquiv (E := E) β z) := by
  let w : Module (cliffordCoefficientAction β) (CliffordPairModule B E) :=
    coefficientChangedToOriginal (ReducedCrossedProductPair.equiv β) z
  have h₁ := congrArg
    (fun ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct (cliffordCoefficientAction β))
        (Module (cliffordCoefficientAction β) (CliffordPairModule B E))
        (Module (cliffordCoefficientAction β) (CliffordPairModule B E)) =>
      pairModuleMap (E := E) β (ρ a w))
    (GradedKasparovCycle.regrade_representation
      (Γ := Unit) (A := ReducedCrossedProduct α)
      (B := ReducedCrossedProduct (cliffordCoefficientAction β))
      (E := Module (cliffordCoefficientAction β) (CliffordPairModule B E))
      (gradedCycle (E := CliffordPairModule B E) (cliffordCoefficientAction β) α
        c.cliffordExpansion)
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := A) α) rfl)
  have h₂ := pairModuleMap_reducedSourceRepresentation (Γ := Γ) (A := A) (B := B)
    (E := E) β α c.groupAction c.representation c.representation_equivariant a w
  exact h₁.trans h₂

private theorem cliffordExpansionDescentIso_operator_aux
    (c : OddKasparovCycle α β E) (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedCliffordExpansion β α c).operator z) =
      (oddCycle β α c).cliffordExpansion.operator (pairModuleEquiv (E := E) β z) := by
  let w : Module (cliffordCoefficientAction β) (CliffordPairModule B E) :=
    coefficientChangedToOriginal (ReducedCrossedProductPair.equiv β) z
  have h₁ := congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct (cliffordCoefficientAction β))
      (Module (cliffordCoefficientAction β) (CliffordPairModule B E))
      (Module (cliffordCoefficientAction β) (CliffordPairModule B E)) =>
      pairModuleMap (E := E) β (T w))
    (GradedKasparovCycle.regrade_operator
      (Γ := Unit) (A := ReducedCrossedProduct α)
      (B := ReducedCrossedProduct (cliffordCoefficientAction β))
      (E := Module (cliffordCoefficientAction β) (CliffordPairModule B E))
      (gradedCycle (E := CliffordPairModule B E) (cliffordCoefficientAction β) α
        c.cliffordExpansion)
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := A) α) rfl)
  have h₂ := pairModuleMap_operator (Γ := Γ) (B := B) (E := E) β
    c.operator (-c.operator) w
  have h₃ := congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
      cliffordPairMap (operatorHom β E c.operator) T (pairModuleMap (E := E) β w))
    (map_neg (operatorHom β E) c.operator)
  exact h₁.trans (h₂.trans h₃)

/-- The genuine full completed unitary proves raw Clifford/descent coherence. -/
def cliffordExpansionDescentIso (c : OddKasparovCycle α β E) :
    GradedKasparovCycleIso (descendedCliffordExpansion β α c)
      (oddCycle β α c).cliffordExpansion where
  moduleEquiv := pairModuleEquiv β
  grading_intertwine z :=
    cliffordExpansionDescentIso_grading_aux (E := E) β α c z
  action_intertwine g z :=
    cliffordExpansionDescentIso_action_aux (E := E) β α c g z
  representation_intertwine a z :=
    cliffordExpansionDescentIso_representation_aux (E := E) β α c a z
  operator_intertwine z :=
    cliffordExpansionDescentIso_operator_aux (E := E) β α c z

end BC4lean.KKTheory.KasparovDescent
