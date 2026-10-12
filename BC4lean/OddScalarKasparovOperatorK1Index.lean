import BC4lean.OddScalarKasparovSupportClass
import BC4lean.OddFredholmStandardStabilization
import BC4lean.GroupShrinkOddHomotopy

/-! # Actual operator K1 index values for arbitrary scalar odd cycles

The actual range of the possibly degenerate scalar representation is used.
Its proved supported normalization supplies a selfadjoint global Fredholm
operator, and genuine standard-module absorption supplies the finite
exponential index. The constructed standard cycle has the original actual
full odd class. Quotient descent of these index values is a separate theorem.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory

variable {B : Type uB} {E : Type uE} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace B]

namespace OddKasparovCycle

variable (c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
  (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B) E)

def scalarSupportFredholmSelfAdjoint : selfAdjoint (AdjointableMap B
    (ProjectionModule c.scalarSupportProjection) (ProjectionModule c.scalarSupportProjection)) :=
  ⟨c.scalarSupportNormalizedCycle.operator, c.scalarSupportNormalizedCycle_selfadjoint⟩

def scalarSupportCanonicalFredholmCycle :=
  oddKTheoryScalarFredholmCycle (Γ := PUnit.{uΓ + 1}) c.scalarSupportNormalizedCycle.countablyGenerated
    c.scalarSupportFredholmSelfAdjoint c.scalarSupportFredholmSelfAdjoint.property
    c.scalarSupportNormalizedCycle_square_isModuleCompact

/-- At the actual trivial group every supported normalized odd scalar cycle
is exactly isomorphic to its canonical genuine scalar Fredholm cycle. -/
def scalarSupportCanonicalFredholmCycleIso :
    OddKasparovCycleIso c.scalarSupportNormalizedCycle c.scalarSupportCanonicalFredholmCycle where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine g x := by
    have hg : g = 1 := Subsingleton.elim g 1
    subst g
    change c.scalarSupportNormalizedCycle.groupAction.action (1 : PUnit.{uΓ + 1}) x = x
    exact c.scalarSupportNormalizedCycle.groupAction.one_apply x
  representation_intertwine z x := by
    change c.scalarSupportRepresentation z x = scalarModuleRepresentation z x
    simp only [c.scalarSupportRepresentation_apply, scalarModuleRepresentation_apply]
  operator_intertwine _ := rfl

/-- The actual whole standard cycle associated to an arbitrary odd scalar
cycle, including a degenerate original scalar representation. -/
def scalarStandardFredholmCycle :=
  oddFredholmStandardStabilizedCycle (Γ := PUnit.{uΓ + 1}) c.scalarSupportNormalizedCycle.countablyGenerated
    c.scalarSupportFredholmSelfAdjoint c.scalarSupportNormalizedCycle_square_isModuleCompact

/-- A genuine actual OperatorK1 value for every original odd scalar cycle.
No nondegeneracy or unital representation assumption occurs. -/
def operatorK1Index : OperatorKTheory.OperatorK1 B :=
  oddFredholmStabilizedIndex c.scalarSupportNormalizedCycle.countablyGenerated
    c.scalarSupportFredholmSelfAdjoint c.scalarSupportNormalizedCycle_square_isModuleCompact

/-- For independent coefficient and module universes, the whole standard
cycle class is transported to the original module universe by the genuine
full-homotopy shrink map, whose small-model proof uses countable generation. -/
theorem scalarStandardFredholmCycle_shrink_class :
    OddKK.shrink (OddKK.mk (BundledOddKasparovCycle.of c.scalarStandardFredholmCycle)) =
      OddKK.mk (BundledOddKasparovCycle.of c) := by
  let s := BundledOddKasparovCycle.of c.scalarStandardFredholmCycle
  let q := BundledOddKasparovCycle.of c.scalarSupportCanonicalFredholmCycle
  let su := BundledOddKasparovCycle.of
    ((c.scalarStandardFredholmCycle).ulift :
      OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B)
        (ULift.{uE} (StandardCountableHilbertModule B)))
  let qu := BundledOddKasparovCycle.of
    ((c.scalarSupportCanonicalFredholmCycle).ulift :
      OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B)
        (ULift.{uB} (ProjectionModule c.scalarSupportProjection)))
  let ss := (s.shrink : BundledOddKasparovCycle.{uΓ, 0, uB, uE}
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B))
  let sus := (su.shrink : BundledOddKasparovCycle.{uΓ, 0, uB, uE}
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B))
  let qus := (qu.shrink : BundledOddKasparovCycle.{uΓ, 0, uB, uE}
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B))
  have hsIso : OddKasparovCycleIso ss.cycle sus.cycle :=
    (s.shrinkIso : OddKasparovCycleIso s.cycle ss.cycle).symm.trans
      ((c.scalarStandardFredholmCycle.uliftIso : OddKasparovCycleIso s.cycle su.cycle).trans
        (su.shrinkIso : OddKasparovCycleIso su.cycle sus.cycle))
  have hqIso : OddKasparovCycleIso qus.cycle q.cycle :=
    (qu.shrinkIso : OddKasparovCycleIso qu.cycle qus.cycle).symm.trans
      (c.scalarSupportCanonicalFredholmCycle.uliftIso :
        OddKasparovCycleIso q.cycle qu.cycle).symm
  have hclass : OddKK.mk su = OddKK.mk qu :=
    oddFredholmStandardStabilizedCycle_class (Γ := PUnit.{uΓ + 1})
      c.scalarSupportNormalizedCycle.countablyGenerated c.scalarSupportFredholmSelfAdjoint
      c.scalarSupportNormalizedCycle_square_isModuleCompact
  change OddKK.shrink (OddKK.mk s) = OddKK.mk (BundledOddKasparovCycle.of c)
  calc
    _ = OddKK.shrink (OddKK.mk su) := OddKK.mk_eq_of_iso hsIso
    _ = OddKK.shrink (OddKK.mk qu) := congrArg
      (OddKK.shrink :
        OddKK.{uΓ, 0, uB, max uB uE}
          (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B) →
        OddKK.{uΓ, 0, uB, uE}
          (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B)) hclass
    _ = OddKK.mk q := OddKK.mk_eq_of_iso hqIso
    _ = OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportNormalizedCycle) :=
      OddKK.mk_eq_of_iso c.scalarSupportCanonicalFredholmCycleIso.symm
    _ = _ := c.scalarSupportNormalized_class.symm

end OddKasparovCycle

namespace OddKasparovCycle

variable {E₀ : Type uB} [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [SMul Bᵐᵒᵖ E₀] [CStarModule Bᵐᵒᵖ E₀] [CompleteSpace E₀]
  (c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B) E₀)

/-- Compatibility in the coefficient module universe, used by the existing
ordinary K1 inverse. The preceding shrink-class theorem is the general result. -/
theorem scalarStandardFredholmCycle_class :
    OddKK.mk (BundledOddKasparovCycle.of c.scalarStandardFredholmCycle) =
      OddKK.mk (BundledOddKasparovCycle.of c) := by
  let s := BundledOddKasparovCycle.of c.scalarStandardFredholmCycle
  let ss := (s.shrink : BundledOddKasparovCycle.{uΓ, 0, uB, uB}
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit.{uΓ + 1} B))
  change OddKK.mk s = OddKK.mk (BundledOddKasparovCycle.of c)
  calc
    _ = OddKK.mk ss := OddKK.mk_eq_of_iso
      (s.shrinkIso : OddKasparovCycleIso s.cycle ss.cycle)
    _ = _ := c.scalarStandardFredholmCycle_shrink_class

end OddKasparovCycle
end BC4lean.KKTheory
