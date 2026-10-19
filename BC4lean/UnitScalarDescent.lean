import BC4lean.KasparovDescentClass
import BC4lean.NativeEvenSourcePullback
import BC4lean.NativeOddSourcePullback
import BC4lean.OrdinaryScalarCoefficientTensor
import BC4lean.OrdinaryOddCoefficientTensor
import BC4lean.GroupUniverseOrdinaryEven
import BC4lean.GroupUniverseOrdinaryOdd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Scalar descent for the literal Unit group.
Explicit whole-cycle isomorphisms identify coefficient-restricted descent
with ordinary coefficient extension in both parities. -/

noncomputable section
universe uB uE u
namespace BC4lean.KKTheory.UnitScalarDescent
open scoped KasparovDescent ComplexOrder

variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
abbrev scalarAction : CStarAlgebraAction Unit ℂ := CStarAlgebraAction.trivial
abbrev coefficientAction : CStarAlgebraAction Unit B := CStarAlgebraAction.trivial
abbrev scalarInclusion : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct scalarAction :=
  coefficientToReducedCrossed scalarAction
abbrev coefficientInclusion : B →⋆ₙₐ[ℂ]
    ReducedCrossedProduct (coefficientAction (B := B)) :=
  coefficientToReducedCrossed (coefficientAction (B := B))
abbrev descendedScalarAction : CStarAlgebraAction Unit (ReducedCrossedProduct scalarAction) :=
  CStarAlgebraAction.trivial
abbrev descendedCoefficientAction : CStarAlgebraAction Unit
    (ReducedCrossedProduct (coefficientAction (B := B))) := CStarAlgebraAction.trivial

/-- Explicitly typed equivariance of the actual scalar coefficient inclusion. -/
theorem scalarCoefficient_equivariant : ∀ (g : Unit) (a : ℂ),
    scalarInclusion ((scalarAction).automorphism g a) = (descendedScalarAction).automorphism g (scalarInclusion a) := fun _ _ => rfl

section Raw
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Descent restricted to the actual scalar coefficients is precisely the
ordinary scalar coefficient-extension cycle on the actual completed tensor. -/
def evenCoefficientRestrictionIso (c : KasparovCycle scalarAction (coefficientAction (B := B)) E) :
    KasparovCycleIso
      (NativeSourcePullback.evenCycle scalarAction scalarInclusion (fun _ _ => rfl)
        (KasparovDescent.evenCycle (coefficientAction (B := B)) scalarAction c))
      (c.scalarCoefficientTensor (coefficientInclusion (B := B))) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine a z := by
    change KasparovDescent.reducedSourceRepresentation (coefficientAction (B := B)) E scalarAction c.groupAction
        c.representation c.representation_equivariant (scalarInclusion a) z =
      KasparovDescent.sourceRepresentation (coefficientAction (B := B)) E c.representation a z
    exact congrArg
      (fun T : AdjointableMap (ReducedCrossedProduct (coefficientAction (B := B)))
          (KasparovDescent.Module (coefficientAction (B := B)) E) (KasparovDescent.Module (coefficientAction (B := B)) E) => T z)
      (KasparovDescent.reducedSourceRepresentation_coefficient (coefficientAction (B := B)) E scalarAction c.groupAction
        c.representation c.representation_equivariant a)
  operator_intertwine _ := rfl

/-- The ungraded odd cycle has the same exact coefficient restriction. -/
def oddCoefficientRestrictionIso (c : OddKasparovCycle scalarAction (coefficientAction (B := B)) E) :
    OddKasparovCycleIso
      (NativeSourcePullback.oddCycle scalarAction scalarInclusion (fun _ _ => rfl)
        (KasparovDescent.oddCycle (coefficientAction (B := B)) scalarAction c))
      (c.coefficientTensor (coefficientInclusion (B := B))) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine a z := by
    change KasparovDescent.reducedSourceRepresentation (coefficientAction (B := B)) E scalarAction c.groupAction
        c.representation c.representation_equivariant (scalarInclusion a) z =
      KasparovDescent.sourceRepresentation (coefficientAction (B := B)) E c.representation a z
    exact congrArg
      (fun T : AdjointableMap (ReducedCrossedProduct (coefficientAction (B := B)))
          (KasparovDescent.Module (coefficientAction (B := B)) E) (KasparovDescent.Module (coefficientAction (B := B)) E) => T z)
      (KasparovDescent.reducedSourceRepresentation_coefficient (coefficientAction (B := B)) E scalarAction c.groupAction
        c.representation c.representation_equivariant a)
  operator_intertwine _ := rfl

end Raw

/-- Actual native source pullback of the descended even class agrees with
its independently product-defined ordinary coefficient map. -/
theorem evenClass_coefficientRestriction
    (x : KasparovHomotopyClass.{0,0,uB,max u uB} scalarAction (coefficientAction (B := B))) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,0,uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct scalarAction)
      (C := ReducedCrossedProduct (coefficientAction (B := B))) («α» := scalarAction) («β» := descendedScalarAction) (γ := (descendedCoefficientAction (B := B)))
      false scalarInclusion scalarCoefficient_equivariant
        (KasparovDescent.evenClass (coefficientAction (B := B)) scalarAction x) =
      GroupUniverseOrdinaryEven.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) x := by
  refine Quotient.inductionOn' x ?_
  intro c
  change GroupUniverseParityFunctoriality.sourcePullback.{0,0,0,uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct scalarAction)
      (C := ReducedCrossedProduct (coefficientAction (B := B))) («α» := scalarAction) («β» := descendedScalarAction) (γ := (descendedCoefficientAction (B := B)))
      false scalarInclusion scalarCoefficient_equivariant
        (KasparovDescent.evenClass (coefficientAction (B := B)) scalarAction (KasparovHomotopyClass.mk c)) =
      GroupUniverseOrdinaryEven.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) (KasparovHomotopyClass.mk c)
  rw [KasparovDescent.evenClass_mk, NativeSourcePullback.even_mk]
  change (KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (NativeSourcePullback.evenCycle scalarAction scalarInclusion scalarCoefficient_equivariant
        (KasparovDescent.evenCycle (coefficientAction (B := B)) scalarAction c.cycle))) :
      KasparovHomotopyClass.{0,0,uB,max u uB} scalarAction (descendedCoefficientAction (B := B))) =
    GroupUniverseOrdinaryEven.coefficientPushforward.{uB,uB,max u uB}
      (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) (KasparovHomotopyClass.mk c)
  have hstored : BundledKasparovCycle.of c.cycle = c := by
    cases c
    rfl
  have hcoefficient :
      GroupUniverseOrdinaryEven.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) (KasparovHomotopyClass.mk c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (c.cycle.scalarCoefficientTensor (coefficientInclusion (B := B)))) := by
    have h := GroupUniverseOrdinaryEven.coefficientPushforward_mk_scalarCoefficientTensor
      c.cycle (coefficientInclusion (B := B))
    simpa only [hstored] using h
  exact (KasparovHomotopyClass.mk_eq_of_iso (evenCoefficientRestrictionIso c.cycle)).trans
    hcoefficient.symm

/-- Both sides use the full odd quotient and its genuine completed coefficient tensor. -/
theorem oddClass_coefficientRestriction
    (x : OddKK.{0,0,uB,max u uB} scalarAction (coefficientAction (B := B))) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,0,uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct scalarAction)
      (C := ReducedCrossedProduct (coefficientAction (B := B))) («α» := scalarAction) («β» := descendedScalarAction) (γ := (descendedCoefficientAction (B := B)))
      true scalarInclusion scalarCoefficient_equivariant
        (KasparovDescent.oddClass (coefficientAction (B := B)) scalarAction x) =
      GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) x := by
  refine Quotient.inductionOn' x ?_
  intro c
  change GroupUniverseParityFunctoriality.sourcePullback.{0,0,0,uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct scalarAction)
      (C := ReducedCrossedProduct (coefficientAction (B := B))) («α» := scalarAction) («β» := descendedScalarAction) (γ := (descendedCoefficientAction (B := B)))
      true scalarInclusion scalarCoefficient_equivariant
        (KasparovDescent.oddClass (coefficientAction (B := B)) scalarAction (OddKK.mk c)) =
      GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) (OddKK.mk c)
  rw [KasparovDescent.oddClass_mk, NativeSourcePullback.odd_mk]
  change (OddKK.mk (BundledOddKasparovCycle.of
      (NativeSourcePullback.oddCycle scalarAction scalarInclusion scalarCoefficient_equivariant
        (KasparovDescent.oddCycle (coefficientAction (B := B)) scalarAction c.cycle))) :
      OddKK.{0,0,uB,max u uB} scalarAction (descendedCoefficientAction (B := B))) =
    GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,uB,max u uB}
      (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) (OddKK.mk c)
  have hstored : BundledOddKasparovCycle.of c.cycle = c := by
    cases c
    rfl
  have hcoefficient :
      GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction (B := B))) (coefficientInclusion (B := B)) (OddKK.mk c) =
      OddKK.mk (BundledOddKasparovCycle.of (c.cycle.coefficientTensor (coefficientInclusion (B := B)))) := by
    have h := GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor
      c.cycle (coefficientInclusion (B := B))
    simpa only [hstored] using h
  exact (OddKK.mk_eq_of_iso (oddCoefficientRestrictionIso c.cycle)).trans
    hcoefficient.symm

end BC4lean.KKTheory.UnitScalarDescent
