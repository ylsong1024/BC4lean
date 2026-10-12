import BC4lean.GroupUniverseProduct
import BC4lean.PositiveGradedULiftFullWitness
import BC4lean.GradedKasparovFirstIsoProduct
import BC4lean.GradedKasparovSecondIsoProduct

/-! # Actual lifted product classes through whole tensor unitaries

The completed first- and second-factor tensor unitaries transport all
four connection laws and localized positivity. A lifted whole-cycle
unitary and genuine full uniqueness identify the chosen products with
the lifted original products. All module universes remain explicit.
-/

noncomputable section
universe uΓ uA uB uC uE uF v
namespace BC4lean.KKTheory.GroupUniverseProduct
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

theorem product_ulift_first
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ, uB, uC, uF} β γ δB δC) :
    GradedKasparovHomotopyClass.ulift.{uΓ, uA, uC, max uE uF, v} (product x y) =
      product (GradedKasparovHomotopyClass.ulift.{uΓ, uA, uB, uE, v} x) y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let c' := (c.ulift : BundledGradedKasparovCycle.{uΓ, uA, uB, max uE v} α β δA δB)
  let q := bundledProduct c d
  let u : GradedKasparovCycleIso c.cycle c'.cycle := c.cycle.uliftIso
  have hR := gradedKasparovFirstIsoProduct_isProduct c.cycle c'.cycle d.cycle u
    (productOperator_isProduct c d)
  have hright := product_mk_eq_of_isProduct c' d hR
  have hq : GradedKasparovCycleIso q.cycle
      (q.ulift : BundledGradedKasparovCycle.{uΓ, uA, uC, max (max uE uF) v}
        α γ δA δC).cycle := q.cycle.uliftIso
  let q' := BundledGradedKasparovCycle.of
    (gradedKasparovTensorCycleOfConditions c'.cycle d.cycle
      (gradedKasparovFirstIsoProductOperator c.cycle c'.cycle d.cycle u (productOperator c d)) hR.cycleConditions)
  have hcycle : GradedKasparovCycleIso q.cycle q'.cycle :=
    gradedKasparovFirstIsoProduct_cycleIso c.cycle c'.cycle d.cycle u
      (productOperator_isProduct c d)
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := (q.ulift : BundledGradedKasparovCycle.{uΓ, uA, uC, max (max uE uF) v}
      α γ δA δC)) (d := q') (hq.symm.trans hcycle)
  exact hiso.trans hright.symm

theorem product_ulift_second
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ, uB, uC, uF} β γ δB δC) :
    GradedKasparovHomotopyClass.ulift.{uΓ, uA, uC, max uE uF, v} (product x y) =
      product x (GradedKasparovHomotopyClass.ulift.{uΓ, uB, uC, uF, v} y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let d' := (d.ulift : BundledGradedKasparovCycle.{uΓ, uB, uC, max uF v} β γ δB δC)
  let q := bundledProduct c d
  let u : GradedKasparovCycleIso d.cycle d'.cycle := d.cycle.uliftIso
  have hR := gradedKasparovSecondIsoProduct_isProduct c.cycle d.cycle d'.cycle u
    (productOperator_isProduct c d)
  have hright := product_mk_eq_of_isProduct c d' hR
  have hq : GradedKasparovCycleIso q.cycle
      (q.ulift : BundledGradedKasparovCycle.{uΓ, uA, uC, max (max uE uF) v}
        α γ δA δC).cycle := q.cycle.uliftIso
  let q' := BundledGradedKasparovCycle.of
    (gradedKasparovTensorCycleOfConditions c.cycle d'.cycle
      (gradedKasparovSecondIsoProductOperator d.cycle d'.cycle u (productOperator c d)) hR.cycleConditions)
  have hcycle : GradedKasparovCycleIso q.cycle q'.cycle :=
    gradedKasparovSecondIsoProduct_cycleIso c.cycle d.cycle d'.cycle u
      (productOperator_isProduct c d)
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := (q.ulift : BundledGradedKasparovCycle.{uΓ, uA, uC, max (max uE uF) v}
      α γ δA δC)) (d := q') (hq.symm.trans hcycle)
  exact hiso.trans hright.symm

end BC4lean.KKTheory.GroupUniverseProduct
