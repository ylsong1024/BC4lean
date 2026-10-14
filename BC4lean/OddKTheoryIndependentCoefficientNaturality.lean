import BC4lean.GroupUniverseOrdinaryOdd
import BC4lean.OddKTheoryCoefficientTensorFiniteIndex
import BC4lean.OddKTheoryModuleUniverseIndex

/-! # Genuine odd comparison naturality for independent coefficient universes

The coefficient map is the actual graded homomorphism-cycle product through
the identity-on-cycle Clifford coordinate bridge. Its raw representative is
the completed ordinary coefficient tensor. Finite unitary inverse recovery
and the true image interval compute its index. Whole shrinking unitaries
then prove naturality for every original module universe, and can place the
actual product image in any chosen target module universe. Neither map is
defined through the K-theory comparison.
-/

noncomputable section
universe uB uC uE uF
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type uB} {C : Type uC}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
local notation "γ₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C)

theorem oddOperatorK1KKInverse_independentCoefficientIndex
    (f : B →⋆ₙₐ[ℂ] C) (x : OperatorK1 B) :
    oddKKOperatorK1Index
      (GroupUniverseOrdinaryOdd.coefficientPushforward f (oddOperatorK1KKInverse x)) =
    operatorK1Map f x := by
  obtain ⟨n, u, hu, hx⟩ := oddKTheoryOperatorK1_exists_scalarIdentityRepresentative x
  rw [← hx, oddOperatorK1KKInverse_scalarIdentityUnitary]
  change oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f
    (OddKK.mk (BundledOddKasparovCycle.of (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu)))) = _
  rw [GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor,
    oddKKOperatorK1Index_mk]
  exact oddKTheoryMatrixUnitaryCoefficientTensor_operatorK1Index f u hu

/-- The actual tensor product carries a whole source shrink unitary to a
whole target tensor unitary, so its index is independent of the source
module universe used to represent the full odd class. -/
theorem oddKKOperatorK1Index_coefficientPushforward_shrink
    (f : B →⋆ₙₐ[ℂ] C) (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f
      (OddKK.shrink.{0, 0, uB, uE, uF} x)) =
    oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f x) := by
  refine Quotient.inductionOn x ?_
  intro c
  let d : BundledOddKasparovCycle.{0, 0, uB, uF} α₁ β₁ := c.shrink
  change oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f
      (OddKK.mk (BundledOddKasparovCycle.of d.cycle))) =
    oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f
      (OddKK.mk (BundledOddKasparovCycle.of c.cycle)))
  rw [GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor,
    GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor,
    oddKKOperatorK1Index_mk, oddKKOperatorK1Index_mk]
  exact (oddScalarKasparovOperatorK1Index_iso
    ((c.shrinkIso : OddKasparovCycleIso c.cycle d.cycle).coefficientTensor f)).symm

theorem oddKKOperatorK1Index_independentCoefficientPushforward
    (f : B →⋆ₙₐ[ℂ] C) (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f x) =
      operatorK1Map f (oddKKOperatorK1Index x) := by
  let y : OddKK.{0, 0, uB, uB} α₁ β₁ := OddKK.shrink.{0, 0, uB, uE, uB} x
  have hy : oddOperatorK1KKInverse (oddKKOperatorK1Index y) = y :=
    oddOperatorK1KKInverse_leftInverse_index y
  calc
    _ = oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f y) :=
      (oddKKOperatorK1Index_coefficientPushforward_shrink.{uB, uC, uE, uB} f x).symm
    _ = oddKKOperatorK1Index (GroupUniverseOrdinaryOdd.coefficientPushforward f
        (oddOperatorK1KKInverse (oddKKOperatorK1Index y))) :=
      congrArg (fun z : OddKK.{0, 0, uB, uB} α₁ β₁ => oddKKOperatorK1Index
        (GroupUniverseOrdinaryOdd.coefficientPushforward f z)) hy.symm
    _ = operatorK1Map f (oddKKOperatorK1Index y) :=
      oddOperatorK1KKInverse_independentCoefficientIndex f _
    _ = _ := congrArg (operatorK1Map f)
      (oddKKOperatorK1Index_shrink_anyModuleUniverse.{uB, uE, uB} x)

set_option maxHeartbeats 4000000 in
theorem oddScalarKasparovOperatorK1Index_coefficientTensor {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : OddKasparovCycle α₁ β₁ E) (f : B →⋆ₙₐ[ℂ] C) :
    (c.coefficientTensor f).operatorK1Index = operatorK1Map f c.operatorK1Index := by
  let d : OddKasparovCycle.{0, 0, uB, uE}
      (CStarAlgebraAction.trivial : CStarAlgebraAction (PUnit : Type) ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction (PUnit : Type) B) E :=
    { countablyGenerated := c.countablyGenerated
      groupAction := EquivariantHilbertModule.trivial
      representation := c.representation
      representation_equivariant := by
        intro g a
        have hg : g = 1 := Subsingleton.elim g 1
        subst g
        rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one]
        rfl
      operator := c.operator
      selfadjoint_mod_compact := c.selfadjoint_mod_compact
      square_mod_compact := c.square_mod_compact
      commutator_compact := c.commutator_compact
      equivariance_mod_compact := by
        intro g a
        have hg : g = 1 := Subsingleton.elim g 1
        subst g
        rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one,
          sub_self, zero_mul]
        exact IsModuleCompact.zero }
  have hd : d.operatorK1Index = c.operatorK1Index := rfl
  have hdf : (d.coefficientTensor f).operatorK1Index = (c.coefficientTensor f).operatorK1Index := rfl
  calc
    _ = (d.coefficientTensor f).operatorK1Index := hdf.symm
    _ = operatorK1Map f d.operatorK1Index := by
      have hh := oddKKOperatorK1Index_independentCoefficientPushforward (B := B) (C := C) f
        (OddKK.mk (Γ := (PUnit : Type)) (A := ℂ) (B := B)
          (BundledOddKasparovCycle.of (Γ := (PUnit : Type)) (A := ℂ) (B := B) (E := E) d))
      rw [GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor,
        oddKKOperatorK1Index_mk, oddKKOperatorK1Index_mk] at hh
      change (d.coefficientTensor f).operatorK1Index = operatorK1Map f d.operatorK1Index at hh
      exact hh
    _ = _ := congrArg (operatorK1Map f) hd

/-- The actual coefficient product may be represented in any target module
universe by its genuine full-homotopy shrinking equivalence. -/
def oddKKIndependentCoefficientPushforward (f : B →⋆ₙₐ[ℂ] C) :
    OddKK.{0, 0, uB, uE} α₁ β₁ →+ OddKK.{0, 0, uC, uF} α₁ γ₁ :=
  (OddKK.shrinkHom.{0, 0, uC, max uE uC, uF}).comp
    (GroupUniverseOrdinaryOdd.coefficientPushforward f)

theorem oddKKIndependentCoefficientPushforward_mk_coefficientTensor {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : OddKasparovCycle α₁ β₁ E) (f : B →⋆ₙₐ[ℂ] C) :
    oddKKIndependentCoefficientPushforward.{uB, uC, uE, uF} f
      (OddKK.mk (BundledOddKasparovCycle.of c)) =
    OddKK.shrink.{0, 0, uC, max uE uC, uF}
      (OddKK.mk (BundledOddKasparovCycle.of (c.coefficientTensor f))) := by
  change OddKK.shrink.{0, 0, uC, max uE uC, uF}
      (GroupUniverseOrdinaryOdd.coefficientPushforward f
        (OddKK.mk (BundledOddKasparovCycle.of c))) = _
  rw [GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor]

theorem oddKKOperatorK1Index_independentCoefficientPushforward_anyModuleUniverse
    (f : B →⋆ₙₐ[ℂ] C) (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1Index (oddKKIndependentCoefficientPushforward.{uB, uC, uE, uF} f x) =
      operatorK1Map f (oddKKOperatorK1Index x) := by
  change oddKKOperatorK1Index (OddKK.shrink.{0, 0, uC, max uE uC, uF}
    (GroupUniverseOrdinaryOdd.coefficientPushforward f x)) = _
  rw [oddKKOperatorK1Index_shrink_anyModuleUniverse]
  exact oddKKOperatorK1Index_independentCoefficientPushforward f x

theorem oddKKOperatorK1AllModuleUniversesAddEquiv_independentCoefficient_natural
    (f : B →⋆ₙₐ[ℂ] C) (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    oddKKOperatorK1AllModuleUniversesAddEquiv
      (oddKKIndependentCoefficientPushforward.{uB, uC, uE, uF} f x) =
    operatorK1Map f (oddKKOperatorK1AllModuleUniversesAddEquiv x) := by
  simpa only [oddKKOperatorK1AllModuleUniversesAddEquiv_apply] using
    oddKKOperatorK1Index_independentCoefficientPushforward_anyModuleUniverse.{uB, uC, uE, uF} f x

theorem oddOperatorK1KKInverseAllModuleUniverses_independentCoefficient_natural
    (f : B →⋆ₙₐ[ℂ] C) (x : OperatorK1 B) :
    oddKKIndependentCoefficientPushforward.{uB, uC, uE, uF} f
      (oddOperatorK1KKInverseAllModuleUniverses.{uB, uE} x) =
    oddOperatorK1KKInverseAllModuleUniverses.{uC, uF} (operatorK1Map f x) := by
  apply (oddKKOperatorK1AllModuleUniversesAddEquiv (B := C) :
    OddKK.{0, 0, uC, uF} α₁ γ₁ ≃+ OperatorK1 C).injective
  simp only [oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  rw [oddKKOperatorK1Index_independentCoefficientPushforward_anyModuleUniverse,
    oddOperatorK1KKInverseAllModuleUniverses_rightInverse_index,
    oddOperatorK1KKInverseAllModuleUniverses_rightInverse_index]

theorem oddKKIndependentCoefficientPushforward_comparison_square (f : B →⋆ₙₐ[ℂ] C) :
    ((oddKKOperatorK1AllModuleUniversesAddEquiv (B := C) :
      OddKK.{0, 0, uC, uF} α₁ γ₁ ≃+ OperatorK1 C).toAddMonoidHom).comp
        (oddKKIndependentCoefficientPushforward.{uB, uC, uE, uF} f) =
    (operatorK1Map f).comp ((oddKKOperatorK1AllModuleUniversesAddEquiv (B := B) :
      OddKK.{0, 0, uB, uE} α₁ β₁ ≃+ OperatorK1 B).toAddMonoidHom) := by
  ext x
  exact oddKKOperatorK1AllModuleUniversesAddEquiv_independentCoefficient_natural f x

end BC4lean.KKTheory
