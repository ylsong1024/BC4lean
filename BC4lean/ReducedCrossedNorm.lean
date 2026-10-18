import BC4lean.AlgebraicCrossedRepresentation
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Faithfulness, norm and separability of regular crossed products

Applying a finite regular operator to a vector supported at the group identity
recovers each twisted coefficient. This proves that the integrated map is
faithful before the operator norm is used as a norm on the algebraic product.
For countable groups and separable coefficients, the actual generator span
also proves separability of the constructed reduced crossed product.
-/

noncomputable section
namespace BC4lean.KKTheory

open TopologicalSpace

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- The coefficient-recovery formula for the actual regular representation. -/
theorem algebraicCrossedOperator_evaluation_inclusion_one (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) (k : Γ) (x : Bᵐᵒᵖ) :
    reducedCrossedEvaluation k
        (algebraicCrossedOperatorHom α f (reducedCrossedInclusion (1 : Γ) x)) =
      MulOpposite.op (α.automorphism k⁻¹ (AlgebraicCrossedProduct.coeff α f k) *
        MulOpposite.unop x) := by
  classical
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp
  | single g b =>
    rw [algebraicCrossedOperatorHom_single]
    change reducedCrossedEvaluation k
      (reducedCrossedCoefficient α b (reducedCrossedRegular g (reducedCrossedInclusion 1 x))) = _
    rw [reducedCrossedEvaluation_coefficient, reducedCrossedEvaluation_regular]
    by_cases h : g = k
    · subst g
      simp only [inv_mul_cancel, reducedCrossedEvaluation_inclusion, ite_true,
        AlgebraicCrossedProduct.coeff_single, Finsupp.single_eq_same]
    · have h' : g⁻¹ * k ≠ 1 := by
        intro hk
        exact h (inv_mul_eq_one.mp hk)
      simp only [reducedCrossedEvaluation_inclusion,
        AlgebraicCrossedProduct.coeff_single, Finsupp.single_apply,
        if_neg (Ne.symm h'), if_neg h, MulOpposite.unop_zero, mul_zero,
        map_zero, zero_mul, MulOpposite.op_zero]
  | add f h ihf ihh =>
    simp only [map_add, AdjointableMap.coe_add_apply, ihf, ihh,
      AlgebraicCrossedProduct.coeff_add, Finsupp.add_apply, add_mul, MulOpposite.op_add]

/-- A vanishing regular operator has every coefficient zero. -/
theorem algebraicCrossedOperatorHom_injective (α : CStarAlgebraAction Γ B) :
    Function.Injective (algebraicCrossedOperatorHom α) := by
  suffices hzero : ∀ f : AlgebraicCrossedProduct α,
      algebraicCrossedOperatorHom α f = 0 → f = 0 by
    intro f h heq
    apply sub_eq_zero.mp
    apply hzero
    simp only [map_sub, heq, sub_self]
  intro f hf
  apply AlgebraicCrossedProduct.ext α
  intro k
  let b := α.automorphism k⁻¹ (AlgebraicCrossedProduct.coeff α f k)
  have h := algebraicCrossedOperator_evaluation_inclusion_one α f k (MulOpposite.op (star b))
  rw [hf] at h
  have hmul : b * star b = 0 := by
    exact MulOpposite.op_injective (by simpa only [AdjointableMap.coe_zero_apply,
      map_zero, MulOpposite.unop_op, MulOpposite.op_zero] using h.symm)
  have hn : ‖b‖ * ‖b‖ = 0 := by
    rw [← CStarRing.norm_self_mul_star, hmul, norm_zero]
  have hb : b = 0 := norm_eq_zero.mp (mul_self_eq_zero.mp hn)
  have hc : AlgebraicCrossedProduct.coeff α f k = 0 := by
    apply (α.automorphism k⁻¹).injective
    rw [map_zero]
    change b = 0
    exact hb
  simpa only [AlgebraicCrossedProduct.coeff_zero, Finsupp.zero_apply] using hc

theorem algebraicToReducedCrossed_injective (α : CStarAlgebraAction Γ B) :
    Function.Injective (algebraicToReducedCrossed α) := by
  intro f h heq
  exact algebraicCrossedOperatorHom_injective α (congrArg Subtype.val heq)

/-- The reduced norm is the norm of the faithful regular Hilbert-module operator. -/
def algebraicCrossedReducedNorm (α : CStarAlgebraAction Γ B) (f : AlgebraicCrossedProduct α) : ℝ :=
  ‖algebraicCrossedOperatorHom α f‖

theorem algebraicCrossedReducedNorm_nonneg (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) : 0 ≤ algebraicCrossedReducedNorm α f := norm_nonneg _

theorem algebraicCrossedReducedNorm_add_le (α : CStarAlgebraAction Γ B)
    (f h : AlgebraicCrossedProduct α) :
    algebraicCrossedReducedNorm α (f + h) ≤
      algebraicCrossedReducedNorm α f + algebraicCrossedReducedNorm α h := by
  simpa only [algebraicCrossedReducedNorm, map_add] using
    norm_add_le (algebraicCrossedOperatorHom α f) (algebraicCrossedOperatorHom α h)

theorem algebraicCrossedReducedNorm_smul (α : CStarAlgebraAction Γ B) (c : ℂ)
    (f : AlgebraicCrossedProduct α) :
    algebraicCrossedReducedNorm α (c • f) = ‖c‖ * algebraicCrossedReducedNorm α f := by
  simp only [algebraicCrossedReducedNorm, map_smul, norm_smul]

theorem algebraicCrossedReducedNorm_mul_le (α : CStarAlgebraAction Γ B)
    (f h : AlgebraicCrossedProduct α) :
    algebraicCrossedReducedNorm α (f * h) ≤
      algebraicCrossedReducedNorm α f * algebraicCrossedReducedNorm α h := by
  simpa only [algebraicCrossedReducedNorm, map_mul] using
    norm_mul_le (algebraicCrossedOperatorHom α f) (algebraicCrossedOperatorHom α h)

@[simp] theorem algebraicCrossedReducedNorm_star (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) :
    algebraicCrossedReducedNorm α (star f) = algebraicCrossedReducedNorm α f := by
  simp only [algebraicCrossedReducedNorm, map_star, norm_star]

@[simp] theorem algebraicCrossedReducedNorm_eq_zero (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) : algebraicCrossedReducedNorm α f = 0 ↔ f = 0 := by
  simp only [algebraicCrossedReducedNorm, norm_eq_zero,
    map_eq_zero_iff _ (algebraicCrossedOperatorHom_injective α)]

theorem algebraicCrossedReducedNorm_cstar (α : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct α) :
    algebraicCrossedReducedNorm α (star f * f) = algebraicCrossedReducedNorm α f ^ 2 := by
  simp only [algebraicCrossedReducedNorm, map_mul, map_star, pow_two]
  exact CStarRing.norm_star_mul_self

/-- The actual coefficient representation is continuous in its operator norm. -/
theorem continuous_reducedCrossedCoefficient (α : CStarAlgebraAction Γ B) :
    Continuous (reducedCrossedCoefficient α) :=
  (AddMonoidHomClass.isometry_of_norm (reducedCrossedCoefficientHom α)
    (norm_reducedCrossedCoefficient α)).continuous

/-- Each fixed group element gives a continuous coefficient family of generators. -/
theorem continuous_reducedCrossedGenerator (α : CStarAlgebraAction Γ B) (g : Γ) :
    Continuous (fun b : B => reducedCrossedGenerator α b g) :=
  (continuous_reducedCrossedCoefficient α).mul continuous_const

/-- The actual finite integrated range is precisely the span of regular generators. -/
theorem algebraicCrossedOperator_range_span (α : CStarAlgebraAction Γ B) :
    (algebraicCrossedOperatorLinear α).range = Submodule.span ℂ
      (Set.range (fun p : B × Γ => reducedCrossedGenerator α p.1 p.2)) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    induction f using AlgebraicCrossedProduct.induction_on α with
    | zero => simp
    | single g b =>
      rw [algebraicCrossedOperatorLinear_single]
      exact Submodule.subset_span ⟨(b, g), rfl⟩
    | add f h ihf ihh =>
      rw [map_add]
      exact Submodule.add_mem _ ihf ihh
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, g⟩, rfl⟩
    exact ⟨AlgebraicCrossedProduct.single α g b,
      algebraicCrossedOperatorLinear_single α g b⟩

/-- The concrete reduced crossed product is the closure of this actual finite span. -/
theorem reducedCrossedAlgebra_coe_eq_closure_span (α : CStarAlgebraAction Γ B) :
    (reducedCrossedAlgebra α :
      Set (AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (ReducedCrossedHilbertModule B Γ))) =
      closure (Submodule.span ℂ
        (Set.range (fun p : B × Γ => reducedCrossedGenerator α p.1 p.2)) :
          Set (AdjointableMap B (ReducedCrossedHilbertModule B Γ)
            (ReducedCrossedHilbertModule B Γ))) := by
  rw [← algebraicCrossedOperator_range_closure α]
  change closure ((algebraicCrossedOperatorLinear α).range :
    Set (AdjointableMap B (ReducedCrossedHilbertModule B Γ)
      (ReducedCrossedHilbertModule B Γ))) = _
  rw [algebraicCrossedOperator_range_span]

/-- Countably many continuous coefficient families form a separable generator set. -/
theorem reducedCrossedGenerator_range_isSeparable [Countable Γ] [SeparableSpace B]
    (α : CStarAlgebraAction Γ B) :
    IsSeparable (Set.range (fun p : B × Γ => reducedCrossedGenerator α p.1 p.2)) := by
  have hrange :
      Set.range (fun p : B × Γ => reducedCrossedGenerator α p.1 p.2) =
        ⋃ g : Γ, Set.range (fun b : B => reducedCrossedGenerator α b g) := by
    ext T
    constructor
    · rintro ⟨⟨b, g⟩, rfl⟩
      exact Set.mem_iUnion.mpr ⟨g, b, rfl⟩
    · intro hT
      obtain ⟨g, b, hb⟩ := Set.mem_iUnion.mp hT
      exact ⟨(b, g), hb⟩
  rw [hrange]
  apply IsSeparable.iUnion
  intro g
  exact isSeparable_range (continuous_reducedCrossedGenerator α g)

/-- The operator-norm closed regular crossed-product algebra is actually separable. -/
theorem reducedCrossedAlgebra_isSeparable [Countable Γ] [SeparableSpace B]
    (α : CStarAlgebraAction Γ B) :
    IsSeparable (reducedCrossedAlgebra α :
      Set (AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (ReducedCrossedHilbertModule B Γ))) := by
  rw [reducedCrossedAlgebra_coe_eq_closure_span]
  exact (reducedCrossedGenerator_range_isSeparable α).span.closure

/-- Countable groups and separable coefficients give a separable reduced crossed product. -/
instance reducedCrossedProduct_separableSpace [Countable Γ] [SeparableSpace B]
    (α : CStarAlgebraAction Γ B) : SeparableSpace (ReducedCrossedProduct α) :=
  (reducedCrossedAlgebra_isSeparable α).separableSpace

end BC4lean.KKTheory
