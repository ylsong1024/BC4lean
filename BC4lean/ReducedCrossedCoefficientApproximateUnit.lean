import BC4lean.ReducedCrossedNorm
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual coefficient approximate units in the reduced crossed product

The concrete coefficient inclusion is nondegenerate. Multiplication on each
regular generator reduces to multiplication in the coefficient algebra.
Finite-support convergence then extends to every element by the actual dense
range and the uniform contraction estimate. The right-hand version follows
from involution and the eventual selfadjointness of the coefficient unit.
No completed nondegeneracy or crossed-product approximate unit is assumed.


-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

variable {Γ B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Left coefficient multiplication on the actual regular generator. -/
theorem coefficientToReducedCrossed_mul_generator (β : CStarAlgebraAction Γ B)
    (e a : B) (g : Γ) :
    coefficientToReducedCrossed β e *
        (⟨reducedCrossedGenerator β a g,
          reducedCrossedGenerator_mem β a g⟩ : ReducedCrossedProduct β) =
      ⟨reducedCrossedGenerator β (e * a) g,
        reducedCrossedGenerator_mem β (e * a) g⟩ := by
  apply Subtype.ext
  change reducedCrossedCoefficientHom β e *
      (reducedCrossedCoefficientHom β a * reducedCrossedRegular g) =
    reducedCrossedCoefficientHom β (e * a) * reducedCrossedRegular g
  rw [map_mul, mul_assoc]

/-- The same multiplication identity with the actual finite-support map. -/
@[simp] theorem coefficientToReducedCrossed_mul_algebraic_single
    (β : CStarAlgebraAction Γ B) (e a : B) (g : Γ) :
    coefficientToReducedCrossed β e *
        algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β g a) =
      algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β g (e * a)) := by
  apply Subtype.ext
  change reducedCrossedCoefficient β e *
      algebraicCrossedOperatorHom β (AlgebraicCrossedProduct.single β g a) =
    algebraicCrossedOperatorHom β (AlgebraicCrossedProduct.single β g (e * a))
  simp only [algebraicCrossedOperatorHom_single]
  change reducedCrossedCoefficientHom β e *
      (reducedCrossedCoefficientHom β a * reducedCrossedRegular g) =
    reducedCrossedCoefficientHom β (e * a) * reducedCrossedRegular g
  rw [map_mul, mul_assoc]

/-- The actual coefficient inclusion gives the usual multiplier norm bound. -/
theorem norm_coefficientToReducedCrossed_mul_le (β : CStarAlgebraAction Γ B)
    (e : B) (c : ReducedCrossedProduct β) :
    ‖coefficientToReducedCrossed β e * c‖ ≤ ‖e‖ * ‖c‖ := by
  simpa only [norm_coefficientToReducedCrossed] using
    norm_mul_le (coefficientToReducedCrossed β e) c

/-- Contractive coefficients act by contractions on the constructed algebra. -/
theorem coefficientToReducedCrossed_left_mul_dist_le
    (β : CStarAlgebraAction Γ B) (e : B) (he : ‖e‖ ≤ 1)
    (c d : ReducedCrossedProduct β) :
    dist (coefficientToReducedCrossed β e * c)
        (coefficientToReducedCrossed β e * d) ≤ dist c d := by
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
  calc
    ‖coefficientToReducedCrossed β e * (c - d)‖ ≤ ‖e‖ * ‖c - d‖ :=
      norm_coefficientToReducedCrossed_mul_le β e (c - d)
    _ ≤ 1 * ‖c - d‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ = ‖c - d‖ := one_mul _

/-- Any actual increasing coefficient approximate unit converges on every
finite-support reduced crossed-product element. -/
theorem tendsto_coefficientToReducedCrossed_mul_algebraic
    (β : CStarAlgebraAction Γ B) {l : Filter B} (hau : l.IsIncreasingApproximateUnit)
    (f : AlgebraicCrossedProduct β) :
    Tendsto (fun e => coefficientToReducedCrossed β e * algebraicToReducedCrossed β f)
      l (𝓝 (algebraicToReducedCrossed β f)) := by
  induction f using AlgebraicCrossedProduct.induction_on β with
  | zero =>
    simpa only [map_zero, mul_zero] using
      (tendsto_const_nhds (f := l) (x := (0 : ReducedCrossedProduct β)))
  | single g a =>
    simp only [coefficientToReducedCrossed_mul_algebraic_single]
    apply tendsto_subtype_rng.mpr
    change Tendsto
      (fun e : B => algebraicCrossedOperatorHom β
        (AlgebraicCrossedProduct.single β g (e * a))) l
      (𝓝 (algebraicCrossedOperatorHom β (AlgebraicCrossedProduct.single β g a)))
    simpa only [algebraicCrossedOperatorHom_single, Function.comp_def] using
      (continuous_reducedCrossedGenerator β g).continuousAt.tendsto.comp
        (hau.tendsto_mul_right a)
  | add f h ihf ihh =>
    simpa only [map_add, mul_add] using ihf.add ihh

/-- The original coefficient approximate unit acts on every element of the
actual reduced crossed product. The dense extension uses a quantitative
contraction estimate, rather than an assumed nondegeneracy conclusion. -/
theorem tendsto_coefficientToReducedCrossed_mul (β : CStarAlgebraAction Γ B)
    {l : Filter B} (hau : l.IsIncreasingApproximateUnit) (c : ReducedCrossedProduct β) :
    Tendsto (fun e => coefficientToReducedCrossed β e * c) l (𝓝 c) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨f, hf⟩ := Metric.denseRange_iff.mp
    (algebraicToReducedCrossed_denseRange β) c (ε / 3) (by positivity)
  have hfinite : ∀ᶠ e in l,
      dist (coefficientToReducedCrossed β e * algebraicToReducedCrossed β f)
        (algebraicToReducedCrossed β f) < ε / 3 :=
    Metric.tendsto_nhds.mp
      (tendsto_coefficientToReducedCrossed_mul_algebraic β hau f)
      (ε / 3) (by positivity)
  filter_upwards [hau.eventually_norm, hfinite] with e he herr
  have hdist := coefficientToReducedCrossed_left_mul_dist_le β e he c
    (algebraicToReducedCrossed β f)
  have hf' : dist (algebraicToReducedCrossed β f) c < ε / 3 := by
    simpa only [dist_comm] using hf
  calc
    dist (coefficientToReducedCrossed β e * c) c ≤
        dist (coefficientToReducedCrossed β e * c)
          (coefficientToReducedCrossed β e * algebraicToReducedCrossed β f) +
        dist (coefficientToReducedCrossed β e * algebraicToReducedCrossed β f) c :=
      dist_triangle _ _ _
    _ ≤ dist c (algebraicToReducedCrossed β f) +
        (dist (coefficientToReducedCrossed β e * algebraicToReducedCrossed β f)
            (algebraicToReducedCrossed β f) + dist (algebraicToReducedCrossed β f) c) :=
      add_le_add hdist (dist_triangle _ _ _)
    _ < ε := by linarith

/-- Right coefficient multiplication converges as well, by involution and
the actual coefficient approximate unit's eventual selfadjointness. -/
theorem tendsto_mul_coefficientToReducedCrossed (β : CStarAlgebraAction Γ B)
    {l : Filter B} (hau : l.IsIncreasingApproximateUnit) (c : ReducedCrossedProduct β) :
    Tendsto (fun e => c * coefficientToReducedCrossed β e) l (𝓝 c) := by
  apply (star_star c ▸ (tendsto_coefficientToReducedCrossed_mul β hau (star c)).star).congr'
  filter_upwards [hau.eventually_star_eq] with e he
  simp only [star_mul, star_star, ← map_star, he]

/-- Canonical positive contractive coefficient approximate-unit convergence
on the left. -/
theorem tendsto_coefficientToReducedCrossed_approximateUnit_mul
    (β : CStarAlgebraAction Γ B) (c : ReducedCrossedProduct β) :
    Tendsto (fun e => coefficientToReducedCrossed β e * c)
      (CStarAlgebra.approximateUnit B) (𝓝 c) :=
  tendsto_coefficientToReducedCrossed_mul β (CStarAlgebra.increasingApproximateUnit B) c

/-- Canonical positive contractive coefficient approximate-unit convergence
on the right. -/
theorem tendsto_mul_coefficientToReducedCrossed_approximateUnit
    (β : CStarAlgebraAction Γ B) (c : ReducedCrossedProduct β) :
    Tendsto (fun e => c * coefficientToReducedCrossed β e)
      (CStarAlgebra.approximateUnit B) (𝓝 c) :=
  tendsto_mul_coefficientToReducedCrossed β (CStarAlgebra.increasingApproximateUnit B) c

/-- Mapping an actual increasing coefficient approximate unit through the
concrete inclusion gives an actual two-sided approximate unit of the
constructed reduced crossed product. -/
theorem coefficientToReducedCrossed_map_isApproximateUnit
    (β : CStarAlgebraAction Γ B) {l : Filter B} (hau : l.IsIncreasingApproximateUnit) :
    (Filter.map (coefficientToReducedCrossed β) l).IsApproximateUnit := by
  let : l.NeBot := hau.neBot
  exact {
    tendsto_mul_left := fun c => by
      rw [Filter.tendsto_map'_iff]
      exact tendsto_mul_coefficientToReducedCrossed β hau c
    tendsto_mul_right := fun c => by
      rw [Filter.tendsto_map'_iff]
      exact tendsto_coefficientToReducedCrossed_mul β hau c
    neBot := inferInstance }

end BC4lean.KKTheory
