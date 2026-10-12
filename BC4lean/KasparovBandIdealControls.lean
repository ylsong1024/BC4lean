import BC4lean.KasparovEvenSquarePartition

/-! # Compact ideal controls from selected geometric band errors

These proofs use the actual strong column-square limit and the actual
operator-norm summability comparison. The hypotheses are the numerical
errors selected by the paired canonical-AU construction, rather than
compactness claims about the final partition.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance kasparovBandIdealControlsLocalInst1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovBandIdealControlsLocalInst2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

namespace IsStrongIncreasingModuleResolution
variable {e : ℕ → AdjointableMap B E E} (he : IsStrongIncreasingModuleResolution e)
  (u : ℕ → AdjointableMap B E E) (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1)

include he in
theorem band_norm_le_one (n : ℕ) : ‖band e n‖ ≤ 1 := by
  have hinc := positive_contractive_increment (e n) (e (n + 1)) (he.nonneg n)
    (he.monotone (Nat.le_succ n))
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (he.nonneg (n + 1))).mpr (he.le_one (n + 1)))
  exact norm_cfcSqrt_le_one_of_nonneg_of_norm_le_one _ hinc.1 hinc.2

include he in
theorem band_square_le_residual (n : ℕ) : band e n * band e n ≤ 1 - e n := by
  rw [he.band_square]
  exact sub_le_sub_right (he.le_one (n + 1)) (e n)

include hu0 hu1 in
private theorem weight_norm_le_one (n : ℕ) : ‖u n‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hu0 n)).mpr (hu1 n)

private theorem finite_band_term_compact
    (hc : ∀ n, IsModuleCompact (band e n)) (n : ℕ) :
    IsModuleCompact (band e n * u n * band e n) :=
  ((hc n).comp_right (u n)).comp_right (band e n)

/-- The second source square's product with each family test is compact,
from the selected current-weight compact residual and the band commutator. -/
theorem partitionSquare_compact_product_of_residual_controls
    (hc : ∀ n, IsModuleCompact (band e n)) (b : AdjointableMap B E E)
    (hres : ∀ᶠ n : ℕ in atTop,
      ‖e n * (u n * b) - u n * b‖ < (kasparovSelectionBudget n) ^ 2 / (‖b‖ + 1))
    (hcomm : ∀ᶠ n : ℕ in atTop,
      ‖band e n * b - b * band e n‖ < kasparovSelectionBudget n) :
    IsModuleCompact (he.partitionSquare u hu0 hu1 * b) := by
  have hsum : Summable (fun n => band e n * u n * band e n * b) := by
    apply (kasparovSelectionBudget_summable.mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [hres, hcomm] with n hnres hncomm
    have hprod := norm_band_weighted_product_lt_of_residual (band e n) (e n) (u n) b
      (band_star n) (he.band_square_le_residual n) (weight_norm_le_one u hu0 hu1 n)
      (kasparovSelectionBudget n) (kasparovSelectionBudget_pos n) hnres
    have hbound := norm_weighted_band_product_le_band_product (band e n) (u n) b
      (he.band_norm_le_one n) (weight_norm_le_one u hu0 hu1 n)
    linarith
  exact compact_right_product_of_summable_strong_series _ _ b
    (he.partitionSquare_finite_apply_tendsto u hu0 hu1)
    (finite_band_term_compact u hc) hsum

/-- The complementary first source square's coefficient product is
compact, from the genuine first-algebra AU and square-root-band controls. -/
theorem complementary_partitionSquare_compact_product_of_unit_controls
    (hc : ∀ n, IsModuleCompact (band e n)) (a : AdjointableMap B E E)
    (hunit : ∀ᶠ n : ℕ in atTop, ‖(1 - u n) * a‖ < kasparovSelectionBudget n)
    (hcomm : ∀ᶠ n : ℕ in atTop,
      ‖band e n * a - a * band e n‖ < kasparovSelectionBudget n) :
    IsModuleCompact (he.partitionSquare (fun n => 1 - u n)
      (fun n => sub_nonneg.mpr (hu1 n)) (fun n => sub_le_self _ (hu0 n)) * a) := by
  let v : ℕ → AdjointableMap B E E := fun n => 1 - u n
  have hv0 (n : ℕ) : 0 ≤ v n := sub_nonneg.mpr (hu1 n)
  have hv1 (n : ℕ) : v n ≤ 1 := sub_le_self _ (hu0 n)
  have hsum : Summable (fun n => band e n * v n * band e n * a) := by
    apply (kasparovSelectionBudget_summable.mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [hunit, hcomm] with n hnunit hncomm
    have hbound := norm_weighted_band_product_le (band e n) (v n) a
      (he.band_norm_le_one n) (weight_norm_le_one v hv0 hv1 n)
    linarith
  exact compact_right_product_of_summable_strong_series _ _ a
    (he.partitionSquare_finite_apply_tendsto v hv0 hv1)
    (finite_band_term_compact v hc) hsum

/-- Norm-summable weighted commutator errors identify the actual
compact commutator of the constructed source square. -/
theorem partitionSquare_compact_commutator_of_geometric_controls
    (hc : ∀ n, IsModuleCompact (band e n)) (a : AdjointableMap B E E)
    (hband : ∀ᶠ n : ℕ in atTop,
      ‖band e n * a - a * band e n‖ < kasparovSelectionBudget n)
    (hweight : ∀ᶠ n : ℕ in atTop, ‖u n * a - a * u n‖ < kasparovSelectionBudget n) :
    IsModuleCompact (he.partitionSquare u hu0 hu1 * a - a * he.partitionSquare u hu0 hu1) := by
  have hsum : Summable (fun n => (band e n * u n * band e n) * a -
      a * (band e n * u n * band e n)) := by
    apply (kasparovSelectionBudget_summable.mul_left 3).of_norm_bounded_eventually_nat
    filter_upwards [hband, hweight] with n hnband hnweight
    have hbound := norm_weighted_band_commutator_le (band e n) (u n) a
      (he.band_norm_le_one n) (weight_norm_le_one u hu0 hu1 n)
    linarith
  exact compact_commutator_of_summable_strong_series _ _ a
    (he.partitionSquare_finite_apply_tendsto u hu0 hu1)
    (finite_band_term_compact u hc) hsum

section ActualAction
variable {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ B}

theorem partitionSquare_compact_action_error_of_geometric_controls
    (hc : ∀ n, IsModuleCompact (band e n))
    (U : EquivariantHilbertModule α E) (g : Γ)
    (hband : ∀ᶠ n : ℕ in atTop,
      ‖U.conjugateOperator g (band e n) - band e n‖ < kasparovSelectionBudget n)
    (hweight : ∀ᶠ n : ℕ in atTop,
      ‖U.conjugateOperator g (u n) - u n‖ < kasparovSelectionBudget n) :
    IsModuleCompact (U.conjugateOperator g (he.partitionSquare u hu0 hu1) -
      he.partitionSquare u hu0 hu1) := by
  have hsum : Summable (fun n => U.conjugateOperator g (band e n * u n * band e n) -
      band e n * u n * band e n) := by
    apply (kasparovSelectionBudget_summable.mul_left 3).of_norm_bounded_eventually_nat
    filter_upwards [hband, hweight] with n hnband hnweight
    have hbound := norm_weighted_band_action_le (U.conjugateOperatorStarAlgEquiv g)
      (band e n) (u n) (he.band_norm_le_one n) (weight_norm_le_one u hu0 hu1 n)
    change ‖U.conjugateOperator g (band e n * u n * band e n) -
      band e n * u n * band e n‖ ≤
        2 * ‖U.conjugateOperator g (band e n) - band e n‖ +
          ‖U.conjugateOperator g (u n) - u n‖ at hbound
    linarith
  exact compact_action_error_of_summable_strong_series U g _ _
    (he.partitionSquare_finite_apply_tendsto u hu0 hu1)
    (finite_band_term_compact u hc) hsum

end ActualAction
end IsStrongIncreasingModuleResolution
end BC4lean.KKTheory
