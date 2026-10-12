import BC4lean.ContractiveModuleCoordinateAnalysis
import BC4lean.ModuleOperatorPositivity
import BC4lean.CompactModuleApproximateUnit
import BC4lean.CompactModuleStrongResolution
import BC4lean.CompactModuleOperatorCriterion

/-! # Genuine coefficient-norm convergence for technical-theorem bands

An increasing strongly convergent positive operator resolution has square-root
bands. Multiplying each band by the square root of a positive contraction
gives coordinates whose coefficient squares are bounded by the band squares.
The band squares telescope. Their tails are bounded in coefficient order by
`⟪x,(eₘ-eₙ)x⟫`, which tends to zero in norm by actual strong convergence.
This proves the actual finite bound and Cauchy condition required to construct
the adjointable column and its positive source square.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped InnerProductSpace Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance kasparovBandCoordinatesLocalInst1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovBandCoordinatesLocalInst2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

namespace IsStrongIncreasingModuleResolution

variable {e : ℕ → AdjointableMap B E E} (he : IsStrongIncreasingModuleResolution e)

/-- The actual positive square-root band of the operator increment. -/
def band (e : ℕ → AdjointableMap B E E) (n : ℕ) : AdjointableMap B E E :=
  CFC.sqrt (e (n + 1) - e n)

include he in
theorem band_square (n : ℕ) : band e n * band e n = e (n + 1) - e n :=
  CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr (he.monotone (Nat.le_succ n)))

theorem band_star (n : ℕ) : star (band e n) = band e n :=
  (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq

private theorem inner_operator_mono {S T : AdjointableMap B E E} (hST : S ≤ T) (x : E) :
    ⟪x, S x⟫_(Bᵐᵒᵖ) ≤ ⟪x, T x⟫_(Bᵐᵒᵖ) := by
  have h := AdjointableMap.inner_nonneg_of_nonneg (T - S) (sub_nonneg.mpr hST) x
  simpa only [AdjointableMap.coe_sub_apply, CStarModule.inner_sub_right, sub_nonneg] using h

private theorem sqrt_inner (a : AdjointableMap B E E) (ha : 0 ≤ a) (x : E) :
    ⟪CFC.sqrt a x, CFC.sqrt a x⟫_(Bᵐᵒᵖ) = ⟪x, a x⟫_(Bᵐᵒᵖ) := by
  rw [(CFC.sqrt a).adjoint_identity]
  have hstar : (CFC.sqrt a).adjoint = CFC.sqrt a :=
    (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  change ⟪x, (CFC.sqrt a).adjoint (CFC.sqrt a x)⟫_(Bᵐᵒᵖ) = ⟪x, a x⟫_(Bᵐᵒᵖ)
  rw [hstar, ← AdjointableMap.mul_apply, CFC.sqrt_mul_sqrt_self a ha]

include he in
theorem band_inner (n : ℕ) (x : E) :
    ⟪band e n x, band e n x⟫_(Bᵐᵒᵖ) =
      ⟪x, (e (n + 1) - e n) x⟫_(Bᵐᵒᵖ) :=
  sqrt_inner _ (sub_nonneg.mpr (he.monotone (Nat.le_succ n))) x

include he in
/-- The finite band coefficient-square sums telescope exactly. -/
theorem band_inner_sum (N : ℕ) (x : E) :
    (∑ n ∈ Finset.range N, ⟪band e n x, band e n x⟫_(Bᵐᵒᵖ)) =
      ⟪x, (e N - e 0) x⟫_(Bᵐᵒᵖ) := by
  simp_rw [he.band_inner, AdjointableMap.coe_sub_apply, CStarModule.inner_sub_right]
  exact Finset.sum_range_sub (fun n => ⟪x, e n x⟫_(Bᵐᵒᵖ)) N

/-- The technical-theorem column coordinate before taking its actual limit. -/
def coordinate (e u : ℕ → AdjointableMap B E E) (n : ℕ) : AdjointableMap B E E :=
  CFC.sqrt (u n) * band e n

variable (u : ℕ → AdjointableMap B E E) (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1)

include hu0 hu1 in
theorem coordinate_inner_le_band (n : ℕ) (x : E) :
    ⟪coordinate e u n x, coordinate e u n x⟫_(Bᵐᵒᵖ) ≤
      ⟪band e n x, band e n x⟫_(Bᵐᵒᵖ) := by
  change ⟪CFC.sqrt (u n) (band e n x), CFC.sqrt (u n) (band e n x)⟫_(Bᵐᵒᵖ) ≤ _
  rw [sqrt_inner _ (hu0 n)]
  simpa only [AdjointableMap.one_apply] using inner_operator_mono (hu1 n) (band e n x)

include he hu0 hu1 in
theorem coordinate_finite_inner_le (N : ℕ) (x : E) :
    (∑ n ∈ Finset.range N, ⟪coordinate e u n x, coordinate e u n x⟫_(Bᵐᵒᵖ)) ≤
      ⟪x, x⟫_(Bᵐᵒᵖ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ⟪band e n x, band e n x⟫_(Bᵐᵒᵖ) :=
      Finset.sum_le_sum (fun n _ => coordinate_inner_le_band u hu0 hu1 n x)
    _ = ⟪x, e N x⟫_(Bᵐᵒᵖ) := by
      rw [he.band_inner_sum, he.zero, sub_zero]
    _ ≤ ⟪x, x⟫_(Bᵐᵒᵖ) := by
      simpa only [AdjointableMap.one_apply] using inner_operator_mono (he.le_one N) x

include he hu0 hu1 in
/-- Every finite coordinate-square tail is bounded in the true coefficient
order by the corresponding telescoping operator increment. -/
theorem coordinate_inner_tail_le {N M : ℕ} (hNM : N ≤ M) (x : E) :
    (∑ n ∈ Finset.range M, ⟪coordinate e u n x, coordinate e u n x⟫_(Bᵐᵒᵖ)) -
      (∑ n ∈ Finset.range N, ⟪coordinate e u n x, coordinate e u n x⟫_(Bᵐᵒᵖ)) ≤
      ⟪x, (e M - e N) x⟫_(Bᵐᵒᵖ) := by
  rw [← Finset.sum_sdiff_eq_sub (Finset.range_mono hNM)]
  calc
    _ ≤ ∑ n ∈ Finset.range M \ Finset.range N, ⟪band e n x, band e n x⟫_(Bᵐᵒᵖ) :=
      Finset.sum_le_sum (fun n _ => coordinate_inner_le_band u hu0 hu1 n x)
    _ = _ := by
      rw [Finset.sum_sdiff_eq_sub (Finset.range_mono hNM), he.band_inner_sum,
        he.band_inner_sum]
      simp only [AdjointableMap.coe_sub_apply, CStarModule.inner_sub_right]
      abel

include he hu0 hu1 in
theorem coordinate_tail_norm_sq_le {N M : ℕ} (hNM : N ≤ M) (x : E) :
    ‖countableModuleTruncation (B := B) (fun n => coordinate e u n x) M -
      countableModuleTruncation (B := B) (fun n => coordinate e u n x) N‖ ^ 2 ≤
      ‖x‖ * ‖e M x - e N x‖ := by
  rw [countableModuleTruncation_difference_norm_sq _ hNM]
  have hpos : 0 ≤
      (∑ n ∈ Finset.range M, ⟪coordinate e u n x, coordinate e u n x⟫_(Bᵐᵒᵖ)) -
        ∑ n ∈ Finset.range N, ⟪coordinate e u n x, coordinate e u n x⟫_(Bᵐᵒᵖ) := by
    rw [← Finset.sum_sdiff_eq_sub (Finset.range_mono hNM)]
    exact Finset.sum_nonneg (fun _ _ => CStarModule.inner_self_nonneg)
  calc
    _ ≤ ‖⟪x, (e M - e N) x⟫_(Bᵐᵒᵖ)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos
        (he.coordinate_inner_tail_le u hu0 hu1 hNM x)
    _ ≤ ‖x‖ * ‖(e M - e N) x‖ := CStarModule.norm_inner_le E
    _ = _ := by rw [AdjointableMap.coe_sub_apply]

include he hu0 hu1 in
/-- Actual strong convergence makes the finite band-column truncations
Cauchy in the genuine countable Hilbert-module norm. -/
theorem coordinate_truncation_cauchy (x : E) :
    CauchySeq (countableModuleTruncation (B := B) (fun n => coordinate e u n x)) :=
  moduleCoordinateTruncation_cauchy_of_strong_order_tails (coordinate e u) e he.strong
    (fun y _ _ hNM => he.coordinate_inner_tail_le u hu0 hu1 hNM y) x

include he hu0 hu1 in
/-- Both analytic hypotheses for the actual contractive adjointable column
are proved from the operator bands and genuine strong convergence. -/
theorem hasContractiveOperatorCoordinates : HasContractiveOperatorCoordinates (coordinate e u) where
  finite_inner_le := he.coordinate_finite_inner_le u hu0 hu1
  truncation_cauchy := he.coordinate_truncation_cauchy u hu0 hu1

/-- The actual positive source square of the proved band column. -/
def partitionSquare : AdjointableMap B E E :=
  (he.hasContractiveOperatorCoordinates u hu0 hu1).positiveSquare

theorem partitionSquare_nonneg : 0 ≤ he.partitionSquare u hu0 hu1 :=
  (he.hasContractiveOperatorCoordinates u hu0 hu1).positiveSquare_nonneg

theorem partitionSquare_le_one : he.partitionSquare u hu0 hu1 ≤ 1 :=
  (he.hasContractiveOperatorCoordinates u hu0 hu1).positiveSquare_le_one

private theorem sqrt_inner_mixed (a : AdjointableMap B E E) (ha : 0 ≤ a) (x y : E) :
    ⟪CFC.sqrt a x, CFC.sqrt a y⟫_(Bᵐᵒᵖ) = ⟪x, a y⟫_(Bᵐᵒᵖ) := by
  rw [(CFC.sqrt a).adjoint_identity]
  have hstar : (CFC.sqrt a).adjoint = CFC.sqrt a :=
    (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  change ⟪x, (CFC.sqrt a).adjoint (CFC.sqrt a y)⟫_(Bᵐᵒᵖ) = ⟪x, a y⟫_(Bᵐᵒᵖ)
  rw [hstar, ← AdjointableMap.mul_apply, CFC.sqrt_mul_sqrt_self a ha]

include he in
theorem band_inner_mixed (n : ℕ) (x y : E) :
    ⟪band e n x, band e n y⟫_(Bᵐᵒᵖ) =
      ⟪x, (e (n + 1) - e n) y⟫_(Bᵐᵒᵖ) :=
  sqrt_inner_mixed _ (sub_nonneg.mpr (he.monotone (Nat.le_succ n))) x y

include he in
theorem band_inner_mixed_sum (N : ℕ) (x y : E) :
    (∑ n ∈ Finset.range N, ⟪band e n x, band e n y⟫_(Bᵐᵒᵖ)) =
      ⟪x, (e N - e 0) y⟫_(Bᵐᵒᵖ) := by
  simp_rw [he.band_inner_mixed, AdjointableMap.coe_sub_apply, CStarModule.inner_sub_right]
  exact Finset.sum_range_sub (fun n => ⟪x, e n y⟫_(Bᵐᵒᵖ)) N

include he hu0 hu1 in
/-- Complementary weight columns have an exact finite coefficient sum. -/
theorem complementary_coordinate_inner_sum (N : ℕ) (x y : E) :
    (∑ n ∈ Finset.range N, ⟪coordinate e u n x, coordinate e u n y⟫_(Bᵐᵒᵖ)) +
      (∑ n ∈ Finset.range N,
        ⟪coordinate e (fun n => 1 - u n) n x,
          coordinate e (fun n => 1 - u n) n y⟫_(Bᵐᵒᵖ)) =
      ⟪x, e N y⟫_(Bᵐᵒᵖ) := by
  rw [← Finset.sum_add_distrib]
  have hterm (n : ℕ) :
      ⟪coordinate e u n x, coordinate e u n y⟫_(Bᵐᵒᵖ) +
        ⟪coordinate e (fun n => 1 - u n) n x,
          coordinate e (fun n => 1 - u n) n y⟫_(Bᵐᵒᵖ) =
      ⟪band e n x, band e n y⟫_(Bᵐᵒᵖ) := by
    change ⟪CFC.sqrt (u n) (band e n x), CFC.sqrt (u n) (band e n y)⟫_(Bᵐᵒᵖ) +
      ⟪CFC.sqrt (1 - u n) (band e n x), CFC.sqrt (1 - u n) (band e n y)⟫_(Bᵐᵒᵖ) = _
    rw [sqrt_inner_mixed _ (hu0 n), sqrt_inner_mixed _ (sub_nonneg.mpr (hu1 n)),
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, CStarModule.inner_sub_right]
    abel
  simp_rw [hterm]
  rw [he.band_inner_mixed_sum, he.zero, sub_zero]

/-- The two actual positive squares sum to the identity. This follows
from genuine coefficient-norm limits and actual strong band resolution. -/
theorem complementary_partitionSquare_add :
    he.partitionSquare u hu0 hu1 +
      he.partitionSquare (fun n => 1 - u n)
        (fun n => sub_nonneg.mpr (hu1 n))
        (fun n => sub_le_self _ (hu0 n)) = 1 := by
  apply AdjointableMap.ext
  intro y
  apply module_inner_ext_right (B := B)
  intro x
  let hX := he.hasContractiveOperatorCoordinates u hu0 hu1
  let hY := he.hasContractiveOperatorCoordinates (fun n => 1 - u n)
    (fun n => sub_nonneg.mpr (hu1 n)) (fun n => sub_le_self _ (hu0 n))
  have hsum := (hX.partial_inner_tendsto_positiveSquare x y).add
    (hY.partial_inner_tendsto_positiveSquare x y)
  have hstrong := ((CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := E)).tendsto (x, y)).comp
    ((tendsto_const_nhds (x := x)).prodMk_nhds (he.strong y))
  simp_rw [he.complementary_coordinate_inner_sum u hu0 hu1] at hsum
  have h := tendsto_nhds_unique hsum hstrong
  simpa only [partitionSquare, hX, hY, AdjointableMap.coe_add_apply,
    AdjointableMap.one_apply, CStarModule.inner_add_right] using h

include hu0 in
/-- Each coordinate source square is the actual weighted band term. -/
theorem coordinate_source_square (n : ℕ) :
    (coordinate e u n).adjoint.comp (coordinate e u n) = band e n * u n * band e n := by
  change star (CFC.sqrt (u n) * band e n) * (CFC.sqrt (u n) * band e n) = _
  rw [star_mul, band_star, (CFC.sqrt_nonneg (u n)).isSelfAdjoint.star_eq]
  calc
    _ = band e n * (CFC.sqrt (u n) * CFC.sqrt (u n)) * band e n := by noncomm_ring
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self _ (hu0 n)]

/-- The finite weighted-band operators converge strongly to the genuine
positive column square, by continuity of the actual adjoint row. -/
theorem partitionSquare_finite_apply_tendsto (x : E) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, band e n * u n * band e n) x)
      atTop (𝓝 (he.partitionSquare u hu0 hu1 x)) := by
  let hX := he.hasContractiveOperatorCoordinates u hu0 hu1
  have htrunc (N : ℕ) :
      countableModuleTruncation (B := B) (fun n => coordinate e u n x) N =
        ∑ n ∈ Finset.range N, countableModuleInclusion (B := B) n (coordinate e u n x) := by
    unfold countableModuleTruncation countableModuleFiniteSection
    simp only [map_sum, countableModuleInclusion_apply]
  have hrow (N : ℕ) :
      hX.synthesis (countableModuleTruncation (B := B) (fun n => coordinate e u n x) N) =
        (∑ n ∈ Finset.range N, band e n * u n * band e n) x := by
    rw [htrunc, map_sum]
    simp only [hX.synthesis_inclusion]
    have hterm (n : ℕ) :
        (coordinate e u n).adjoint (coordinate e u n x) = (band e n * u n * band e n) x :=
      congrArg (fun T : AdjointableMap B E E => T x) (coordinate_source_square u hu0 n)
    simp_rw [hterm]
    have hsum (s : Finset ℕ) :
        (∑ n ∈ s, band e n * u n * band e n) x =
          ∑ n ∈ s, (band e n * u n * band e n) x := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert n s hn ih => simp only [Finset.sum_insert hn, AdjointableMap.coe_add_apply, ih]
    exact (hsum _).symm
  have ht := hX.synthesis.toCLM.continuous.tendsto (hX.analysisSum x) |>.comp
    (hX.truncation_tendsto x)
  change Tendsto (fun N => hX.synthesis
    (countableModuleTruncation (B := B) (fun n => coordinate e u n x) N)) atTop
      (𝓝 (hX.synthesis (hX.analysisSum x))) at ht
  have hlimit : hX.synthesis (hX.analysisSum x) = he.partitionSquare u hu0 hu1 x := by
    change hX.synthesis (hX.column x) = hX.column.adjoint (hX.column x)
    rw [HasContractiveOperatorCoordinates.column, AdjointableMap.adjoint_adjoint]
  simpa only [hrow, hlimit] using ht

end IsStrongIncreasingModuleResolution

local instance kasparovBandCoordinatesLocalInst3 : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
local instance kasparovBandCoordinatesCompactPreorder : Preorder (CompactModuleOperator B E) :=
  (CStarAlgebra.spectralOrder (CompactModuleOperator B E)).toPreorder
local instance kasparovBandCoordinatesCompactLE : LE (CompactModuleOperator B E) :=
  (CStarAlgebra.spectralOrder (CompactModuleOperator B E)).toLE
local instance kasparovBandCoordinatesLocalInst4 : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _

/-- The actual positive CFC square root of a compact operator is compact,
by the proved compactness criterion for its actual adjoint square. -/
theorem IsModuleCompact.cfcSqrt {T : AdjointableMap B E E}
    (hT : IsModuleCompact T) (hpos : 0 ≤ T) : IsModuleCompact (CFC.sqrt T) := by
  apply IsModuleCompact.of_adjoint_comp_self
  change IsModuleCompact (star (CFC.sqrt T) * CFC.sqrt T)
  rw [(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self T hpos]
  exact hT

/-- Square-root bands of an increasing actual compact sequence are compact. -/
theorem compact_sequence_band_isModuleCompact
    (v : ℕ → CompactModuleOperator B E) (hMono : Monotone v) (n : ℕ) :
    IsModuleCompact (IsStrongIncreasingModuleResolution.band
      (fun k => (v k : AdjointableMap B E E)) n) := by
  have hcompact : IsModuleCompact
      ((v (n + 1) : AdjointableMap B E E) - (v n : AdjointableMap B E E)) :=
    IsModuleCompact.sub (v (n + 1)).property (v n).property
  apply hcompact.cfcSqrt
  apply sub_nonneg.mpr
  exact OrderHomClass.mono
    (NonUnitalStarSubalgebraClass.subtype (compactModuleOperatorAlgebra (B := B) (E := E)))
    (hMono (Nat.le_succ n))

/-- Every finite weighted-band source square is genuinely compact. -/
theorem compact_sequence_finite_band_sum_isModuleCompact
    (v : ℕ → CompactModuleOperator B E) (hMono : Monotone v)
    (u : ℕ → AdjointableMap B E E) (N : ℕ) :
    IsModuleCompact (∑ n ∈ Finset.range N,
      IsStrongIncreasingModuleResolution.band (fun k => (v k : AdjointableMap B E E)) n *
        u n * IsStrongIncreasingModuleResolution.band
          (fun k => (v k : AdjointableMap B E E)) n) := by
  apply Submodule.sum_mem
  intro n _
  exact ((compact_sequence_band_isModuleCompact v hMono n).comp_right (u n)).comp_right _

end BC4lean.KKTheory
