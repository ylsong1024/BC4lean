import BC4lean.KasparovOperatorAlgebraActions

/-! # Discharging the band bounds from the actual recursive selections

The paired selector's concrete inequalities give all numerical controls
used by the norm-series ideal proofs. The compact sequence's genuine AU
property supplies the actual strong resolution; it is not assumed to act
essentially. The action compatibility is the real restricted ambient
module action from the preceding restriction construction.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance kasparovSelectedBandBoundsLocalInst1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovSelectedBandBoundsLocalInst2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance kasparovSelectedBandBoundsLocalInst3 : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
local instance kasparovSelectedBandBoundsLocalInst4 : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _

variable {U : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E)} [IsClosed (U : Set (AdjointableMap B E E))]
local instance kasparovSelectedBandBoundsLocalInst5 : PartialOrder U := CStarAlgebra.spectralOrder _
local instance kasparovSelectedBandBoundsLocalInst6 : StarOrderedRing U := CStarAlgebra.spectralOrderedRing _

namespace IsKasparovCountableSelection
variable {δ t b : ℕ → AdjointableMap B E E} {qU : ℕ → U}
  {qK : ℕ → CompactModuleOperator B E} {γ : ℕ → Γ}
  {αU : Γ → U ≃⋆ₐ[ℂ] U} {αK : Γ → CompactModuleOperator B E ≃⋆ₐ[ℂ] CompactModuleOperator B E}
  {τ : ℕ → ℝ} {u : ℕ → U} {e : ℕ → CompactModuleOperator B E}
  (h : IsKasparovCountableSelection U (compactModuleOperatorAlgebra (B := B) (E := E))
    δ t b qU qK γ αU αK τ u e)

include h in
omit [Group Γ] in
theorem mappedWeight_nonneg (n : ℕ) : 0 ≤ (u n : AdjointableMap B E E) := by
  obtain ⟨v, hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (h.nonnegU n)
  have hv' : (u n : AdjointableMap B E E) =
      star (v : AdjointableMap B E E) * (v : AdjointableMap B E E) :=
    congrArg (fun a : U => (a : AdjointableMap B E E)) hv
  rw [hv']
  exact star_mul_self_nonneg (v : AdjointableMap B E E)

include h in
omit [Group Γ] in
theorem mappedWeight_le_one (n : ℕ) : (u n : AdjointableMap B E E) ≤ 1 := by
  have hn : ‖(u n : AdjointableMap B E E)‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le (NonUnitalStarSubalgebraClass.subtype U) (u n)).trans
      (h.strictU n).le
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h.mappedWeight_nonneg n)).mp hn

include h in
omit [Group Γ] in
/-- The constructed compact AU is an actual strong operator resolution. -/
theorem strongModuleResolution
    (hqleft : ∀ a, Tendsto (fun n => a * qK n) atTop (𝓝 a))
    (hqright : ∀ a, Tendsto (fun n => qK n * a) atTop (𝓝 a)) :
    IsStrongIncreasingModuleResolution (fun n => (e n : AdjointableMap B E E)) :=
  strongIncreasingModuleResolution_of_compact_sequence e h.zeroK h.monotoneK h.nonnegK
    (fun n => (h.strictK n).le)
    (fun a => (h.approximateUnitK hqleft hqright a).1)
    (fun a => (h.approximateUnitK hqleft hqright a).2)

include h in
omit [Group Γ] in
private theorem compact_endpoint_commutator_bound
    (hτ : IsKasparovBandControlTolerance t τ) (n k : ℕ) (hk : k ≤ n) :
    ‖(e n : AdjointableMap B E E) * t k - t k * (e n : AdjointableMap B E E)‖ < τ n := by
  by_cases hn : n = 0
  · subst n
    rw [h.zeroK]
    simpa using hτ.positive 0
  · exact h.commutatorK n (by omega) k hk

include h in
omit [Group Γ] in
/-- Both selected endpoints enter the actual CFC band modulus, giving
the geometric square-root commutator bound for every fixed test index. -/
theorem band_commutator_bound
    (hτ : IsKasparovBandControlTolerance t τ)
    (he : IsStrongIncreasingModuleResolution (fun n => (e n : AdjointableMap B E E)))
    (n k : ℕ) (hk : k ≤ n) :
    ‖IsStrongIncreasingModuleResolution.band (fun n => (e n : AdjointableMap B E E)) n * t k -
      t k * IsStrongIncreasingModuleResolution.band (fun n => (e n : AdjointableMap B E E)) n‖ <
        kasparovSelectionBudget n := by
  have hinc := positive_contractive_increment (e n : AdjointableMap B E E)
    (e (n + 1) : AdjointableMap B E E) (he.nonneg n)
    (he.monotone (Nat.le_succ n)) (h.strictK (n + 1)).le
  exact hτ.commutator n k hk _ _ hinc.1 hinc.2
    (h.compact_endpoint_commutator_bound hτ n k hk)
    (h.compact_endpoint_commutator_bound hτ (n + 1) k (hk.trans (Nat.le_succ n)))

section ActualAction
variable {α : CStarAlgebraAction Γ B} (V : EquivariantHilbertModule α E)
  (hαK : ∀ g a, (αK g a : AdjointableMap B E E) = V.conjugateOperator g a)
  (hαU : ∀ g a, (αU g a : AdjointableMap B E E) = V.conjugateOperator g a)

include h hαK in
private theorem compact_endpoint_action_bound
    (hτ : IsKasparovBandControlTolerance t τ) (n k : ℕ) (hk : k ≤ n) :
    ‖V.conjugateOperator (γ k) (e n : AdjointableMap B E E) - (e n : AdjointableMap B E E)‖ < τ n := by
  by_cases hn : n = 0
  · subst n
    rw [h.zeroK]
    change ‖V.conjugateOperator (γ k) 0 - 0‖ < τ 0
    have hz : V.conjugateOperator (γ k) (0 : AdjointableMap B E E) = 0 := by
      apply AdjointableMap.ext
      intro x
      change V.action (γ k) (0 : E) = 0
      exact map_zero _
    rw [hz, sub_zero, norm_zero]
    exact hτ.positive 0
  · have hb := h.actionK n (by omega) k hk
    have heq : (αK (γ k) (e n) - e n : CompactModuleOperator B E).val =
        V.conjugateOperator (γ k) (e n) - (e n : AdjointableMap B E E) := by
      exact congrArg (fun T => T - (e n : AdjointableMap B E E)) (hαK (γ k) (e n))
    rw [← heq]
    exact (NonUnitalStarAlgHom.norm_apply_le
      (NonUnitalStarSubalgebraClass.subtype
        (compactModuleOperatorAlgebra (B := B) (E := E)))
      (αK (γ k) (e n) - e n)).trans_lt hb

include h hαK in
theorem band_action_bound
    (hτ : IsKasparovBandControlTolerance t τ)
    (he : IsStrongIncreasingModuleResolution (fun n => (e n : AdjointableMap B E E)))
    (n k : ℕ) (hk : k ≤ n) :
    ‖V.conjugateOperator (γ k)
      (IsStrongIncreasingModuleResolution.band (fun n => (e n : AdjointableMap B E E)) n) -
      IsStrongIncreasingModuleResolution.band (fun n => (e n : AdjointableMap B E E)) n‖ <
        kasparovSelectionBudget n := by
  have hinc := positive_contractive_increment (e n : AdjointableMap B E E)
    (e (n + 1) : AdjointableMap B E E) (he.nonneg n)
    (he.monotone (Nat.le_succ n)) (h.strictK (n + 1)).le
  exact hτ.action n (V.conjugateOperatorStarAlgEquiv (γ k)) _ _ hinc.1 hinc.2
    (h.compact_endpoint_action_bound V hαK hτ n k hk)
    (h.compact_endpoint_action_bound V hαK hτ (n + 1) k (hk.trans (Nat.le_succ n)))

include h hαU in
theorem mappedWeight_action_bound (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ‖V.conjugateOperator (γ k) (u n : AdjointableMap B E E) - (u n : AdjointableMap B E E)‖ <
      kasparovSelectionBudget n := by
  have hb := h.actionU n hn k hk
  have heq : (αU (γ k) (u n) - u n : U).val =
      V.conjugateOperator (γ k) (u n) - (u n : AdjointableMap B E E) := by
    exact congrArg (fun T => T - (u n : AdjointableMap B E E)) (hαU (γ k) (u n))
  rw [← heq]
  exact (NonUnitalStarAlgHom.norm_apply_le (NonUnitalStarSubalgebraClass.subtype U)
    (αU (γ k) (u n) - u n)).trans_lt hb

end ActualAction

include h in
omit [Group Γ] in
/-- The actual first coefficient tests give the complementary weight
error used in the first ideal-product series. -/
theorem complementary_unit_bound (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ‖(1 - (u n : AdjointableMap B E E)) * (qU k : AdjointableMap B E E)‖ <
      kasparovSelectionBudget n := by
  rw [sub_mul, one_mul, norm_sub_rev]
  exact (h.testsU n hn k hk).2

end IsKasparovCountableSelection
end BC4lean.KKTheory
