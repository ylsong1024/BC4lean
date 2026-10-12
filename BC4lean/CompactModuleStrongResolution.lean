import BC4lean.CompactModuleApproximateUnit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Actual increasing strong module resolutions from compact AUs

The compact approximate-unit sequence acts strongly on the original
Hilbert module by the rank-one norm estimate. This property is independent
of the later column construction for the technical-theorem bands.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance compactModuleStrongResolutionLocalOrderInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance compactModuleStrongResolutionLocalOrderInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance compactModuleStrongResolutionLocalOrderInstance03 : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
local instance compactModuleStrongResolutionLocalOrderInstance04 : Preorder (CompactModuleOperator B E) :=
  (CStarAlgebra.spectralOrder (CompactModuleOperator B E)).toPreorder
local instance compactModuleStrongResolutionLocalOrderInstance05 : LE (CompactModuleOperator B E) :=
  (CStarAlgebra.spectralOrder (CompactModuleOperator B E)).toLE
local instance compactModuleStrongResolutionLocalOrderInstance06 : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _

/-- The actual properties of an increasing strong operator resolution. -/
structure IsStrongIncreasingModuleResolution (e : ℕ → AdjointableMap B E E) : Prop where
  zero : e 0 = 0
  monotone : Monotone e
  le_one (n : ℕ) : e n ≤ 1
  strong (x : E) : Tendsto (fun n => e n x) atTop (𝓝 x)

theorem IsStrongIncreasingModuleResolution.nonneg
    {e : ℕ → AdjointableMap B E E} (he : IsStrongIncreasingModuleResolution e) (n : ℕ) :
    0 ≤ e n := by
  rw [← he.zero]
  exact he.monotone (Nat.zero_le n)

/-- A genuine two-sided compact AU supplies every strong-resolution
property, using the proved rank-one estimate on the original module. -/
theorem strongIncreasingModuleResolution_of_compact_sequence
    (u : ℕ → CompactModuleOperator B E) (huZero : u 0 = 0) (huMono : Monotone u)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, ‖u n‖ ≤ 1)
    (hleft : ∀ a, Tendsto (fun n => a * u n) atTop (𝓝 a))
    (hright : ∀ a, Tendsto (fun n => u n * a) atTop (𝓝 a)) :
    IsStrongIncreasingModuleResolution (fun n => (u n : AdjointableMap B E E)) where
  zero := congrArg Subtype.val huZero
  monotone := by
    intro n m hnm
    exact OrderHomClass.mono
      (NonUnitalStarSubalgebraClass.subtype (compactModuleOperatorAlgebra (B := B) (E := E)))
      (huMono hnm)
  le_one n := by
    have hnonneg : 0 ≤ (u n : AdjointableMap B E E) := map_nonneg
      (NonUnitalStarSubalgebraClass.subtype (compactModuleOperatorAlgebra (B := B) (E := E)))
      (hu0 n)
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnonneg).mp (hu1 n)
  strong := tendsto_compact_sequence_apply u hu0 hu1 hleft hright

end BC4lean.KKTheory
