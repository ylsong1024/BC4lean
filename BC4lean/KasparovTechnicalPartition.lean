import BC4lean.GradingConjugateOperator
import BC4lean.EquivariantOperatorAutomorphism
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.NoncommRing

/-! # The concrete partition consumed by the Kasparov product

This is the square-root convention of Gabe–Szabó, Theorem 2.6. The first
partition square has weights `1-uₙ`; the second has weights `uₙ`.
The product construction consumes the actual operators and every compact
control, including exact evenness and both discrete-family products.
The countable selection and band-limit construction supply these fields;
the structure itself is not an existence assumption.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance kasparovTechnicalPartitionLocalOrderInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovTechnicalPartitionLocalOrderInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- All actual operator controls of the even countable discrete technical
partition. The complete discrete family is retained in the statement. -/
structure KasparovTechnicalPartition
    {β : CStarGrading B} {α : CStarAlgebraAction Γ B}
    (γ : GradedHilbertModule β E) (U : EquivariantHilbertModule α E)
    (E₁ E₂ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    (Δ : Set (AdjointableMap B E E)) (f : ℕ → AdjointableMap B E E) where
  m : AdjointableMap B E E
  n : AdjointableMap B E E
  m_nonneg : 0 ≤ m
  n_nonneg : 0 ≤ n
  m_norm_le_one : ‖m‖ ≤ 1
  n_norm_le_one : ‖n‖ ≤ 1
  square_partition : m * m + n * n = 1
  m_even : GradedHilbertModule.IsEven γ γ m
  n_even : GradedHilbertModule.IsEven γ γ n
  first_ideal : ∀ a ∈ E₁, IsModuleCompact (m * a)
  second_ideal : ∀ b ∈ E₂, IsModuleCompact (n * b)
  commutator_m : ∀ d ∈ Δ, IsModuleCompact (m * d - d * m)
  commutator_n : ∀ d ∈ Δ, IsModuleCompact (n * d - d * n)
  action_m : ∀ g, IsModuleCompact (U.conjugateOperator g m - m)
  action_n : ∀ g, IsModuleCompact (U.conjugateOperator g n - n)
  family_left : ∀ k, IsModuleCompact (n * f k)
  family_right : ∀ k, IsModuleCompact (f k * n)

/-- The weights commute as a consequence of positivity and the actual
square partition; this is derived rather than an independent requirement. -/
theorem KasparovTechnicalPartition.weights_commute
    {β : CStarGrading B} {α : CStarAlgebraAction Γ B}
    {γ : GradedHilbertModule β E} {U : EquivariantHilbertModule α E}
    {E₁ E₂ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E)}
    {Δ : Set (AdjointableMap B E E)} {f : ℕ → AdjointableMap B E E}
    (p : KasparovTechnicalPartition γ U E₁ E₂ Δ f) : Commute p.m p.n := by
  have hsq : p.m * p.m = 1 - p.n * p.n := by
    rw [← p.square_partition]
    abel
  have hcomm : Commute (p.m * p.m) p.n := by
    change (p.m * p.m) * p.n = p.n * (p.m * p.m)
    rw [hsq]
    noncomm_ring
  have h := hcomm.cfcₙ_nnreal NNReal.sqrt
  change Commute (CFC.sqrt (p.m * p.m)) p.n at h
  simpa only [CFC.sqrt_mul_self p.m p.m_nonneg] using h

namespace KasparovTechnicalPartition
variable {β : CStarGrading B} {α : CStarAlgebraAction Γ B}
  {γ : GradedHilbertModule β E} {U : EquivariantHilbertModule α E}
  {E₁ E₂ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E)}
  {Δ : Set (AdjointableMap B E E)} {f : ℕ → AdjointableMap B E E}
  (p : KasparovTechnicalPartition γ U E₁ E₂ Δ f)

/-- The source theorem's left family product, valued in the actual
compact algebra with its inherited operator norm. -/
def familyLeftMap (k : ℕ) : CompactModuleOperator B E := ⟨p.n * f k, p.family_left k⟩

/-- The source theorem's right family product as an actual compact map. -/
def familyRightMap (k : ℕ) : CompactModuleOperator B E := ⟨f k * p.n, p.family_right k⟩

/-- On the countable discrete parameter space, the full compact-valued
left family product is norm-continuous. -/
theorem continuous_familyLeftMap : Continuous p.familyLeftMap := continuous_of_discreteTopology

theorem continuous_familyRightMap : Continuous p.familyRightMap := continuous_of_discreteTopology

end KasparovTechnicalPartition

/-- Actual positive contraction square roots are contractive, including
the zero algebra case. -/
theorem norm_cfcSqrt_le_one_of_nonneg_of_norm_le_one
    (M : AdjointableMap B E E) (hM0 : 0 ≤ M) (hM1 : ‖M‖ ≤ 1) : ‖CFC.sqrt M‖ ≤ 1 := by
  have hs : IsSelfAdjoint (CFC.sqrt M) := (CFC.sqrt_nonneg M).isSelfAdjoint
  have heq : ‖CFC.sqrt M‖ ^ 2 = ‖M‖ := by
    rw [← hs.norm_mul_self, CFC.sqrt_mul_sqrt_self M hM0]
  nlinarith [norm_nonneg (CFC.sqrt M)]

end BC4lean.KKTheory
