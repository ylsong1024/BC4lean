import BC4lean.KasparovTechnicalPartition
import BC4lean.GradingConjugateOperator
import BC4lean.KasparovSquareRootCompactControls

/-! # Exact evenness of the constructed square partition

Averaging both genuine source squares under grading conjugation preserves
their sum and all compact controls. The countable construction includes the
grading images of the commutator and family tests. Positive square roots
then give the actual even technical partition required by the product.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped Topology

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] {β : CStarGrading B} {α : CStarAlgebraAction Γ B}

local instance kasparovEvenSquarePartitionLocalInst1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovEvenSquarePartitionLocalInst2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

namespace GradedHilbertModule

/-- The genuine positive-square average under actual grading conjugation. -/
def evenSquare (γ : GradedHilbertModule β E) (M : AdjointableMap B E E) :
    AdjointableMap B E E := (1 / 2 : ℝ) • (M + γ.conjugateOperator M)

theorem evenSquare_nonneg (γ : GradedHilbertModule β E) (M : AdjointableMap B E E)
    (hM : 0 ≤ M) : 0 ≤ γ.evenSquare M :=
  smul_nonneg (by norm_num) (add_nonneg hM (map_nonneg γ.conjugateOperatorStarAlgEquiv hM))

theorem evenSquare_norm_le_one (γ : GradedHilbertModule β E) (M : AdjointableMap B E E)
    (hM : ‖M‖ ≤ 1) : ‖γ.evenSquare M‖ ≤ 1 := by
  have hσnorm : ‖γ.conjugateOperator M‖ = ‖M‖ := StarAlgEquiv.norm_map γ.conjugateOperatorStarAlgEquiv M
  calc
    ‖γ.evenSquare M‖ = (1 / 2 : ℝ) * ‖M + γ.conjugateOperator M‖ := by
      rw [evenSquare, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖M‖ + ‖γ.conjugateOperator M‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ 1 := by rw [hσnorm]; linarith

theorem evenSquare_even (γ : GradedHilbertModule β E) (M : AdjointableMap B E E) :
    IsEven γ γ (γ.evenSquare M) := by
  apply (γ.conjugateOperator_eq_self_iff _).mp
  change γ.conjugateOperatorStarAlgEquiv (γ.evenSquare M) = _
  simp only [evenSquare, LinearMapClass.map_smul_of_tower (S := ℂ), map_add,
    conjugateOperatorStarAlgEquiv_apply, conjugateOperator_involutive]
  rw [add_comm]

theorem evenSquare_partition (γ : GradedHilbertModule β E) (M N : AdjointableMap B E E)
    (hMN : M + N = 1) : γ.evenSquare M + γ.evenSquare N = 1 := by
  let σ := γ.conjugateOperatorStarAlgEquiv
  have heq : γ.evenSquare M + γ.evenSquare N = (1 / 2 : ℝ) • ((M + N) + σ (M + N)) := by
    simp only [evenSquare, map_add, σ, conjugateOperatorStarAlgEquiv_apply, smul_add]
    abel
  rw [heq, hMN, map_one]
  rw [← two_smul ℝ (1 : AdjointableMap B E E), smul_smul]
  norm_num

private theorem compact_real_smul {T : AdjointableMap B E E} (hT : IsModuleCompact T) (r : ℝ) :
    IsModuleCompact (r • T) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact hT.smul (r : ℂ)

/-- Both first and second ideal-product controls survive exact averaging
when the corresponding source algebra is grading stable. -/
theorem evenSquare_compact_product (γ : GradedHilbertModule β E)
    (M a : AdjointableMap B E E)
    (hMa : IsModuleCompact (M * a))
    (hMσa : IsModuleCompact (M * γ.conjugateOperator a)) :
    IsModuleCompact (γ.evenSquare M * a) := by
  let σ := γ.conjugateOperatorStarAlgEquiv
  have hsecond : IsModuleCompact (γ.conjugateOperator M * a) := by
    have h := γ.conjugateOperator_mem_moduleCompact hMσa
    change IsModuleCompact (σ (M * σ a)) at h
    simpa only [map_mul, σ, conjugateOperatorStarAlgEquiv_apply, conjugateOperator_involutive] using h
  simpa only [evenSquare, smul_mul_assoc, add_mul] using
    compact_real_smul (hMa.add hsecond) (1 / 2)

theorem evenSquare_compact_commutator (γ : GradedHilbertModule β E)
    (M d : AdjointableMap B E E)
    (hMd : IsModuleCompact (M * d - d * M))
    (hMσd : IsModuleCompact (M * γ.conjugateOperator d - γ.conjugateOperator d * M)) :
    IsModuleCompact (γ.evenSquare M * d - d * γ.evenSquare M) := by
  let σ := γ.conjugateOperatorStarAlgEquiv
  have hsecond : IsModuleCompact (γ.conjugateOperator M * d - d * γ.conjugateOperator M) := by
    have h := γ.conjugateOperator_mem_moduleCompact hMσd
    change IsModuleCompact (σ (M * σ d - σ d * M)) at h
    simpa only [map_sub, map_mul, σ, conjugateOperatorStarAlgEquiv_apply, conjugateOperator_involutive] using h
  have heq : γ.evenSquare M * d - d * γ.evenSquare M = (1 / 2 : ℝ) •
      ((M * d - d * M) + (γ.conjugateOperator M * d - d * γ.conjugateOperator M)) := by
    simp only [evenSquare, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, add_mul, mul_add]
    abel
  rw [heq]
  exact compact_real_smul (hMd.add hsecond) (1 / 2)

theorem evenSquare_compact_action_error (γ : GradedHilbertModule β E)
    (U : EquivariantHilbertModule α E) (hU : U.PreservesGrading γ) (g : Γ)
    (M : AdjointableMap B E E) (hM : IsModuleCompact (U.conjugateOperator g M - M)) :
    IsModuleCompact (U.conjugateOperator g (γ.evenSquare M) - γ.evenSquare M) := by
  let σ := γ.conjugateOperatorStarAlgEquiv
  let ρ := U.conjugateOperatorStarAlgEquiv g
  have heq : U.conjugateOperator g (γ.evenSquare M) - γ.evenSquare M =
      (1 / 2 : ℝ) • ((U.conjugateOperator g M - M) + σ (U.conjugateOperator g M - M)) := by
    change ρ ((1 / 2 : ℝ) • (M + σ M)) - (1 / 2 : ℝ) • (M + σ M) = _
    simp only [LinearMapClass.map_smul_of_tower (S := ℂ), map_add, map_sub, σ, ρ,
      conjugateOperatorStarAlgEquiv_apply, EquivariantHilbertModule.conjugateOperatorStarAlgEquiv]
    rw [γ.conjugateOperator_commutes_action U hU g M]
    module
  rw [heq]
  exact compact_real_smul (hM.add (γ.conjugateOperator_mem_moduleCompact hM)) (1 / 2)

end GradedHilbertModule

/-- The actual compact source-square controls, including the explicitly
added grading-image family tests, give the exact even square-root partition.
This is the final conversion step of the constructed band theorem. -/
def KasparovTechnicalPartition.ofSourceSquares
    (γ : GradedHilbertModule β E) (U : EquivariantHilbertModule α E)
    (hU : U.PreservesGrading γ)
    (E₁ E₂ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    (Δ : Set (AdjointableMap B E E)) (f : ℕ → AdjointableMap B E E)
    (hE₁ : ∀ a ∈ E₁, γ.conjugateOperator a ∈ E₁)
    (hE₂ : ∀ a ∈ E₂, γ.conjugateOperator a ∈ E₂)
    (M N : AdjointableMap B E E) (hM0 : 0 ≤ M) (hN0 : 0 ≤ N)
    (hM1 : ‖M‖ ≤ 1) (hN1 : ‖N‖ ≤ 1) (hMN : M + N = 1)
    (hfirst : ∀ a ∈ E₁, IsModuleCompact (M * a))
    (hsecond : ∀ a ∈ E₂, IsModuleCompact (N * a))
    (hcommM : ∀ d ∈ Δ, IsModuleCompact (M * d - d * M) ∧
      IsModuleCompact (M * γ.conjugateOperator d - γ.conjugateOperator d * M))
    (hcommN : ∀ d ∈ Δ, IsModuleCompact (N * d - d * N) ∧
      IsModuleCompact (N * γ.conjugateOperator d - γ.conjugateOperator d * N))
    (hactionM : ∀ g, IsModuleCompact (U.conjugateOperator g M - M))
    (hactionN : ∀ g, IsModuleCompact (U.conjugateOperator g N - N))
    (hfamily : ∀ k, IsModuleCompact (N * f k) ∧ IsModuleCompact (N * star (f k)) ∧
      IsModuleCompact (N * γ.conjugateOperator (f k)) ∧
      IsModuleCompact (N * γ.conjugateOperator (star (f k)))) :
    KasparovTechnicalPartition γ U E₁ E₂ Δ f := by
  let M' := γ.evenSquare M
  let N' := γ.evenSquare N
  have hM'0 : 0 ≤ M' := γ.evenSquare_nonneg M hM0
  have hN'0 : 0 ≤ N' := γ.evenSquare_nonneg N hN0
  have hM'1 : ‖M'‖ ≤ 1 := γ.evenSquare_norm_le_one M hM1
  have hN'1 : ‖N'‖ ≤ 1 := γ.evenSquare_norm_le_one N hN1
  refine
    { m := CFC.sqrt M'
      n := CFC.sqrt N'
      m_nonneg := CFC.sqrt_nonneg M'
      n_nonneg := CFC.sqrt_nonneg N'
      m_norm_le_one := norm_cfcSqrt_le_one_of_nonneg_of_norm_le_one M' hM'0 hM'1
      n_norm_le_one := norm_cfcSqrt_le_one_of_nonneg_of_norm_le_one N' hN'0 hN'1
      square_partition := ?_
      m_even := (γ.evenSquare_even M).cfcSqrt hM'0
      n_even := (γ.evenSquare_even N).cfcSqrt hN'0
      first_ideal := fun a ha =>
        (γ.evenSquare_compact_product M a (hfirst a ha) (hfirst _ (hE₁ a ha))).sqrt_mul hM'0
      second_ideal := fun a ha =>
        (γ.evenSquare_compact_product N a (hsecond a ha) (hsecond _ (hE₂ a ha))).sqrt_mul hN'0
      commutator_m := fun d hd =>
        (γ.evenSquare_compact_commutator M d (hcommM d hd).1 (hcommM d hd).2).sqrt_commutator hM'0 hM'1
      commutator_n := fun d hd =>
        (γ.evenSquare_compact_commutator N d (hcommN d hd).1 (hcommN d hd).2).sqrt_commutator hN'0 hN'1
      action_m := fun g =>
        (γ.evenSquare_compact_action_error U hU g M (hactionM g)).sqrt_action_error U g hM'0 hM'1
      action_n := fun g =>
        (γ.evenSquare_compact_action_error U hU g N (hactionN g)).sqrt_action_error U g hN'0 hN'1
      family_left := fun k =>
        (γ.evenSquare_compact_product N (f k) (hfamily k).1 (hfamily k).2.2.1).sqrt_mul hN'0
      family_right := ?_ }
  · rw [CFC.sqrt_mul_sqrt_self M' hM'0, CFC.sqrt_mul_sqrt_self N' hN'0]
    exact γ.evenSquare_partition M N hMN
  · intro k
    have h := (γ.evenSquare_compact_product N (star (f k))
      (hfamily k).2.1 (hfamily k).2.2.2).sqrt_mul hN'0
    have ha := h.adjoint
    change IsModuleCompact (star (CFC.sqrt N' * star (f k))) at ha
    simpa only [star_mul, star_star, (CFC.sqrt_nonneg N').isSelfAdjoint.star_eq] using ha

end BC4lean.KKTheory
