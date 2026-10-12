import BC4lean.KasparovBandCompactLimits
import BC4lean.EquivariantOperatorAutomorphism

/-! # Compact controls pass to the actual square-root partition

Rectangular compactness of an adjointable map follows from compactness of
its actual adjoint square. Polynomial telescoping and uniform CFC
approximation carry compact commutators and action differences to square
roots. This supplies the m,n convention of the source technical theorem
from the M,N source squares.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance kasparovSquareRootCompactControlsLocalInst1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovSquareRootCompactControlsLocalInst2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- A positive operator square's compact product gives the compact
product for its actual square root, by the true adjoint-square criterion. -/
theorem IsModuleCompact.sqrt_mul {M a : AdjointableMap B E E}
    (hMa : IsModuleCompact (M * a)) (hM : 0 ≤ M) : IsModuleCompact (CFC.sqrt M * a) := by
  apply IsModuleCompact.of_adjoint_comp_self
  change IsModuleCompact (star (CFC.sqrt M * a) * (CFC.sqrt M * a))
  have heq : star (CFC.sqrt M * a) * (CFC.sqrt M * a) = star a * (M * a) := by
    rw [star_mul, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
    calc
      _ = star a * ((CFC.sqrt M * CFC.sqrt M) * a) := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self M hM]
  rw [heq]
  exact hMa.comp_left (star a)

omit [CompleteSpace E] in
/-- Power commutators remain in the actual compact ideal by the
noncommutative telescoping identity. -/
theorem IsModuleCompact.power_commutator {M a : AdjointableMap B E E}
    (hMa : IsModuleCompact (M * a - a * M)) (k : ℕ) :
    IsModuleCompact (M ^ k * a - a * M ^ k) := by
  induction k with
  | zero => simpa using (IsModuleCompact.zero (B := B) (E := E) (F := E))
  | succ k ih =>
    have heq : M ^ (k + 1) * a - a * M ^ (k + 1) =
        M ^ k * (M * a - a * M) + (M ^ k * a - a * M ^ k) * M := by
      rw [pow_succ]
      noncomm_ring
    rw [heq]
    exact (hMa.comp_left (M ^ k)).add (ih.comp_right M)

omit [CompleteSpace E] in
theorem IsModuleCompact.polynomial_commutator {M a : AdjointableMap B E E}
    (hMa : IsModuleCompact (M * a - a * M)) (p : Polynomial ℝ) :
    IsModuleCompact (Polynomial.aeval M p * a - a * Polynomial.aeval M p) := by
  have heq : Polynomial.aeval M p * a - a * Polynomial.aeval M p =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (M ^ k * a - a * M ^ k) := by
    simp only [Polynomial.aeval_eq_sum_range, Finset.sum_mul, Finset.mul_sum,
      smul_sub, smul_mul_assoc, mul_smul_comm, Finset.sum_sub_distrib]
  rw [heq]
  apply (moduleCompact B E E).sum_mem
  intro k _
  change IsModuleCompact ((p.coeff k : ℝ) • (M ^ k * a - a * M ^ k))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (hMa.power_commutator k).smul (p.coeff k : ℂ)

/-- Compact commutators pass to the actual CFC square root by genuine
operator-norm polynomial approximation. Zero modules are included. -/
theorem IsModuleCompact.sqrt_commutator {M a : AdjointableMap B E E}
    (hMa : IsModuleCompact (M * a - a * M)) (hM0 : 0 ≤ M) (hM1 : ‖M‖ ≤ 1) :
    IsModuleCompact (CFC.sqrt M * a - a * CFC.sqrt M) := by
  rcases subsingleton_or_nontrivial (AdjointableMap B E E) with h | h
  · let := h
    simpa only [Subsingleton.elim (CFC.sqrt M * a - a * CFC.sqrt M) 0] using
      (IsModuleCompact.zero (B := B) (E := E) (F := E))
  · let := h
    let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    choose p hp using fun n => exists_polynomial_uniformly_approximating_cfc_sqrt
      (A := AdjointableMap B E E) (ε n) (by dsimp [ε]; positivity)
    let z : ℕ → AdjointableMap B E E := fun n => Polynomial.aeval M (p n) * a -
      a * Polynomial.aeval M (p n)
    have hbound (n : ℕ) : ‖z n - (CFC.sqrt M * a - a * CFC.sqrt M)‖ ≤
        (2 * ‖a‖) * ε n := by
      have heq : z n - (CFC.sqrt M * a - a * CFC.sqrt M) =
          (Polynomial.aeval M (p n) - CFC.sqrt M) * a -
            a * (Polynomial.aeval M (p n) - CFC.sqrt M) := by
        dsimp [z]
        noncomm_ring
      rw [heq]
      have ha := hp n M hM0 hM1
      rw [norm_sub_rev] at ha
      calc
        _ ≤ ‖(Polynomial.aeval M (p n) - CFC.sqrt M) * a‖ +
            ‖a * (Polynomial.aeval M (p n) - CFC.sqrt M)‖ := norm_sub_le _ _
        _ ≤ ‖Polynomial.aeval M (p n) - CFC.sqrt M‖ * ‖a‖ +
            ‖a‖ * ‖Polynomial.aeval M (p n) - CFC.sqrt M‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ε n * ‖a‖ + ‖a‖ * ε n := by gcongr
        _ = _ := by ring
    have hlim : Tendsto z atTop (𝓝 (CFC.sqrt M * a - a * CFC.sqrt M)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero (fun _ => norm_nonneg _) hbound
      simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖a‖)
    exact IsModuleCompact.of_tendsto hlim (Eventually.of_forall fun n => hMa.polynomial_commutator (p n))

omit [CompleteSpace E] in
theorem IsModuleCompact.power_difference {M N : AdjointableMap B E E}
    (hMN : IsModuleCompact (M - N)) (k : ℕ) : IsModuleCompact (M ^ k - N ^ k) := by
  induction k with
  | zero => simpa using (IsModuleCompact.zero (B := B) (E := E) (F := E))
  | succ k ih =>
    have heq : M ^ (k + 1) - N ^ (k + 1) =
        (M ^ k - N ^ k) * M + N ^ k * (M - N) := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [heq]
    exact (ih.comp_right M).add (hMN.comp_left (N ^ k))

omit [CompleteSpace E] in
theorem IsModuleCompact.polynomial_difference {M N : AdjointableMap B E E}
    (hMN : IsModuleCompact (M - N)) (p : Polynomial ℝ) :
    IsModuleCompact (Polynomial.aeval M p - Polynomial.aeval N p) := by
  have heq : Polynomial.aeval M p - Polynomial.aeval N p =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (M ^ k - N ^ k) := by
    simp only [Polynomial.aeval_eq_sum_range, smul_sub, Finset.sum_sub_distrib]
  rw [heq]
  apply (moduleCompact B E E).sum_mem
  intro k _
  change IsModuleCompact ((p.coeff k : ℝ) • (M ^ k - N ^ k))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (hMN.power_difference k).smul (p.coeff k : ℂ)

theorem IsModuleCompact.sqrt_difference {M N : AdjointableMap B E E}
    (hMN : IsModuleCompact (M - N)) (hM0 : 0 ≤ M) (hM1 : ‖M‖ ≤ 1)
    (hN0 : 0 ≤ N) (hN1 : ‖N‖ ≤ 1) :
    IsModuleCompact (CFC.sqrt M - CFC.sqrt N) := by
  rcases subsingleton_or_nontrivial (AdjointableMap B E E) with h | h
  · let := h
    simpa only [Subsingleton.elim (CFC.sqrt M - CFC.sqrt N) 0] using
      (IsModuleCompact.zero (B := B) (E := E) (F := E))
  · let := h
    let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    choose p hp using fun n => exists_polynomial_uniformly_approximating_cfc_sqrt
      (A := AdjointableMap B E E) (ε n) (by dsimp [ε]; positivity)
    let z : ℕ → AdjointableMap B E E := fun n => Polynomial.aeval M (p n) - Polynomial.aeval N (p n)
    have hbound (n : ℕ) : ‖z n - (CFC.sqrt M - CFC.sqrt N)‖ ≤ 2 * ε n := by
      have heq : z n - (CFC.sqrt M - CFC.sqrt N) =
          (Polynomial.aeval M (p n) - CFC.sqrt M) +
            (CFC.sqrt N - Polynomial.aeval N (p n)) := by dsimp [z]; abel
      rw [heq]
      have hM := hp n M hM0 hM1
      rw [norm_sub_rev] at hM
      exact (norm_add_le _ _).trans (by linarith [hp n N hN0 hN1])
    have hlim : Tendsto z atTop (𝓝 (CFC.sqrt M - CFC.sqrt N)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero (fun _ => norm_nonneg _) hbound
      simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    exact IsModuleCompact.of_tendsto hlim (Eventually.of_forall fun n => hMN.polynomial_difference (p n))

section ActualAction
variable {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ B}

/-- Actual equivariance modulo compact maps passes to the square root. -/
theorem IsModuleCompact.sqrt_action_error
    (U : EquivariantHilbertModule α E) (g : Γ) {M : AdjointableMap B E E}
    (hM : IsModuleCompact (U.conjugateOperator g M - M)) (hM0 : 0 ≤ M) (hM1 : ‖M‖ ≤ 1) :
    IsModuleCompact (U.conjugateOperator g (CFC.sqrt M) - CFC.sqrt M) := by
  let β := U.conjugateOperatorStarAlgEquiv g
  have hpos : 0 ≤ β M := map_nonneg β hM0
  have hnorm : ‖β M‖ ≤ 1 := by simpa only [StarAlgEquiv.norm_map] using hM1
  have h := hM.sqrt_difference hpos hnorm hM0 hM1
  have heq : β (CFC.sqrt M) = CFC.sqrt (β M) := by
    symm
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self M hM0]
    · exact map_nonneg β (CFC.sqrt_nonneg M)
  change IsModuleCompact (β (CFC.sqrt M) - CFC.sqrt M)
  rw [heq]
  exact h

end ActualAction
end BC4lean.KKTheory
