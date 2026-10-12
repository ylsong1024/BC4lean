import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.NoncommRing

noncomputable section
namespace BC4lean.KKTheory

section Powers
variable {R : Type*} [NormedRing R] [NormOneClass R]

/-- Powers of contractions have norm at most one. -/
theorem norm_pow_le_one_of_norm_le_one (a : R) (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  calc
    ‖a ^ n‖ ≤ ‖a‖ ^ n := norm_pow_le _ _
    _ ≤ (1 : ℝ) ^ n := pow_le_pow_left₀ (norm_nonneg _) ha n
    _ = 1 := one_pow _

/-- The power commutator estimate follows by a noncommutative telescoping
identity; it requires no order inequality between noncommuting elements. -/
theorem norm_power_commutator_le (a b : R) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖a ^ n * b - b * a ^ n‖ ≤ (n : ℝ) * ‖a * b - b * a‖ := by
  induction n with
  | zero => simp
  | succ n hn =>
    have heq : a ^ (n + 1) * b - b * a ^ (n + 1) =
        a ^ n * (a * b - b * a) + (a ^ n * b - b * a ^ n) * a := by
      rw [pow_succ]
      noncomm_ring
    rw [heq]
    have hpow := norm_pow_le_one_of_norm_le_one a ha n
    calc
      _ ≤ ‖a ^ n * (a * b - b * a)‖ + ‖(a ^ n * b - b * a ^ n) * a‖ := norm_add_le _ _
      _ ≤ ‖a ^ n‖ * ‖a * b - b * a‖ + ‖a ^ n * b - b * a ^ n‖ * ‖a‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * ‖a * b - b * a‖ + ‖a ^ n * b - b * a ^ n‖ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))
          (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
      _ ≤ (n + 1 : ℕ) * ‖a * b - b * a‖ := by
        push_cast
        nlinarith

/-- Powers are uniformly Lipschitz on contractions, using the actual
noncommutative difference-of-powers identity. -/
theorem norm_pow_sub_pow_le_of_contractions (a b : R) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (n : ℕ) : ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n hn =>
    have heq : a ^ (n + 1) - b ^ (n + 1) =
        (a ^ n - b ^ n) * a + b ^ n * (a - b) := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [heq]
    have hpow := norm_pow_le_one_of_norm_le_one b hb n
    calc
      _ ≤ ‖(a ^ n - b ^ n) * a‖ + ‖b ^ n * (a - b)‖ := norm_add_le _ _
      _ ≤ ‖a ^ n - b ^ n‖ * ‖a‖ + ‖b ^ n‖ * ‖a - b‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖a ^ n - b ^ n‖ * 1 + 1 * ‖a - b‖ :=
        add_le_add (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))
      _ ≤ (n + 1 : ℕ) * ‖a - b‖ := by
        push_cast
        nlinarith
end Powers

/-- The finite coefficient-weighted power bound of a real polynomial. -/
def polynomialNormModulus (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * (k : ℝ)

theorem polynomialNormModulus_nonneg (p : Polynomial ℝ) : 0 ≤ polynomialNormModulus p :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

section PolynomialBounds
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]

/-- A polynomial commutator is controlled by its actual coefficient sum
and the commutator of its argument. -/
theorem norm_polynomial_commutator_le (p : Polynomial ℝ) (a b : A) (ha : ‖a‖ ≤ 1) :
    ‖Polynomial.aeval a p * b - b * Polynomial.aeval a p‖ ≤
      polynomialNormModulus p * ‖a * b - b * a‖ := by
  have heq : Polynomial.aeval a p * b - b * Polynomial.aeval a p =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (a ^ k * b - b * a ^ k) := by
    simp only [Polynomial.aeval_eq_sum_range, Finset.sum_mul, Finset.mul_sum,
      smul_sub, smul_mul_assoc, mul_smul_comm, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k • (a ^ k * b - b * a ^ k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1),
        (‖p.coeff k‖ * (k : ℝ)) * ‖a * b - b * a‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_power_commutator_le a b ha k) (norm_nonneg (p.coeff k))
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Polynomial evaluation is uniformly Lipschitz on contractions. -/
theorem norm_polynomial_sub_polynomial_le (p : Polynomial ℝ) (a b : A)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖Polynomial.aeval a p - Polynomial.aeval b p‖ ≤ polynomialNormModulus p * ‖a - b‖ := by
  have heq : Polynomial.aeval a p - Polynomial.aeval b p =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (a ^ k - b ^ k) := by
    simp only [Polynomial.aeval_eq_sum_range, smul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k • (a ^ k - b ^ k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), (‖p.coeff k‖ * (k : ℝ)) * ‖a - b‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_pow_sub_pow_le_of_contractions a b ha hb k) (norm_nonneg (p.coeff k))
    _ = _ := by rw [← Finset.sum_mul]; rfl
end PolynomialBounds


/-- Replacing one commutator input gives a quantitative error bound. -/
theorem norm_commutator_error_le {R : Type*} [NormedRing R] (x y b : R) :
    ‖x * b - b * x‖ ≤ 2 * ‖x - y‖ * ‖b‖ + ‖y * b - b * y‖ := by
  have heq : x * b - b * x =
      ((x - y) * b + (y * b - b * y)) - b * (x - y) := by noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖(x - y) * b‖ + ‖y * b - b * y‖ + ‖b * (x - y)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖x - y‖ * ‖b‖ + ‖y * b - b * y‖ + ‖b‖ * ‖x - y‖ :=
      add_le_add (add_le_add (norm_mul_le _ _) (le_refl _)) (norm_mul_le _ _)
    _ = _ := by ring

section CStarSquareRoot
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

/-- One real polynomial uniformly approximates the actual CFC square root
of every positive contraction, by scalar Weierstrass approximation and the
isometric CFC norm bound. -/
theorem exists_polynomial_uniformly_approximating_cfc_sqrt (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ a : A, 0 ≤ a → ‖a‖ ≤ 1 →
      ‖CFC.sqrt a - Polynomial.aeval a p‖ ≤ ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 Real.sqrt
    Real.continuous_sqrt.continuousOn ε hε
  refine ⟨p, fun a ha0 ha1 => ?_⟩
  have hsa : IsSelfAdjoint a := .of_nonneg ha0
  rw [CFC.sqrt_eq_real_sqrt a ha0, cfcₙ_eq_cfc,
    ← cfc_polynomial p a hsa, ← cfc_sub Real.sqrt p.eval a
      Real.continuous_sqrt.continuousOn p.continuous.continuousOn]
  apply norm_cfc_le hε.le
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg ha0 hx
  have hx1 : x ≤ 1 :=
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans ha1)
  simpa only [Real.norm_eq_abs, abs_sub_comm] using (hp x ⟨hx0, hx1⟩).le


/-- Square-root commutators have a uniform small-error modulus on positive
contractions. The proof uses polynomial approximation and telescoping
commutators, without an order comparison of noncommuting operators. -/
theorem exists_cfc_sqrt_commutator_modulus (b : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : A, 0 ≤ a → ‖a‖ ≤ 1 →
      ‖a * b - b * a‖ < η → ‖CFC.sqrt a * b - b * CFC.sqrt a‖ < ε := by
  let δ : ℝ := ε / (4 * (‖b‖ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_uniformly_approximating_cfc_sqrt (A := A) δ hδ
  let L := polynomialNormModulus p
  have hL : 0 ≤ L := polynomialNormModulus_nonneg p
  let η : ℝ := ε / (2 * (L + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  refine ⟨η, hη, fun a ha0 ha1 hab => ?_⟩
  have hpoly := norm_polynomial_commutator_le p a b ha1
  have herror := norm_commutator_error_le (CFC.sqrt a) (Polynomial.aeval a p) b
  have happrox := hp a ha0 ha1
  have hδeq : δ * (4 * (‖b‖ + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hsmall : ‖a * b - b * a‖ * (2 * (L + 1)) < ε :=
    (lt_div_iff₀ (by positivity)).mp hab
  have hc0 := norm_nonneg (a * b - b * a)
  have hb0 := norm_nonneg b
  have happroxBound : 2 * ‖CFC.sqrt a - Polynomial.aeval a p‖ * ‖b‖ ≤ ε / 2 := by
    have hprod := mul_le_mul_of_nonneg_right happrox hb0
    nlinarith
  have hpolyBound : L * ‖a * b - b * a‖ < ε / 2 := by nlinarith
  nlinarith

/-- The actual CFC square root is uniformly continuous in norm on positive
contractions, by one common polynomial approximation. -/
theorem exists_cfc_sqrt_difference_modulus (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ a b : A, 0 ≤ a → ‖a‖ ≤ 1 → 0 ≤ b → ‖b‖ ≤ 1 →
      ‖a - b‖ < η → ‖CFC.sqrt a - CFC.sqrt b‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_uniformly_approximating_cfc_sqrt (A := A)
    (ε / 4) (by positivity)
  let L := polynomialNormModulus p
  have hL : 0 ≤ L := polynomialNormModulus_nonneg p
  let η : ℝ := ε / (2 * (L + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  refine ⟨η, hη, fun a b ha0 ha1 hb0 hb1 hab => ?_⟩
  have hpoly := norm_polynomial_sub_polynomial_le p a b ha1 hb1
  have hapa := hp a ha0 ha1
  have hapb := hp b hb0 hb1
  have hsmall : ‖a - b‖ * (2 * (L + 1)) < ε :=
    (lt_div_iff₀ (by positivity)).mp hab
  have hdiff0 := norm_nonneg (a - b)
  have hpolyBound : L * ‖a - b‖ < ε / 2 := by nlinarith
  calc
    ‖CFC.sqrt a - CFC.sqrt b‖ =
        ‖(CFC.sqrt a - Polynomial.aeval a p) +
          (Polynomial.aeval a p - Polynomial.aeval b p) +
            (Polynomial.aeval b p - CFC.sqrt b)‖ := by congr 1; abel
    _ ≤ ‖CFC.sqrt a - Polynomial.aeval a p‖ +
        ‖Polynomial.aeval a p - Polynomial.aeval b p‖ +
          ‖Polynomial.aeval b p - CFC.sqrt b‖ := norm_add₃_le
    _ < ε := by rw [norm_sub_rev (Polynomial.aeval b p)]; linarith

omit [Nontrivial A] in
/-- A star algebra automorphism preserves the actual positive CFC square
root, by its genuine uniqueness property. -/
theorem starAlgEquiv_map_cfc_sqrt (α : A ≃⋆ₐ[ℂ] A) (a : A) (ha : 0 ≤ a) :
    α (CFC.sqrt a) = CFC.sqrt (α a) := by
  symm
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self a ha]
  · exact map_nonneg α (CFC.sqrt_nonneg a)

/-- The same difference modulus controls every automorphism error of square
roots of positive contractions. -/
theorem exists_cfc_sqrt_automorphism_modulus (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (α : A ≃⋆ₐ[ℂ] A) (a : A), 0 ≤ a → ‖a‖ ≤ 1 →
      ‖α a - a‖ < η → ‖α (CFC.sqrt a) - CFC.sqrt a‖ < ε := by
  obtain ⟨η, hη, hdiff⟩ := exists_cfc_sqrt_difference_modulus (A := A) ε hε
  refine ⟨η, hη, fun α a ha0 ha1 herr => ?_⟩
  rw [starAlgEquiv_map_cfc_sqrt α a ha0]
  exact hdiff (α a) a (map_nonneg α ha0) (by simpa only [StarAlgEquiv.norm_map] using ha1)
    ha0 ha1 herr

end CStarSquareRoot
end BC4lean.KKTheory
