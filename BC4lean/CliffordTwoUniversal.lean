import BC4lean.CliffordTwoMatrix

/-! # The proved two-generator Clifford universal law and maximal C⋆ norm

Every pair of selfadjoint unitaries satisfying vu=-uv determines one actual
unital complex star homomorphism from M₂(ℂ). Its formula is the proved four
Clifford-word expansion, and uniqueness follows from that expansion. All
nonunital star representations are contractive as well, including degenerate
ones; the identity representation attains the constructed operator norm.
-/

noncomputable section
namespace BC4lean.KKTheory
namespace CliffordTwo

variable {D : Type*} [CStarAlgebra D]

def liftLinear (u v : D) : CliffordTwo →ₗ[ℂ] D where
  toFun M := ∑ k : Fin 2 × Fin 2, coefficient M k • word u v k
  map_add' M N := by
    simp only [← coefficientLinear_apply, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' z M := by
    simp only [← coefficientLinear_apply, map_smul, smul_smul, Finset.smul_sum,
      RingHom.id_apply, smul_eq_mul]

@[simp] theorem liftLinear_word (u v : D) (k : Fin 2 × Fin 2) :
    liftLinear u v (word epsilonOne epsilonTwo k) = word u v k := by
  change (∑ l : Fin 2 × Fin 2,
    coefficient (word epsilonOne epsilonTwo k) l • word u v l) = word u v k
  simp only [coefficient_word, ite_smul, one_smul, zero_smul]
  exact Fintype.sum_ite_eq' k (word u v)

theorem liftLinear_mul (u v : D) (hu : u * u = 1) (hv : v * v = 1)
    (hanti : v * u = -(u * v)) (M N : CliffordTwo) :
    liftLinear u v (M * N) = liftLinear u v M * liftLinear u v N := by
  rw [decompose M, decompose N]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, smul_smul,
    word_mul epsilonOne epsilonTwo epsilonOne_square epsilonTwo_square epsilonTwo_mul_epsilonOne,
    word_mul u v hu hv hanti, liftLinear_word]

theorem liftLinear_star (u v : D) (hu : star u = u) (hv : star v = v)
    (hanti : v * u = -(u * v)) (M : CliffordTwo) :
    liftLinear u v (star M) = star (liftLinear u v M) := by
  rw [decompose M]
  simp only [star_sum, star_smul, map_sum, map_smul, smul_smul,
    word_star epsilonOne epsilonTwo epsilonOne_star epsilonTwo_star epsilonTwo_mul_epsilonOne,
    word_star u v hu hv hanti, liftLinear_word]

/-- The genuine universal complex star homomorphism for two anticommuting
selfadjoint unitaries, with both generator images fixed. -/
def lift (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v)) :
    CliffordTwo →⋆ₐ[ℂ] D where
  toFun := liftLinear u v
  map_zero' := (liftLinear u v).map_zero
  map_add' := (liftLinear u v).map_add
  map_mul' := liftLinear_mul u v hu₂ hv₂ hanti
  map_one' := by
    simpa [word] using liftLinear_word u v (0, 0)
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, (liftLinear u v).map_smul]
    have h : liftLinear u v 1 = 1 := by
      simpa [word] using liftLinear_word u v (0, 0)
    rw [h, Algebra.algebraMap_eq_smul_one]
  map_star' := liftLinear_star u v hu hv hanti

@[simp] theorem lift_epsilonOne (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v)) :
    lift u v hu hv hu₂ hv₂ hanti epsilonOne = u := by
  simpa [lift, word] using liftLinear_word u v (1, 0)

@[simp] theorem lift_epsilonTwo (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v)) :
    lift u v hu hv hu₂ hv₂ hanti epsilonTwo = v := by
  simpa [lift, word] using liftLinear_word u v (0, 1)

theorem lift_unique (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v))
    (φ : CliffordTwo →⋆ₐ[ℂ] D) (hφu : φ epsilonOne = u) (hφv : φ epsilonTwo = v) :
    φ = lift u v hu hv hu₂ hv₂ hanti := by
  ext M
  rw [decompose M]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [word, hφu, hφv]

theorem existsUnique_lift (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v)) :
    ∃! φ : CliffordTwo →⋆ₐ[ℂ] D, φ epsilonOne = u ∧ φ epsilonTwo = v :=
  ⟨lift u v hu hv hu₂ hv₂ hanti,
    ⟨lift_epsilonOne u v hu hv hu₂ hv₂ hanti, lift_epsilonTwo u v hu hv hu₂ hv₂ hanti⟩,
    fun φ hφ => lift_unique u v hu hv hu₂ hv₂ hanti φ hφ.1 hφ.2⟩

/-- The universal homomorphism is graded when both specified generators are odd. -/
theorem lift_graded (δ : CStarGrading D) (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v))
    (huOdd : δ.automorphism u = -u) (hvOdd : δ.automorphism v = -v) (M : CliffordTwo) :
    δ.automorphism (lift u v hu hv hu₂ hv₂ hanti M) =
      lift u v hu hv hu₂ hv₂ hanti (grading.automorphism M) := by
  rw [decompose M]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [word, huOdd, hvOdd]

/-- Contractivity also covers nonunital and degenerate representations. -/
theorem representation_norm_le {E : Type*} [NonUnitalCStarAlgebra E]
    (φ : CliffordTwo →⋆ₙₐ[ℂ] E) (M : CliffordTwo) : ‖φ M‖ ≤ ‖M‖ :=
  NonUnitalStarAlgHom.norm_apply_le φ M

structure Representation where
  carrier : Type
  [cstarAlgebra : NonUnitalCStarAlgebra carrier]
  starHom : CliffordTwo →⋆ₙₐ[ℂ] carrier

attribute [instance] Representation.cstarAlgebra

def Representation.normValue (ρ : Representation) (M : CliffordTwo) : ℝ := ‖ρ.starHom M‖

def identityRepresentation : Representation where
  carrier := CliffordTwo
  starHom := NonUnitalStarAlgHom.id ℂ CliffordTwo

theorem isGreatest_representationNorms (M : CliffordTwo) :
    IsGreatest (Set.range fun ρ : Representation => ρ.normValue M) ‖M‖ := by
  refine ⟨⟨identityRepresentation, rfl⟩, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  exact representation_norm_le ρ.starHom M

def maximalNorm (M : CliffordTwo) : ℝ := sSup (Set.range fun ρ : Representation => ρ.normValue M)

/-- The universal maximal C⋆ norm is exactly the actual matrix operator norm. -/
theorem maximalNorm_eq (M : CliffordTwo) : maximalNorm M = ‖M‖ :=
  (isGreatest_representationNorms M).isLUB.csSup_eq
    ⟨‖M‖, (isGreatest_representationNorms M).1⟩

/-- The universal norm is already complete in the actual matrix algebra. -/
theorem completeSpace : CompleteSpace CliffordTwo := inferInstance

end CliffordTwo
end BC4lean.KKTheory
