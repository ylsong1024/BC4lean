import BC4lean.ReducedCrossedHilbertModule
import BC4lean.EquivariantHilbertModule
import BC4lean.AdjointableComplete
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Regular coefficient operators on the crossed-product Hilbert module

Uniformly bounded coefficient families act diagonally on the actual coefficient
Hilbert module. The bound uses the order inequality for conjugation in a
C⋆-algebra, so it controls the norm of the sum of coefficient squares.
-/

noncomputable section
namespace BC4lean.KKTheory

open UniformSpace
open scoped InnerProductSpace

variable {Γ B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Coordinatewise left multiplication on finite coefficient vectors. -/
def reducedCrossedFiniteDiagonal (a : Γ → B) :
    ReducedCrossedVectors B Γ →ₗ[ℂ] ReducedCrossedVectors B Γ :=
  Finsupp.lsum ℂ fun i => (Finsupp.lsingle i).comp (standardLeftMulCLM (a i)).toLinearMap

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem reducedCrossedFiniteDiagonal_single (a : Γ → B) (i : Γ) (b : Bᵐᵒᵖ) :
    reducedCrossedFiniteDiagonal a (Finsupp.single i b) =
      Finsupp.single i (MulOpposite.op (a i * MulOpposite.unop b)) := by
  simp [reducedCrossedFiniteDiagonal, Finsupp.lsum_single]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem reducedCrossedFiniteDiagonal_apply (a : Γ → B)
    (x : ReducedCrossedVectors B Γ) (i : Γ) :
    reducedCrossedFiniteDiagonal a x i = MulOpposite.op (a i * MulOpposite.unop (x i)) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, mul_add]
  | single j b =>
    by_cases h : j = i
    · subst j
      simp
    · simp [h]

omit [PartialOrder B] [StarOrderedRing B] in
theorem reducedCrossedFiniteDiagonal_support_subset (a : Γ → B)
    (x : ReducedCrossedVectors B Γ) :
    (reducedCrossedFiniteDiagonal a x).support ⊆ x.support := by
  classical
  intro i hi
  by_contra h
  have hz : x i = 0 := Finsupp.notMem_support_iff.mp h
  simpa [hz] using Finsupp.mem_support_iff.mp hi

theorem reducedCrossedFiniteDiagonal_inner (a : Γ → B)
    (x y : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner (reducedCrossedFiniteDiagonal a x) y =
      reducedCrossedFiniteInner x (reducedCrossedFiniteDiagonal (fun i => star (a i)) y) := by
  classical
  rw [reducedCrossedFiniteInner_eq_sum _ _ x.support
    (reducedCrossedFiniteDiagonal_support_subset a x),
    reducedCrossedFiniteInner_eq_sum _ _ x.support (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [reducedCrossedFiniteDiagonal_apply]
  exact (standardLeftMulMap (a i)).adjoint_identity (x i) (y i)

/-- The coefficient-square estimate underlying the regular representation. -/
theorem reducedCrossedFiniteDiagonal_inner_le (a : Γ → B) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner (reducedCrossedFiniteDiagonal a x)
        (reducedCrossedFiniteDiagonal a x) ≤
      K ^ 2 • reducedCrossedFiniteInner x x := by
  classical
  rw [reducedCrossedFiniteInner_eq_sum _ _ x.support
    (reducedCrossedFiniteDiagonal_support_subset a x),
    reducedCrossedFiniteInner_eq_sum _ _ x.support (Finset.Subset.refl _), Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [reducedCrossedFiniteDiagonal_apply]
  rw [← MulOpposite.unop_le_unop]
  change star (a i * MulOpposite.unop (x i)) * (a i * MulOpposite.unop (x i)) ≤
    K ^ 2 • (star (MulOpposite.unop (x i)) * MulOpposite.unop (x i))
  calc
    _ ≤ ‖a i‖ ^ 2 • (star (MulOpposite.unop (x i)) * MulOpposite.unop (x i)) := by
      rw [star_mul, ← mul_assoc, mul_assoc _ (star (a i)),
        sq, ← CStarRing.norm_star_mul_self (x := a i)]
      exact CStarAlgebra.star_left_conjugate_le_norm_smul
    _ ≤ _ := smul_le_smul_of_nonneg_right
      (sq_le_sq₀ (norm_nonneg _) hK |>.mpr (ha i)) (star_mul_self_nonneg _)

/-- Uniform coefficient bounds give bounds in the genuine Hilbert-module norm. -/
theorem reducedCrossedFiniteDiagonal_formNorm_le (a : Γ → B) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (x : ReducedCrossedVectors B Γ) :
    PositiveModuleForm.formNorm (B := B) (reducedCrossedFiniteDiagonal a x) ≤
      K * PositiveModuleForm.formNorm (B := B) x := by
  apply (sq_le_sq₀ (PositiveModuleForm.formNorm_nonneg _)
    (mul_nonneg hK (PositiveModuleForm.formNorm_nonneg _))).mp
  rw [PositiveModuleForm.formNorm_sq, mul_pow, PositiveModuleForm.formNorm_sq]
  change ‖reducedCrossedFiniteInner (reducedCrossedFiniteDiagonal a x)
    (reducedCrossedFiniteDiagonal a x)‖ ≤ K ^ 2 * ‖reducedCrossedFiniteInner x x‖
  calc
    _ ≤ ‖K ^ 2 • reducedCrossedFiniteInner x x‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le
        (PositiveModuleForm.inner_self_nonneg (B := B) (x := reducedCrossedFiniteDiagonal a x))
        (reducedCrossedFiniteDiagonal_inner_le a K hK ha x)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg K)]

/-- A bounded diagonal family descends to the actual normed module quotient. -/
def reducedCrossedQuotientDiagonal (a : Γ → B) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) :
    AdjointableMap B (ReducedCrossedPreModule B Γ) (ReducedCrossedPreModule B Γ) where
  toCLM := positiveModuleQuotientLiftCLM (reducedCrossedFiniteDiagonal a)
    (reducedCrossedFiniteDiagonal_formNorm_le a K hK ha)
  adjointCLM := positiveModuleQuotientLiftCLM
    (reducedCrossedFiniteDiagonal (fun i => star (a i)))
    (reducedCrossedFiniteDiagonal_formNorm_le (fun i => star (a i)) K hK
      (fun i => by simpa only [norm_star] using ha i))
  adjoint_identity x y := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective x
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective y
    simp only [positiveModuleQuotientLiftCLM_mk, PositiveModuleQuotient.inner_mk]
    exact reducedCrossedFiniteDiagonal_inner a x y

/-- Bounded diagonal families act by actual adjointable operators on the completion. -/
def reducedCrossedDiagonal (a : Γ → B) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  (reducedCrossedQuotientDiagonal a K hK ha).completion

@[simp] theorem reducedCrossedDiagonal_mk (a : Γ → B) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedDiagonal a K hK ha (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedFiniteDiagonal a x) := by
  rw [reducedCrossedMk_apply, reducedCrossedDiagonal, AdjointableMap.completion_apply_coe]
  rfl

@[simp] theorem reducedCrossedDiagonal_adjoint_mk (a : Γ → B) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) (x : ReducedCrossedVectors B Γ) :
    (reducedCrossedDiagonal a K hK ha).adjoint (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedFiniteDiagonal (fun i => star (a i)) x) := by
  rw [reducedCrossedMk_apply, reducedCrossedDiagonal, AdjointableMap.completion_adjoint,
    AdjointableMap.completion_apply_coe]
  rfl

theorem norm_reducedCrossedDiagonal_le (a : Γ → B) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, ‖a i‖ ≤ K) : ‖reducedCrossedDiagonal a K hK ha‖ ≤ K := by
  rw [reducedCrossedDiagonal, AdjointableMap.norm_completion]
  exact norm_positiveModuleQuotientLiftCLM_le _ hK
    (reducedCrossedFiniteDiagonal_formNorm_le a K hK ha)

/-- Agreement on finite vectors determines an adjointable regular operator. -/
theorem reducedCrossedRegular_ext
    {S T : AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)}
    (h : ∀ x : ReducedCrossedVectors B Γ, S (reducedCrossedMk x) = T (reducedCrossedMk x)) :
    S = T := by
  ext x
  exact reducedCrossedMk_denseRange.induction_on x
    (isClosed_eq S.toCLM.continuous T.toCLM.continuous) h

variable [Group Γ]

/-- The twisted coefficient action on the regular module. -/
def reducedCrossedCoefficient (α : CStarAlgebraAction Γ B) (b : B) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  reducedCrossedDiagonal (fun i => α.automorphism i⁻¹ b) ‖b‖ (norm_nonneg _)
    (fun i => (StarAlgEquiv.norm_map (α.automorphism i⁻¹) b).le)

@[simp] theorem reducedCrossedCoefficient_mk (α : CStarAlgebraAction Γ B) (b : B)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedCoefficient α b (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedFiniteDiagonal (fun i => α.automorphism i⁻¹ b) x) :=
  reducedCrossedDiagonal_mk _ _ _ _ _

theorem norm_reducedCrossedCoefficient_le (α : CStarAlgebraAction Γ B) (b : B) :
    ‖reducedCrossedCoefficient α b‖ ≤ ‖b‖ := norm_reducedCrossedDiagonal_le _ _ _ _

/-- The adjoint of the coefficient operator is multiplication by the starred coefficient. -/
@[simp] theorem reducedCrossedCoefficient_star (α : CStarAlgebraAction Γ B) (b : B) :
    reducedCrossedCoefficient α (star b) = star (reducedCrossedCoefficient α b) := by
  apply reducedCrossedRegular_ext
  intro x
  change reducedCrossedCoefficient α (star b) (reducedCrossedMk x) =
    (reducedCrossedCoefficient α b).adjoint (reducedCrossedMk x)
  rw [reducedCrossedCoefficient_mk, reducedCrossedCoefficient,
    reducedCrossedDiagonal_adjoint_mk]
  exact congrArg (fun a : Γ → B => reducedCrossedMk (reducedCrossedFiniteDiagonal a x))
    (funext fun i => map_star (α.automorphism i⁻¹) b)

/-- The coefficient algebra acts by a genuine complex nonunital star homomorphism. -/
def reducedCrossedCoefficientHom (α : CStarAlgebraAction Γ B) :
    B →⋆ₙₐ[ℂ]
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) where
  toFun := reducedCrossedCoefficient α
  map_zero' := by
    apply reducedCrossedRegular_ext
    intro x
    rw [reducedCrossedCoefficient_mk]
    change reducedCrossedMk _ = 0
    have hd : reducedCrossedFiniteDiagonal (fun i => α.automorphism i⁻¹ 0) x = 0 := by
      ext i
      simp
    rw [hd]
    exact map_zero (reducedCrossedMk (B := B) (Γ := Γ))
  map_add' b c := by
    apply reducedCrossedRegular_ext
    intro x
    simp only [AdjointableMap.coe_add_apply, reducedCrossedCoefficient_mk, ← map_add]
    congr 1
    ext i
    simp [add_mul]
  map_mul' b c := by
    apply reducedCrossedRegular_ext
    intro x
    change reducedCrossedCoefficient α (b * c) (reducedCrossedMk x) =
      reducedCrossedCoefficient α b (reducedCrossedCoefficient α c (reducedCrossedMk x))
    simp only [reducedCrossedCoefficient_mk]
    congr 1
    ext i
    simp [mul_assoc]
  map_smul' c b := by
    apply reducedCrossedRegular_ext
    intro x
    simp only [AdjointableMap.coe_smul_apply, reducedCrossedCoefficient_mk, ← map_smul]
    congr 1
    ext i
    simp [smul_mul_assoc]
  map_star' := reducedCrossedCoefficient_star α

/-- Translation by a group element on the actual coefficient Hilbert module. -/
def reducedCrossedRegular (g : Γ) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  reducedCrossedReindex (Equiv.mulLeft g)

@[simp] theorem reducedCrossedRegular_mk (g : Γ) (x : ReducedCrossedVectors B Γ) :
    reducedCrossedRegular g (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedEmbeddingLinear (Equiv.mulLeft g).toEmbedding x) :=
  reducedCrossedReindex_mk _ _

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem reducedCrossedRegular_finite_apply (g : Γ)
    (x : ReducedCrossedVectors B Γ) (i : Γ) :
    reducedCrossedEmbeddingLinear (Equiv.mulLeft g).toEmbedding x i = x (g⁻¹ * i) := by
  rw [reducedCrossedEmbeddingLinear_equiv_apply]
  rfl

@[simp] theorem reducedCrossedRegular_one :
    reducedCrossedRegular (B := B) (1 : Γ) = 1 := by
  apply reducedCrossedRegular_ext
  intro x
  rw [reducedCrossedRegular_mk]
  change reducedCrossedMk _ = reducedCrossedMk x
  congr 1
  ext i
  simp only [reducedCrossedRegular_finite_apply, inv_one, one_mul]

@[simp] theorem reducedCrossedRegular_mul (g h : Γ) :
    reducedCrossedRegular (B := B) (g * h) =
      reducedCrossedRegular g * reducedCrossedRegular h := by
  apply reducedCrossedRegular_ext
  intro x
  change reducedCrossedRegular (g * h) (reducedCrossedMk x) =
    reducedCrossedRegular g (reducedCrossedRegular h (reducedCrossedMk x))
  simp only [reducedCrossedRegular_mk]
  congr 1
  ext i
  simp only [reducedCrossedRegular_finite_apply, mul_inv_rev, mul_assoc]

/-- The actual regular representation satisfies the group laws. -/
def reducedCrossedRegularHom :
    Γ →* AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) where
  toFun := reducedCrossedRegular
  map_one' := reducedCrossedRegular_one
  map_mul' := reducedCrossedRegular_mul

@[simp] theorem reducedCrossedRegular_star (g : Γ) :
    star (reducedCrossedRegular (B := B) g) = reducedCrossedRegular g⁻¹ := by
  change (reducedCrossedReindex (B := B) (Equiv.mulLeft g)).adjoint =
    reducedCrossedReindex (Equiv.mulLeft g⁻¹)
  rw [reducedCrossedReindex_adjoint, Equiv.mulLeft_symm]

/-- The regular coefficient and group representations satisfy covariance. -/
theorem reducedCrossed_covariance (α : CStarAlgebraAction Γ B) (g : Γ) (b : B) :
    reducedCrossedCoefficient α (α.automorphism g b) * reducedCrossedRegular g =
      reducedCrossedRegular g * reducedCrossedCoefficient α b := by
  apply reducedCrossedRegular_ext
  intro x
  change reducedCrossedCoefficient α (α.automorphism g b)
    (reducedCrossedRegular g (reducedCrossedMk x)) =
      reducedCrossedRegular g (reducedCrossedCoefficient α b (reducedCrossedMk x))
  simp only [reducedCrossedRegular_mk, reducedCrossedCoefficient_mk]
  congr 1
  ext i
  simp only [reducedCrossedFiniteDiagonal_apply, reducedCrossedRegular_finite_apply]
  congr 2
  simp only [mul_inv_rev, inv_inv, ← α.mul_apply]

@[simp] theorem reducedCrossedCoefficient_inclusion (α : CStarAlgebraAction Γ B) (b : B)
    (i : Γ) (x : Bᵐᵒᵖ) :
    reducedCrossedCoefficient α b (reducedCrossedInclusion i x) =
      reducedCrossedInclusion i (MulOpposite.op (α.automorphism i⁻¹ b * MulOpposite.unop x)) := by
  rw [reducedCrossedInclusion_apply, reducedCrossedCoefficient_mk,
    reducedCrossedFiniteDiagonal_single, reducedCrossedInclusion_apply]

/-- The regular coefficient representation is isometric, including nonunital coefficients. -/
@[simp] theorem norm_reducedCrossedCoefficient (α : CStarAlgebraAction Γ B) (b : B) :
    ‖reducedCrossedCoefficient α b‖ = ‖b‖ := by
  apply le_antisymm (norm_reducedCrossedCoefficient_le α b)
  by_cases hb : ‖b‖ = 0
  · simpa only [hb] using norm_nonneg (reducedCrossedCoefficient α b)
  · have h := AdjointableMap.norm_apply_le (reducedCrossedCoefficient α b)
      (reducedCrossedInclusion (1 : Γ) (MulOpposite.op (star b)))
    have hmul : ‖b‖ * ‖b‖ ≤ ‖reducedCrossedCoefficient α b‖ * ‖b‖ := by
      simpa only [reducedCrossedCoefficient_inclusion, inv_one, α.one_apply,
        reducedCrossedInclusion_norm, MulOpposite.unop_op, MulOpposite.norm_op,
        norm_star, CStarRing.norm_self_mul_star, AdjointableMap.norm_def] using h
    exact le_of_mul_le_mul_right hmul
      (lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb))

theorem reducedCrossedCoefficient_injective (α : CStarAlgebraAction Γ B) :
    Function.Injective (reducedCrossedCoefficient α) := by
  intro b c h
  have hz : reducedCrossedCoefficientHom α (b - c) = 0 := by
    simp only [map_sub]
    exact sub_eq_zero.mpr h
  have hn := norm_reducedCrossedCoefficient α (b - c)
  change ‖reducedCrossedCoefficientHom α (b - c)‖ = ‖b - c‖ at hn
  rw [hz, norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)

/-- Coordinate evaluation of a regular translate. -/
@[simp] theorem reducedCrossedEvaluation_regular (g : Γ)
    (x : ReducedCrossedHilbertModule B Γ) (i : Γ) :
    reducedCrossedEvaluation i (reducedCrossedRegular g x) =
      reducedCrossedEvaluation (g⁻¹ * i) x := by
  exact reducedCrossedEvaluation_reindex (Equiv.mulLeft g) x i

/-- The regular coefficient representation has the expected coordinate formula. -/
@[simp] theorem reducedCrossedEvaluation_coefficient (α : CStarAlgebraAction Γ B) (b : B)
    (x : ReducedCrossedHilbertModule B Γ) (i : Γ) :
    reducedCrossedEvaluation i (reducedCrossedCoefficient α b x) =
      MulOpposite.op (α.automorphism i⁻¹ b * MulOpposite.unop (reducedCrossedEvaluation i x)) := by
  have h : (reducedCrossedEvaluation (B := B) i).comp (reducedCrossedCoefficient α b) =
      (standardLeftMul (α.automorphism i⁻¹ b)).comp (reducedCrossedEvaluation i) := by
    apply reducedCrossed_adjointable_ext_mk
    intro y
    simp only [AdjointableMap.comp_apply, reducedCrossedCoefficient_mk,
      reducedCrossedEvaluation_mk, reducedCrossedFiniteDiagonal_apply, standardLeftMul_apply]
  exact congrArg (fun T : AdjointableMap B (ReducedCrossedHilbertModule B Γ) Bᵐᵒᵖ => T x) h

end BC4lean.KKTheory
