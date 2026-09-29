import BC4lean.L2Group
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# First milestone: the left regular representation

We construct translations directly on square-summable functions. No countability
assumption is required. All groups in this module are regarded as discrete.
-/

noncomputable section

namespace BC4lean

open scoped ENNReal

universe u

variable {Γ : Type u} [Group Γ]

/-- Left translation preserves square summability by reindexing the sum. -/
theorem memLp_leftTranslate (g : Γ) (ξ : L2Group Γ) :
    Memℓp (fun h => ξ (g⁻¹ * h)) 2 := by
  apply memℓp_gen
  exact (Equiv.mulLeft g⁻¹).summable_iff.mpr
    ((lp.memℓp ξ).summable (by norm_num))

/-- Left translation, before packaging it as a linear isometry. -/
def leftTranslate (g : Γ) (ξ : L2Group Γ) : L2Group Γ :=
  ⟨fun h => ξ (g⁻¹ * h), memLp_leftTranslate g ξ⟩

@[simp] theorem leftTranslate_apply (g h : Γ) (ξ : L2Group Γ) :
    leftTranslate g ξ h = ξ (g⁻¹ * h) := rfl

@[simp] theorem leftTranslate_one (ξ : L2Group Γ) : leftTranslate 1 ξ = ξ := by
  apply lp.ext
  funext h
  simp

theorem leftTranslate_mul (g h : Γ) (ξ : L2Group Γ) :
    leftTranslate (g * h) ξ = leftTranslate g (leftTranslate h ξ) := by
  apply lp.ext
  funext k
  simp [mul_assoc]

@[simp] theorem leftTranslate_inv_left (g : Γ) (ξ : L2Group Γ) :
    leftTranslate g⁻¹ (leftTranslate g ξ) = ξ := by
  rw [← leftTranslate_mul, inv_mul_cancel, leftTranslate_one]

@[simp] theorem leftTranslate_inv_right (g : Γ) (ξ : L2Group Γ) :
    leftTranslate g (leftTranslate g⁻¹ ξ) = ξ := by
  rw [← leftTranslate_mul, mul_inv_cancel, leftTranslate_one]

/-- Translations preserve the norm, by invariance of a sum under a bijection. -/
@[simp] theorem norm_leftTranslate (g : Γ) (ξ : L2Group Γ) :
    ‖leftTranslate g ξ‖ = ‖ξ‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (Equiv.mulLeft g⁻¹).tsum_eq (fun h => ‖ξ h‖ ^ (2 : ℝ≥0∞).toReal)

/-- A unitary expressed as a complex-linear isometric equivalence. -/
def leftRegular (g : Γ) : L2Group Γ ≃ₗᵢ[ℂ] L2Group Γ where
  toFun := leftTranslate g
  invFun := leftTranslate g⁻¹
  left_inv := leftTranslate_inv_left g
  right_inv := leftTranslate_inv_right g
  map_add' ξ η := by
    apply lp.ext
    rfl
  map_smul' c ξ := by
    apply lp.ext
    rfl
  norm_map' := norm_leftTranslate g

@[simp] theorem leftRegular_apply (g h : Γ) (ξ : L2Group Γ) :
    leftRegular g ξ h = ξ (g⁻¹ * h) := rfl

theorem leftRegular_inner (g : Γ) (ξ η : L2Group Γ) :
    inner ℂ (leftRegular g ξ) (leftRegular g η) = inner ℂ ξ η :=
  (leftRegular g).inner_map_map ξ η

/-- The regular operator in the algebra of bounded complex-linear operators. -/
def regularOperator (g : Γ) : L2Group Γ →L[ℂ] L2Group Γ :=
  (leftRegular g : L2Group Γ →L[ℂ] L2Group Γ)

@[simp] theorem regularOperator_apply (g h : Γ) (ξ : L2Group Γ) :
    regularOperator g ξ h = ξ (g⁻¹ * h) := rfl

@[simp] theorem regularOperator_one : regularOperator (1 : Γ) = 1 := by
  ext ξ h
  simp [regularOperator]

@[simp] theorem regularOperator_mul (g h : Γ) :
    regularOperator (g * h) = regularOperator g * regularOperator h := by
  ext ξ k
  simp [regularOperator, mul_assoc]

@[simp] theorem regularOperator_star (g : Γ) :
    star (regularOperator g) = regularOperator g⁻¹ := by
  change star (leftRegular g : L2Group Γ →L[ℂ] L2Group Γ) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  rfl

/-- Both unitary identities hold in the bounded-operator algebra. -/
theorem regularOperator_unitary (g : Γ) :
    star (regularOperator g) * regularOperator g = 1 ∧
      regularOperator g * star (regularOperator g) = 1 := by
  constructor <;> simp [← regularOperator_mul]

/-- The left regular representation, packaged as a multiplicative map. -/
def operatorRepresentation : Γ →* (L2Group Γ →L[ℂ] L2Group Γ) where
  toFun := regularOperator
  map_one' := regularOperator_one
  map_mul' := regularOperator_mul

/-- Translation carries the delta vector at `h` to the delta vector at `g * h`. -/
@[simp] theorem regularOperator_delta (g h : Γ) :
    regularOperator g (L2Group.delta h) = L2Group.delta (g * h) := by
  classical
  ext k
  simp only [regularOperator_apply, L2Group.delta_apply, inv_mul_eq_iff_eq_mul]

@[simp] theorem norm_regularOperator (g : Γ) : ‖regularOperator g‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ξ
    change ‖leftTranslate g ξ‖ ≤ 1 * ‖ξ‖
    simp only [norm_leftTranslate, one_mul, le_refl]
  · have h := (regularOperator g).le_opNorm (L2Group.delta (1 : Γ))
    simpa only [regularOperator_delta, L2Group.norm_delta, mul_one] using h

/-- The left regular representation with values in the unitary group. -/
def regularRepresentation : Γ →* unitary (L2Group Γ →L[ℂ] L2Group Γ) where
  toFun g := ⟨regularOperator g, Unitary.mem_iff.mpr (regularOperator_unitary g)⟩
  map_one' := Subtype.ext regularOperator_one
  map_mul' g h := Subtype.ext (regularOperator_mul g h)

@[simp] theorem regularRepresentation_coe (g : Γ) :
    (regularRepresentation g : L2Group Γ →L[ℂ] L2Group Γ) = regularOperator g := rfl

@[simp] theorem regularRepresentation_apply (g h : Γ) (ξ : L2Group Γ) :
    (regularRepresentation g : L2Group Γ →L[ℂ] L2Group Γ) ξ h = ξ (g⁻¹ * h) := rfl

end BC4lean
