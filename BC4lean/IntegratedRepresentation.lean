import BC4lean.GroupAlgebra
import BC4lean.LeftRegularRepresentation
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! # The integrated regular representation and reduced norm

All groups are regarded as discrete. No countability assumption is used.
The algebra homomorphism is Mathlib's linear extension of the regular operators;
compatibility with the group-algebra involution is proved below.
-/

noncomputable section

namespace BC4lean

variable {Γ : Type*} [Group Γ]

/-- The linear extension of the regular operators to the complex group algebra. -/
def integratedRepresentation : GroupAlgebra Γ →ₐ[ℂ] (L2Group Γ →L[ℂ] L2Group Γ) :=
  MonoidAlgebra.lift ℂ _ Γ operatorRepresentation

theorem integratedRepresentation_sum (a : GroupAlgebra Γ) :
    integratedRepresentation a = ∑ g ∈ a.coeff.support, a.coeff g • regularOperator g :=
  MonoidAlgebra.lift_apply operatorRepresentation a

@[simp] theorem integratedRepresentation_single (g : Γ) (z : ℂ) :
    integratedRepresentation (MonoidAlgebra.single g z) = z • regularOperator g :=
  MonoidAlgebra.lift_single operatorRepresentation g z

@[simp] theorem integratedRepresentation_delta (g : Γ) :
    integratedRepresentation (GroupAlgebra.delta g) = regularOperator g := by
  simp [GroupAlgebra.delta]

theorem integratedRepresentation_apply (a : GroupAlgebra Γ) (ξ : L2Group Γ) (h : Γ) :
    integratedRepresentation a ξ h =
      ∑ g ∈ a.coeff.support, a.coeff g * ξ (g⁻¹ * h) := by
  rw [integratedRepresentation_sum]
  simp only [sum_apply, smul_apply, lp.coeFn_sum,
    lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, regularOperator_apply]

theorem norm_integratedRepresentation_le (a : GroupAlgebra Γ) :
    ‖integratedRepresentation a‖ ≤ GroupAlgebra.l1Norm a := by
  rw [integratedRepresentation_sum]
  calc
    _ ≤ ∑ g ∈ a.coeff.support, ‖a.coeff g • regularOperator g‖ := norm_sum_le _ _
    _ = GroupAlgebra.l1Norm a := by simp [GroupAlgebra.l1Norm, norm_smul]

@[simp] theorem integratedRepresentation_star (a : GroupAlgebra Γ) :
    integratedRepresentation (star a) = star (integratedRepresentation a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [star_add, map_add, ha, hb]
  | single g z =>
    change integratedRepresentation (GroupAlgebra.involution (MonoidAlgebra.single g z)) = _
    simp only [GroupAlgebra.involution_single, integratedRepresentation_single,
      star_smul, regularOperator_star]

/-- The integrated representation as a unital complex star-algebra homomorphism. -/
def integratedStarHom : GroupAlgebra Γ →⋆ₐ[ℂ] (L2Group Γ →L[ℂ] L2Group Γ) where
  toAlgHom := integratedRepresentation
  map_star' := integratedRepresentation_star

@[simp] theorem integratedStarHom_apply (a : GroupAlgebra Γ) :
    integratedStarHom a = integratedRepresentation a := rfl

/-- Coefficients are recovered by applying the operator to the identity delta vector. -/
@[simp] theorem integratedRepresentation_delta_one (a : GroupAlgebra Γ) (h : Γ) :
    integratedRepresentation a (L2Group.delta 1) h = a.coeff h := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | single g z =>
    simp [L2Group.delta_apply, Finsupp.single_apply, eq_comm]

theorem integratedRepresentation_injective :
    Function.Injective (integratedRepresentation (Γ := Γ)) := by
  intro a b hab
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro h
  simpa using congrArg (fun T : L2Group Γ →L[ℂ] L2Group Γ => T (L2Group.delta 1) h) hab

/-- The coefficient function as an ℓ²-vector; the next theorem identifies it pointwise. -/
def GroupAlgebra.toL2 (a : GroupAlgebra Γ) : L2Group Γ :=
  integratedRepresentation a (L2Group.delta 1)

@[simp] theorem GroupAlgebra.toL2_apply (a : GroupAlgebra Γ) (h : Γ) :
    a.toL2 h = a.coeff h := integratedRepresentation_delta_one a h

theorem norm_toL2_le (a : GroupAlgebra Γ) : ‖a.toL2‖ ≤ ‖integratedRepresentation a‖ := by
  simpa only [GroupAlgebra.toL2, L2Group.norm_delta, mul_one] using
    (integratedRepresentation a).le_opNorm (L2Group.delta (1 : Γ))

theorem norm_coeff_le (a : GroupAlgebra Γ) (h : Γ) :
    ‖a.coeff h‖ ≤ ‖integratedRepresentation a‖ := by
  simpa only [GroupAlgebra.toL2_apply] using
    (L2Group.norm_apply_le a.toL2 h).trans (norm_toL2_le a)

/-- The algebraic image is exactly the finite complex span of the regular operators. -/
theorem integratedRepresentation_range :
    (integratedRepresentation (Γ := Γ)).range.toSubmodule =
      Submodule.span ℂ (Set.range (regularOperator (Γ := Γ))) := by
  apply le_antisymm
  · rintro T ⟨a, rfl⟩
    change integratedRepresentation a ∈ Submodule.span ℂ (Set.range regularOperator)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | single g z =>
      rw [integratedRepresentation_single]
      exact Submodule.smul_mem _ z (Submodule.subset_span ⟨g, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro T ⟨g, rfl⟩
    exact ⟨GroupAlgebra.delta g, integratedRepresentation_delta g⟩

/-- The reduced norm is the norm of the faithful regular operator. -/
def reducedNorm (a : GroupAlgebra Γ) : ℝ := ‖integratedRepresentation a‖

theorem reducedNorm_nonneg (a : GroupAlgebra Γ) : 0 ≤ reducedNorm a := norm_nonneg _

@[simp] theorem reducedNorm_eq_zero (a : GroupAlgebra Γ) : reducedNorm a = 0 ↔ a = 0 := by
  simp only [reducedNorm, norm_eq_zero, map_eq_zero_iff _ integratedRepresentation_injective]

theorem reducedNorm_add_le (a b : GroupAlgebra Γ) :
    reducedNorm (a + b) ≤ reducedNorm a + reducedNorm b := by
  simpa only [reducedNorm, map_add] using norm_add_le (integratedRepresentation a) _

theorem reducedNorm_smul (z : ℂ) (a : GroupAlgebra Γ) :
    reducedNorm (z • a) = ‖z‖ * reducedNorm a := by
  simp only [reducedNorm, map_smul, norm_smul]

theorem reducedNorm_mul_le (a b : GroupAlgebra Γ) :
    reducedNorm (a * b) ≤ reducedNorm a * reducedNorm b := by
  simpa only [reducedNorm, map_mul] using norm_mul_le (integratedRepresentation a) _

@[simp] theorem reducedNorm_star (a : GroupAlgebra Γ) : reducedNorm (star a) = reducedNorm a := by
  unfold reducedNorm
  rw [integratedRepresentation_star]
  exact norm_star (integratedRepresentation a)

theorem reducedNorm_cstar (a : GroupAlgebra Γ) :
    reducedNorm (star a * a) = reducedNorm a ^ 2 := by
  unfold reducedNorm
  rw [map_mul, integratedRepresentation_star]
  simpa only [pow_two] using CStarRing.norm_star_mul_self (x := integratedRepresentation a)

@[simp] theorem reducedNorm_delta (g : Γ) : reducedNorm (GroupAlgebra.delta g) = 1 := by
  simp only [reducedNorm, integratedRepresentation_delta, norm_regularOperator]

theorem reducedNorm_bounds (a : GroupAlgebra Γ) :
    ‖a.toL2‖ ≤ reducedNorm a ∧ reducedNorm a ≤ GroupAlgebra.l1Norm a :=
  ⟨norm_toL2_le a, norm_integratedRepresentation_le a⟩

end BC4lean
