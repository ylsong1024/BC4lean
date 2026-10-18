import BC4lean.EquivariantHilbertModule
import Mathlib.Algebra.SkewMonoidAlgebra.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The algebraic crossed product

The finite-support twisted convolution star algebra for an action on a possibly
nonunital complex C⋆-algebra. No norm or completion is asserted here.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]

/-- Finitely supported coefficient functions, with operations twisted by `α`. -/
def AlgebraicCrossedProduct (_α : CStarAlgebraAction Γ B) := SkewMonoidAlgebra B Γ

namespace AlgebraicCrossedProduct

variable (α : CStarAlgebraAction Γ B)

@[instance_reducible] private def actionDistribSMul : DistribSMul Γ B where
  smul g b := α.automorphism g b
  smul_zero g := map_zero (α.automorphism g)
  smul_add g a b := map_add (α.automorphism g) a b

instance : AddCommGroup (AlgebraicCrossedProduct α) :=
  inferInstanceAs (AddCommGroup (SkewMonoidAlgebra B Γ))

instance : Module ℂ (AlgebraicCrossedProduct α) :=
  inferInstanceAs (Module ℂ (SkewMonoidAlgebra B Γ))

instance : Mul (AlgebraicCrossedProduct α) :=
  letI := actionDistribSMul α
  inferInstanceAs (Mul (SkewMonoidAlgebra B Γ))

instance : NonUnitalNonAssocSemiring (AlgebraicCrossedProduct α) :=
  letI := actionDistribSMul α
  inferInstanceAs (NonUnitalNonAssocSemiring (SkewMonoidAlgebra B Γ))

instance : NonUnitalNonAssocRing (AlgebraicCrossedProduct α) where
  __ := (inferInstance : AddCommGroup (AlgebraicCrossedProduct α))
  __ := (inferInstance : NonUnitalNonAssocSemiring (AlgebraicCrossedProduct α))

/-- The finite coefficient function of an algebraic crossed-product element. -/
def coeff (f : AlgebraicCrossedProduct α) : Γ →₀ B := SkewMonoidAlgebra.coeff f

/-- The elementary term `a δ_g`. -/
def single (g : Γ) (a : B) : AlgebraicCrossedProduct α := SkewMonoidAlgebra.single g a

@[ext] theorem ext {f h : AlgebraicCrossedProduct α}
    (heq : ∀ g, coeff α f g = coeff α h g) : f = h :=
  SkewMonoidAlgebra.coeff_injective (Finsupp.ext heq)

@[simp] theorem coeff_zero : coeff α 0 = 0 := rfl

@[simp] theorem coeff_add (f h : AlgebraicCrossedProduct α) :
    coeff α (f + h) = coeff α f + coeff α h := SkewMonoidAlgebra.coeff_add f h

@[simp] theorem coeff_smul (c : ℂ) (f : AlgebraicCrossedProduct α) :
    coeff α (c • f) = c • coeff α f := SkewMonoidAlgebra.coeff_smul c f

@[simp] theorem coeff_single (g : Γ) (a : B) :
    coeff α (single α g a) = Finsupp.single g a := rfl

/-- Regard a finite coefficient function as an algebraic crossed-product element. -/
def ofCoeff (f : Γ →₀ B) : AlgebraicCrossedProduct α := SkewMonoidAlgebra.ofCoeff f

@[simp] theorem coeff_ofCoeff (f : Γ →₀ B) : coeff α (ofCoeff α f) = f := rfl

@[simp] theorem ofCoeff_coeff (f : AlgebraicCrossedProduct α) : ofCoeff α (coeff α f) = f := rfl

/-- The algebraic crossed product has exactly the finite coefficient vectors as its
underlying complex vector space. -/
def coeffLinearEquiv : AlgebraicCrossedProduct α ≃ₗ[ℂ] (Γ →₀ B) where
  toFun := coeff α
  invFun := ofCoeff α
  left_inv := ofCoeff_coeff α
  right_inv := coeff_ofCoeff α
  map_add' := coeff_add α
  map_smul' := coeff_smul α

@[simp] theorem coeffLinearEquiv_apply (f : AlgebraicCrossedProduct α) :
    coeffLinearEquiv α f = coeff α f := rfl

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι)
    (f : ι → AlgebraicCrossedProduct α) :
    coeff α (∑ i ∈ s, f i) = ∑ i ∈ s, coeff α (f i) :=
  map_sum (coeffLinearEquiv α).toLinearMap f s

theorem sum_single (f : AlgebraicCrossedProduct α) :
    (∑ g ∈ (coeff α f).support, single α g (coeff α f g)) = f :=
  SkewMonoidAlgebra.sum_single f

@[simp] theorem single_zero (g : Γ) : single α g 0 = 0 :=
  SkewMonoidAlgebra.single_zero g

@[simp] theorem single_add (g : Γ) (a b : B) :
    single α g (a + b) = single α g a + single α g b :=
  SkewMonoidAlgebra.single_add g a b

@[simp] theorem single_smul (g : Γ) (c : ℂ) (a : B) :
    single α g (c • a) = c • single α g a :=
  (SkewMonoidAlgebra.smul_single c g a).symm

@[simp] theorem single_mul_single (g h : Γ) (a b : B) :
    single α g a * single α h b = single α (g * h) (a * α.automorphism g b) := by
  let _ := actionDistribSMul α
  change SkewMonoidAlgebra.single g a * SkewMonoidAlgebra.single h b =
    SkewMonoidAlgebra.single (g * h) (a * (g • b))
  simp [SkewMonoidAlgebra.mul_def]

@[elab_as_elim] theorem induction_on {p : AlgebraicCrossedProduct α → Prop}
    (f : AlgebraicCrossedProduct α) (zero : p 0)
    (single : ∀ g a, p (AlgebraicCrossedProduct.single α g a))
    (add : ∀ f g, p f → p g → p (f + g)) : p f :=
  SkewMonoidAlgebra.induction_on f zero single add

instance : NonUnitalRing (AlgebraicCrossedProduct α) where
  mul_assoc f g h := by
    induction f using induction_on α with
    | zero => simp
    | single x a =>
      induction g using induction_on α with
      | zero => simp
      | single y b =>
        induction h using induction_on α with
        | zero => simp
        | single z c => simp [mul_assoc, map_mul]
        | add h₁ h₂ ih₁ ih₂ => simp_all [mul_add]
      | add g₁ g₂ ih₁ ih₂ => simp_all [add_mul, mul_add]
    | add f₁ f₂ ih₁ ih₂ => simp_all [add_mul]

theorem smul_mul (c : ℂ) (f h : AlgebraicCrossedProduct α) :
    (c • f) * h = c • (f * h) := by
  induction f using induction_on α with
  | zero => simp
  | single g a =>
    induction h using induction_on α with
    | zero => simp
    | single k b =>
      simp only [← single_smul, single_mul_single, smul_mul_assoc]
    | add h₁ h₂ ih₁ ih₂ => rw [mul_add, mul_add, ih₁, ih₂, smul_add]
  | add f₁ f₂ ih₁ ih₂ => rw [smul_add, add_mul, add_mul, ih₁, ih₂, smul_add]

theorem mul_smul (c : ℂ) (f h : AlgebraicCrossedProduct α) :
    f * (c • h) = c • (f * h) := by
  induction f using induction_on α with
  | zero => simp
  | single g a =>
    induction h using induction_on α with
    | zero => simp
    | single k b =>
      simp only [← single_smul, single_mul_single, map_smul, mul_smul_comm]
    | add h₁ h₂ ih₁ ih₂ => rw [smul_add, mul_add, mul_add, ih₁, ih₂, smul_add]
  | add f₁ f₂ ih₁ ih₂ => rw [add_mul, add_mul, ih₁, ih₂, smul_add]

instance : IsScalarTower ℂ (AlgebraicCrossedProduct α) (AlgebraicCrossedProduct α) :=
  ⟨smul_mul α⟩

instance : SMulCommClass ℂ (AlgebraicCrossedProduct α) (AlgebraicCrossedProduct α) :=
  ⟨fun c f h => (mul_smul α c f h).symm⟩

@[simp] theorem coeff_single_mul (g k : Γ) (a : B) (f : AlgebraicCrossedProduct α) :
    coeff α (single α g a * f) k = a * α.automorphism g (coeff α f (g⁻¹ * k)) := by
  classical
  induction f using induction_on α with
  | zero => simp
  | single h b =>
    simp only [single_mul_single, coeff_single, Finsupp.single_apply]
    by_cases hh : g * h = k
    · have hh' : h = g⁻¹ * k := (eq_inv_mul_iff_mul_eq).mpr hh
      simp only [if_pos hh, if_pos hh']
    · have hh' : h ≠ g⁻¹ * k := fun heq => hh ((eq_inv_mul_iff_mul_eq).mp heq)
      simp only [if_neg hh, if_neg hh', map_zero, mul_zero]
  | add f h ihf ihh => simp [mul_add, ihf, ihh]

/-- The usual left-support formula for twisted convolution. -/
theorem coeff_mul (f h : AlgebraicCrossedProduct α) (k : Γ) :
    coeff α (f * h) k =
      ∑ g ∈ (coeff α f).support,
        coeff α f g * α.automorphism g (coeff α h (g⁻¹ * k)) := by
  classical
  conv_lhs => rw [← sum_single α f, Finset.sum_mul]
  simp only [coeff_sum, Finsupp.finsetSum_apply, coeff_single_mul]

/-- Twisted inversion of the coefficient function. -/
instance : Star (AlgebraicCrossedProduct α) where
  star f := by
    classical
    exact SkewMonoidAlgebra.ofCoeff <| Finsupp.onFinset
      ((coeff α f).support.image Inv.inv)
      (fun k => α.automorphism k (star (coeff α f k⁻¹)))
      (by
        intro k hk
        apply Finset.mem_image.mpr
        refine ⟨k⁻¹, Finsupp.mem_support_iff.mpr ?_, inv_inv k⟩
        intro hz
        exact hk (by simp [hz]))

@[simp] theorem coeff_star (f : AlgebraicCrossedProduct α) (k : Γ) :
    coeff α (star f) k = α.automorphism k (star (coeff α f k⁻¹)) := rfl

instance : StarAddMonoid (AlgebraicCrossedProduct α) where
  star_involutive f := by
    apply ext α
    intro g
    simp only [coeff_star, inv_inv, map_star, star_star]
    exact α.apply_inv_apply g (coeff α f g)
  star_add f h := by
    apply ext α
    intro g
    simp

@[simp] theorem star_single (g : Γ) (a : B) :
    star (single α g a) = single α g⁻¹ (α.automorphism g⁻¹ (star a)) := by
  classical
  apply ext α
  intro k
  by_cases hk : k = g⁻¹
  · subst k
    simp
  · have hk' : k⁻¹ ≠ g := by
      intro h
      exact hk (by rw [← h, inv_inv])
    simp [hk, hk']

instance : StarRing (AlgebraicCrossedProduct α) where
  star_involutive := star_star
  star_add := star_add
  star_mul f h := by
    induction f using induction_on α with
    | zero => simp
    | single g a =>
      induction h using induction_on α with
      | zero => simp
      | single k b =>
        simp only [single_mul_single, star_single, mul_inv_rev]
        congr 1
        rw [star_mul, map_mul, ← map_star (α.automorphism g) b]
        simp only [CStarAlgebraAction.mul_apply, CStarAlgebraAction.inv_apply_apply]
      | add h₁ h₂ ih₁ ih₂ => simp_all [mul_add, add_mul]
    | add f₁ f₂ ih₁ ih₂ => simp_all [add_mul, mul_add]

instance : StarModule ℂ (AlgebraicCrossedProduct α) where
  star_smul c f := by
    apply ext α
    intro g
    simp [star_smul]

end AlgebraicCrossedProduct
end BC4lean.KKTheory
