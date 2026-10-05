import BC4lean.LabeledAllowedRealization
import BC4lean.LabeledOrbitSkeleta

/-! # Action and dimension filtration of an invariant face subcomplex -/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]

instance : MulAction Γ (AllowedRealization A) where
  smul g x := ⟨g • x.val, by
    change supportSimplex (g • x.val) ∈ A
    rw [supportSimplex_smul]
    exact (Fact.out : ∀ g s, s ∈ A → g • s ∈ A) g (supportSimplex x.val) x.property⟩
  one_smul x := Subtype.ext (one_smul Γ x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance : ContinuousConstSMul Γ (AllowedRealization A) where
  continuous_const_smul g := (continuous_const_smul g).subtype_map (fun x hx => by
    change supportSimplex (g • x) ∈ A
    rw [supportSimplex_smul]
    exact (Fact.out : ∀ g s, s ∈ A → g • s ∈ A) g (supportSimplex x) hx)

/-- The dimension carrier inside the actual allowed subspace. -/
def allowedSkeletalCarrier (n : ℕ) : Set (AllowedRealization A) :=
  {x | x.val ∈ skeletalCarrier n}

instance (n : ℕ) : MulAction Γ (allowedSkeletalCarrier A n) where
  smul g x := ⟨g • x.val, skeletalCarrier_smul n g x.property⟩
  one_smul x := Subtype.ext (one_smul Γ x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance (n : ℕ) : ContinuousConstSMul Γ (allowedSkeletalCarrier A n) where
  continuous_const_smul g :=
    (continuous_const_smul g : Continuous (fun x : AllowedRealization A => g • x)).subtype_map
      (fun _ hx => skeletalCarrier_smul n g hx)

omit [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)] in
theorem allowedSkeletalCarrier_mono : Monotone (allowedSkeletalCarrier A) :=
  fun _ _ h _ hx => skeletalCarrier_mono h hx

end BC4lean.ProperActions.LabeledOrbitRealization
