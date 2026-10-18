import BC4lean.AlgebraicCrossedProduct
import BC4lean.ProperCutoffFunction
import BC4lean.CutoffCoefficientProjection
import BC4lean.CZeroAlgebra

/-! # Actual finite-support cutoff projections

The cutoff coefficient functions are bundled in the genuine twisted star
algebra of finitely supported `C₀(X, ℂ)` coefficients. The mixed element
implements algebraic Murray--von Neumann equivalence of the two projections.
-/

noncomputable section
open scoped CompactlySupported ZeroAtInfty
open Function
namespace BC4lean.ProperActions.Cutoff
open KKTheory

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]
  [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X]
  [ContinuousConstSMul Γ X]

/-- Each mixed coefficient is a compactly supported complex continuous function. -/
def mixedCompactCoefficient (c d : CutoffFunction Γ X) (g : Γ) : C_c(X, ℂ) where
  toFun x := ((c x * d (g⁻¹ • x) : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((map_continuous c).mul ((map_continuous d).comp (continuous_const_smul g⁻¹)))
  hasCompactSupport' := by
    have h := (CompactlySupportedContinuousMapClass.hasCompactSupport c).mul_right
      (f' := fun x => d (g⁻¹ • x))
    exact h.comp_left Complex.ofReal_zero

/-- Regard that actual compactly supported coefficient as an element of C₀. -/
def mixedCZeroCoefficient (c d : CutoffFunction Γ X) (g : Γ) : C₀(X, ℂ) :=
  mixedCompactCoefficient c d g

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X] in
@[simp] theorem mixedCZeroCoefficient_apply (c d : CutoffFunction Γ X) (g : Γ) (x : X) :
    mixedCZeroCoefficient c d g x = ((c x * d (g⁻¹ • x) : ℝ) : ℂ) := rfl

/-- Compact transporters give finite group support for the mixed C₀ coefficients. -/
theorem finite_mixedCZeroCoefficient_support (c d : CutoffFunction Γ X) :
    HasFiniteSupport (mixedCZeroCoefficient c d) := by
  classical
  apply (finite_mixedCoefficient_support c.toCompactlySupportedContinuousMap
    d.toCompactlySupportedContinuousMap).subset
  intro g hg
  change mixedCZeroCoefficient c d g ≠ 0 at hg
  change (fun x : X => c x * d (g⁻¹ • x)) ≠ 0
  intro hz
  apply hg
  apply ZeroAtInftyContinuousMap.ext
  intro x
  have hx : c x * d (g⁻¹ • x) = 0 := congrFun hz x
  change ((c x * d (g⁻¹ • x) : ℝ) : ℂ) = 0
  simpa only [Complex.ofReal_zero] using congrArg Complex.ofReal hx

/-- The actual mixed finite-support element in the algebraic crossed product. -/
def mixedAlgebraic (c d : CutoffFunction Γ X) : AlgebraicCrossedProduct (CZero.action Γ (X := X)) :=
  SkewMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (mixedCZeroCoefficient c d) (finite_mixedCZeroCoefficient_support c d))

@[simp] theorem coeff_mixedAlgebraic (c d : CutoffFunction Γ X) (g : Γ) :
    AlgebraicCrossedProduct.coeff (CZero.action Γ) (mixedAlgebraic c d) g =
      mixedCZeroCoefficient c d g := rfl

omit [ContinuousConstSMul Γ X] in
/-- Real cutoff normalization gives exactly the complex coefficient normalization. -/
theorem complex_normalized [LocallyCompactSpace X] (c : CutoffFunction Γ X) :
    CutoffCoefficients.Normalized (Γ := Γ) (fun x => (c x : ℂ)) := by
  intro x
  calc
    (∑ᶠ g : Γ, star (c (g⁻¹ • x) : ℂ) * (c (g⁻¹ • x) : ℂ)) =
        ∑ᶠ g : Γ, ((c (g⁻¹ • x) ^ 2 : ℝ) : ℂ) := by
      apply finsum_congr
      intro g
      simp [pow_two]
    _ = ((∑ᶠ g : Γ, c (g⁻¹ • x) ^ 2 : ℝ) : ℂ) :=
      (Complex.ofRealHom.toAddMonoidHom.map_finsum
        (finite_orbitSquareSupport c.toCompactlySupportedContinuousMap x)).symm
    _ = 1 := by
      have hn : (∑ᶠ g : Γ, c (g⁻¹ • x) ^ 2) = 1 := c.normalized x
      exact congrArg Complex.ofReal hn

/-- The involution of the actual mixed element exchanges the two cutoffs. -/
@[simp] theorem star_mixedAlgebraic (c d : CutoffFunction Γ X) :
    star (mixedAlgebraic c d) = mixedAlgebraic d c := by
  apply AlgebraicCrossedProduct.ext
  intro g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp [AlgebraicCrossedProduct.coeff_star, CZero.action_apply,
    mixedCZeroCoefficient_apply, mul_comm]

private theorem cZero_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → C₀(X, ℂ)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  let ev : C₀(X, ℂ) →+ ℂ :=
    { toFun := fun a => a x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev f s

/-- Multiplication of the actual mixed elements cancels the middle cutoff. -/
theorem mixedAlgebraic_mul [LocallyCompactSpace X] (c d e : CutoffFunction Γ X) :
    mixedAlgebraic c d * mixedAlgebraic d e = mixedAlgebraic c e := by
  classical
  apply AlgebraicCrossedProduct.ext
  intro g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rw [AlgebraicCrossedProduct.coeff_mul]
  simp only [cZero_sum_apply, ZeroAtInftyContinuousMap.mul_apply,
    CZero.action_apply, coeff_mixedAlgebraic, mixedCZeroCoefficient_apply]
  have hcalc : (∑ᶠ t : Γ,
      CutoffCoefficients.mixed (fun x => (c x : ℂ)) (fun x => (d x : ℂ)) t x *
      CutoffCoefficients.mixed (fun x => (d x : ℂ)) (fun x => (e x : ℂ))
        (t⁻¹ * g) (t⁻¹ • x)) =
      CutoffCoefficients.mixed (fun x => (c x : ℂ)) (fun x => (e x : ℂ)) g x :=
    congrFun (congrFun (CutoffCoefficients.convolution_mixed_of_normalized
      (fun x => (c x : ℂ)) (complex_normalized d) (fun x => (e x : ℂ))) g) x
  have hs : support (fun t : Γ =>
      CutoffCoefficients.mixed (fun x => (c x : ℂ)) (fun x => (d x : ℂ)) t x *
      CutoffCoefficients.mixed (fun x => (d x : ℂ)) (fun x => (e x : ℂ))
        (t⁻¹ * g) (t⁻¹ • x)) ⊆
      (AlgebraicCrossedProduct.coeff (CZero.action Γ) (mixedAlgebraic c d)).support := by
    intro t ht
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hzero := congrArg (fun f : C₀(X, ℂ) => f x) hz
    simp only [coeff_mixedAlgebraic, mixedCZeroCoefficient_apply,
      ZeroAtInftyContinuousMap.zero_apply] at hzero
    have hz' : CutoffCoefficients.mixed
        (fun x => (c x : ℂ)) (fun x => (d x : ℂ)) t x = 0 := by
      simpa only [CutoffCoefficients.mixed, Complex.star_def,
        Complex.conj_ofReal, ← Complex.ofReal_mul] using hzero
    exact ht (by simp only [hz', zero_mul])
  rw [finsum_eq_sum_of_support_subset _ hs] at hcalc
  simpa only [CutoffCoefficients.mixed, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_mul] using hcalc

/-- The algebraic cutoff projection is the actual coefficient formula. -/
def algebraicProjection (c : CutoffFunction Γ X) :
    AlgebraicCrossedProduct (CZero.action Γ (X := X)) := mixedAlgebraic c c

@[simp] theorem star_algebraicProjection (c : CutoffFunction Γ X) :
    star (algebraicProjection c) = algebraicProjection c := star_mixedAlgebraic c c

@[simp] theorem algebraicProjection_mul_self [LocallyCompactSpace X]
    (c : CutoffFunction Γ X) : algebraicProjection c * algebraicProjection c =
      algebraicProjection c := mixedAlgebraic_mul c c c

/-- Both partial-isometry equations are proved for the concrete mixed element. -/
theorem mixedAlgebraic_partialIsometry [LocallyCompactSpace X] (c d : CutoffFunction Γ X) :
    star (mixedAlgebraic c d) * mixedAlgebraic c d = algebraicProjection d ∧
      mixedAlgebraic c d * star (mixedAlgebraic c d) = algebraicProjection c := by
  rw [star_mixedAlgebraic, mixedAlgebraic_mul, mixedAlgebraic_mul]
  exact ⟨rfl, rfl⟩

end BC4lean.ProperActions.Cutoff
