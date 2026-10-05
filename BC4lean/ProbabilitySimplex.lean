import BC4lean.FixedPointCriterion
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Sequences

/-! # The probability simplex with pointwise convergence

This constructs a concrete Γ-space. No equivariant CW structure or local
compactness is assumed in this definition.
-/

noncomputable section
open scoped BigOperators

namespace BC4lean.ProperActions

/-- Real nonnegative summable functions with total mass one. -/
def probabilitySet (Γ : Type*) : Set (Γ → ℝ) :=
  {f | (∀ g, 0 ≤ f g) ∧ Summable f ∧ ∑' g, f g = 1}

/-- The probability simplex, with the subspace topology from pointwise convergence. -/
abbrev ProbabilitySimplex (Γ : Type*) := probabilitySet Γ

/-- The probability simplex is convex in the real function space. -/
theorem probabilitySet_convex (Γ : Type*) : Convex ℝ (probabilitySet Γ) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun x => add_nonneg (mul_nonneg ha (hf.1 x)) (mul_nonneg hb (hg.1 x)),
    (hf.2.1.mul_left a).add (hg.2.1.mul_left b), ?_⟩
  change (∑' x, (a * f x + b * g x)) = 1
  rw [Summable.tsum_add (hf.2.1.mul_left a) (hg.2.1.mul_left b),
    tsum_mul_left, tsum_mul_left, hf.2.2, hg.2.2, mul_one, mul_one]
  exact hab

namespace ProbabilitySimplex
variable {Γ : Type*}

/-- The unit mass at one index. -/
def delta (g : Γ) : ProbabilitySimplex Γ := by
  classical
  refine ⟨Pi.single g 1, ?_, (by
    convert (hasSum_ite_eq g (1 : ℝ)).summable using 1
    funext x
    simp [Pi.single_apply]), ?_⟩
  · intro x
    by_cases h : x = g <;> simp [h]
  · simp

/-- A finite set carries at most the total mass. -/
theorem sum_le_one (p : ProbabilitySimplex Γ) (s : Finset Γ) :
    ∑ g ∈ s, p.1 g ≤ 1 := by
  rw [← p.2.2.2]
  exact p.2.2.1.sum_le_tsum s (fun g _ => p.2.1 g)

/-- Every probability function has more than half its mass on some finite set. -/
theorem exists_half_mass (p : ProbabilitySimplex Γ) :
    ∃ s : Finset Γ, (1 / 2 : ℝ) < ∑ g ∈ s, p.1 g := by
  by_contra! h
  have hh := p.2.2.1.tsum_le_of_sum_le h
  rw [p.2.2.2] at hh
  norm_num at hh

variable [Group Γ]

/-- Left translation of a probability function. -/
def translate (g : Γ) (p : ProbabilitySimplex Γ) : ProbabilitySimplex Γ :=
  ⟨fun x => p.1 (g⁻¹ * x), fun x => p.2.1 (g⁻¹ * x),
    (Equiv.mulLeft g⁻¹).summable_iff.mpr p.2.2.1,
    ((Equiv.mulLeft g⁻¹).tsum_eq p.1).trans p.2.2.2⟩

instance instMulAction : MulAction Γ (ProbabilitySimplex Γ) where
  smul := translate
  one_smul p := by
    apply Subtype.ext
    funext x
    change p.1 (1⁻¹ * x) = p.1 x
    simp
  mul_smul g h p := by
    apply Subtype.ext
    funext x
    change p.1 ((g * h)⁻¹ * x) = p.1 (h⁻¹ * (g⁻¹ * x))
    simp [mul_assoc]

@[simp] theorem smul_apply (g : Γ) (p : ProbabilitySimplex Γ) (x : Γ) :
    (g • p).1 x = p.1 (g⁻¹ * x) := rfl

instance instContinuousConstSMul : ContinuousConstSMul Γ (ProbabilitySimplex Γ) where
  continuous_const_smul g := by
    change Continuous (translate g)
    apply Continuous.subtype_mk
    exact continuous_pi fun x => (continuous_apply (g⁻¹ * x)).comp continuous_subtype_val

/-- The whole simplex is contractible; the fixed-subspace statement is proved separately. -/
theorem contractible : ContractibleSpace (ProbabilitySimplex Γ) :=
  (probabilitySet_convex Γ).contractibleSpace ⟨(delta (1 : Γ)).1, (delta (1 : Γ)).2⟩

end ProbabilitySimplex
end BC4lean.ProperActions
