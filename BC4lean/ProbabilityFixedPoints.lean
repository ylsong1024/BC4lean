import BC4lean.ProbabilitySimplex

/-! # Fixed points of the probability simplex -/

noncomputable section
open scoped BigOperators
namespace BC4lean.ProperActions

variable {Γ : Type*} [Group Γ]

/-- The invariant probability functions for a subgroup, as a convex subset of function space. -/
def invariantProbabilitySet (H : Subgroup Γ) : Set (Γ → ℝ) :=
  {f | f ∈ probabilitySet Γ ∧ ∀ h : H, ∀ x, f ((h : Γ)⁻¹ * x) = f x}

/-- Invariance and normalization are preserved under convex combinations. -/
theorem invariantProbabilitySet_convex (H : Subgroup Γ) :
    Convex ℝ (invariantProbabilitySet H) := by
  intro f hf g hg a b ha hb hab
  refine ⟨probabilitySet_convex Γ hf.1 hg.1 ha hb hab, ?_⟩
  intro h x
  change a * f ((h : Γ)⁻¹ * x) + b * g ((h : Γ)⁻¹ * x) = a * f x + b * g x
  rw [hf.2 h x, hg.2 h x]

/-- Fixed points are homeomorphic to the invariant convex subset. -/
def probabilityFixedPointsHomeomorph (H : Subgroup Γ) :
    FixedPointSpace H (ProbabilitySimplex Γ) ≃ₜ invariantProbabilitySet H where
  toFun p := ⟨p.1.1, p.1.2, fun h x => congrArg (fun q : ProbabilitySimplex Γ => q.1 x) (p.2 h)⟩
  invFun f := ⟨⟨f.1, f.2.1⟩, fun h => Subtype.ext (funext (f.2.2 h))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- A finite subgroup has an invariant probability function: its uniform distribution. -/
theorem invariantProbabilitySet_nonempty (H : Subgroup Γ) [Finite H] :
    (invariantProbabilitySet H).Nonempty := by
  classical
  let := Fintype.ofFinite H
  let c : ℝ := (Fintype.card H : ℝ)⁻¹
  let f : Γ → ℝ := (H : Set Γ).indicator (fun _ => c)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcard : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x
    exact Set.indicator_nonneg (fun _ _ => hc) x
  · exact summable_of_hasFiniteSupport ((Set.toFinite (H : Set Γ)).subset Set.support_indicator_subset)
  · change (∑' x, (H : Set Γ).indicator (fun _ => c) x) = 1
    rw [← tsum_subtype]
    simp [tsum_fintype, c, hcard]
  · intro h x
    simp only [f, Set.indicator_apply, SetLike.mem_coe]
    rw [H.mul_mem_cancel_left (H.inv_mem h.2)]

namespace ProbabilitySimplex

/-- Finite-subgroup fixed points of the simplex are contractible. -/
theorem fixedPoints_contractible (H : Subgroup Γ) [Finite H] :
    ContractibleSpace (FixedPointSpace H (ProbabilitySimplex Γ)) := by
  let := (invariantProbabilitySet_convex H).contractibleSpace (invariantProbabilitySet_nonempty H)
  exact (probabilityFixedPointsHomeomorph H).contractibleSpace

/-- Infinite subgroups have no invariant probability functions. -/
theorem fixedPoints_empty (H : Subgroup Γ) [Infinite H] :
    IsEmpty (FixedPointSpace H (ProbabilitySimplex Γ)) := by
  classical
  refine ⟨fun p => ?_⟩
  have hex : ∃ x, p.1.1 x ≠ 0 := by
    by_contra! hz
    have ht := p.1.2.2.2
    simp only [hz, tsum_zero] at ht
    norm_num at ht
  obtain ⟨x, hx⟩ := hex
  have hpos : 0 < p.1.1 x := lt_of_le_of_ne (p.1.2.1 x) (Ne.symm hx)
  have hs : Summable (fun h : H => p.1.1 ((h : Γ) * x)) :=
    p.1.2.2.1.comp_injective (fun _ _ h => Subtype.ext (mul_right_cancel h))
  have he (h : H) : p.1.1 ((h : Γ) * x) = p.1.1 x := by
    have hfix := congrArg (fun q : ProbabilitySimplex Γ => q.1 x) (p.2 h⁻¹)
    change p.1.1 (((h⁻¹ : H) : Γ)⁻¹ * x) = p.1.1 x at hfix
    simpa only [Subgroup.coe_inv, inv_inv] using hfix
  simp only [he] at hs
  let := Finite.of_summable_const hpos hs
  exact not_finite H

/-- The concrete simplex satisfies the full finite/infinite subgroup criterion. -/
theorem fixedPointCriterion : FixedPointCriterion Γ (ProbabilitySimplex Γ) :=
  ⟨fun H _ => fixedPoints_contractible H, fun H _ => fixedPoints_empty H⟩

end ProbabilitySimplex
end BC4lean.ProperActions
