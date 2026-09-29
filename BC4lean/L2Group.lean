import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Square-summable functions and the delta Hilbert basis

The index type need not be countable or carry a group structure.
Mathlib supplies the complete complex inner product space structure on `lp`.
Sums are unordered sums over finite subsets, not a chosen enumeration.
-/

noncomputable section

namespace BC4lean

open scoped ENNReal

/-- Square-summable complex-valued functions, with their Hilbert space structure. -/
abbrev L2Group (Γ : Type*) := lp (fun _ : Γ => ℂ) 2

namespace L2Group

variable {Γ : Type*}

/-- Membership is exactly summability of the squared coefficient norms. -/
theorem mem_iff (f : Γ → ℂ) :
    Memℓp f 2 ↔ Summable (fun g => ‖f g‖ ^ (2 : ℕ)) := by
  simpa using (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (f := f))

/-- Completeness is inherited from Mathlib's `lp` construction. -/
theorem completeSpace : CompleteSpace (L2Group Γ) := inferInstance

theorem summable_norm_sq (ξ : L2Group Γ) : Summable (fun g => ‖ξ g‖ ^ (2 : ℕ)) :=
  (mem_iff ξ).mp (lp.memℓp ξ)

theorem norm_sq (ξ : L2Group Γ) : ‖ξ‖ ^ (2 : ℕ) = ∑' g, ‖ξ g‖ ^ (2 : ℕ) := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) ξ

theorem inner_eq_tsum (ξ η : L2Group Γ) :
    inner ℂ ξ η = ∑' g, star (ξ g) * η g := by
  simpa [RCLike.inner_apply, mul_comm] using lp.inner_eq_tsum (𝕜 := ℂ) ξ η

theorem summable_inner (ξ η : L2Group Γ) :
    Summable (fun g => star (ξ g) * η g) := by
  simpa [RCLike.inner_apply, mul_comm] using lp.summable_inner (𝕜 := ℂ) ξ η

/-- The delta vector at `g`. -/
def delta (g : Γ) : L2Group Γ := by
  classical
  exact lp.single 2 g 1

open scoped Classical in
theorem delta_apply (g h : Γ) : delta g h = if h = g then 1 else 0 := by
  classical
  simp [delta, lp.single_apply, Pi.single_apply]

@[simp] theorem delta_apply_self (g : Γ) : delta g g = 1 := by
  classical
  simp [delta_apply]

@[simp] theorem norm_delta (g : Γ) : ‖delta g‖ = 1 := by
  classical
  simp only [delta, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one]

/-- The identity coordinate representation gives the canonical Hilbert basis. -/
def deltaBasis : HilbertBasis Γ ℂ (L2Group Γ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem deltaBasis_apply (g : Γ) : deltaBasis g = delta g := rfl

theorem delta_orthonormal : Orthonormal ℂ (delta : Γ → L2Group Γ) :=
  deltaBasis.orthonormal

theorem delta_dense_span :
    (Submodule.span ℂ (Set.range (delta : Γ → L2Group Γ))).topologicalClosure = ⊤ :=
  deltaBasis.dense_span

theorem hasSum_delta (ξ : L2Group Γ) : HasSum (fun g => ξ g • delta g) ξ :=
  deltaBasis.hasSum_repr ξ

@[simp] theorem inner_delta (g : Γ) (ξ : L2Group Γ) : inner ℂ (delta g) ξ = ξ g :=
  (deltaBasis.repr_apply_apply ξ g).symm

theorem norm_apply_le (ξ : L2Group Γ) (g : Γ) : ‖ξ g‖ ≤ ‖ξ‖ :=
  lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ξ g

end L2Group
end BC4lean
