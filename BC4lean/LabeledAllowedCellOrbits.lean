import BC4lean.LabeledSimplexOrbits
import BC4lean.LabeledAllowedAction

/-! # Actual orbit indices of an invariant family of simplices -/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitSimplex
universe u
variable {Γ : Type u} [Group Γ]
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]

/-- Membership is constant on a simplex orbit, in both directions. -/
theorem smul_mem_allowed_iff (g : Γ) (s : LabeledOrbitSimplex Γ) :
    g • s ∈ A ↔ s ∈ A := by
  constructor
  · intro h
    have h' := (Fact.out : ∀ g s, s ∈ A → g • s ∈ A) g⁻¹ (g • s) h
    simpa using h'
  · exact (Fact.out : ∀ g s, s ∈ A → g • s ∈ A) g s

/-- The orbit representatives actually occurring in the allowed subcomplex. -/
def AllowedCellOrbit (n : ℕ) := {q : CellOrbit Γ n | (cellRepresentative q).val ∈ A}

theorem cellOrbitSimplex_mem_allowed_iff {n : ℕ} (q : CellOrbit Γ n)
    (a : Γ ⧸ cellStabilizer q) :
    (cellOrbitSimplex q a).val ∈ A ↔ (cellRepresentative q).val ∈ A := by
  induction a using QuotientGroup.induction_on with
  | H g =>
    change g • (cellRepresentative q).val ∈ A ↔ _
    exact smul_mem_allowed_iff A g _

end BC4lean.ProperActions.LabeledOrbitSimplex
