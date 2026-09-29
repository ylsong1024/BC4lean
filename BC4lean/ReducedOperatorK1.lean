import BC4lean.StableUnitary
import BC4lean.ReducedOperatorK0

/-! # The degree-one reduced analytic target -/
noncomputable section
namespace BC4lean
variable (Γ : Type*) [Group Γ]

/-- Stable norm-homotopy K₁ of the reduced group C*-algebra, with spectral order. -/
def ReducedK1 : Type _ :=
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  OperatorKTheory.K1 (ReducedGroupCStar Γ)

instance reducedK1AddCommGroup : AddCommGroup (ReducedK1 Γ) := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  exact inferInstanceAs (AddCommGroup (OperatorKTheory.K1 (ReducedGroupCStar Γ)))

end BC4lean
