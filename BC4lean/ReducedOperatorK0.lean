import BC4lean.OperatorK0
import BC4lean.ReducedGroupCStar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # The degree-zero analytic target

The reduced group C⋆-algebra carries its canonical spectral order. This makes
its stable projection monoid and unital operator K₀ available for every group.
No assembly map, K₁ construction, or computation of these groups is asserted.
-/

noncomputable section
namespace BC4lean

universe u v
variable (Γ : Type u) [Group Γ]

/-- Stable projection classes for the reduced group C⋆-algebra, with spectral order. -/
def ReducedProjectionMonoid : Type _ :=
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  OperatorKTheory.StableProjectionMonoid (ReducedGroupCStar Γ)

instance reducedProjectionAddCommMonoid : AddCommMonoid (ReducedProjectionMonoid Γ) := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  exact inferInstanceAs (AddCommMonoid (OperatorKTheory.StableProjectionMonoid (ReducedGroupCStar Γ)))

/-- The degree-zero analytic target K₀(Cᵣ*(Γ)), using the canonical spectral order. -/
def ReducedK0 : Type _ :=
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  OperatorKTheory.K0 (ReducedGroupCStar Γ)

instance reducedK0AddCommGroup : AddCommGroup (ReducedK0 Γ) := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  exact inferInstanceAs (AddCommGroup (OperatorKTheory.K0 (ReducedGroupCStar Γ)))

/-- The canonical map from projection classes to the degree-zero analytic group. -/
def reducedK0Class : ReducedProjectionMonoid Γ →+ ReducedK0 Γ := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  exact OperatorKTheory.k0Class

/-- The universal property specialized to the reduced group algebra. -/
def reducedK0Universal {G : Type v} [AddCommGroup G] :
    (ReducedProjectionMonoid Γ →+ G) ≃ (ReducedK0 Γ →+ G) := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  exact OperatorKTheory.k0Universal

end BC4lean
