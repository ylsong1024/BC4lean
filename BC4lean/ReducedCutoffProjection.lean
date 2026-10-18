import BC4lean.CutoffAlgebraicProjection
import BC4lean.AlgebraicCrossedRepresentation
import BC4lean.NonunitalProjectionK0

/-! # Cutoff projections and their genuine operator K₀ class

The finite-support cutoff formula is integrated in the constructed regular
reduced crossed product. Its projection identities and the two mixed-cutoff
partial-isometry identities survive this actual star homomorphism. The
existing nonunital operator K₀ construction therefore gives a class independent
of the cutoff. Neither Kasparov descent nor an assembly map is asserted here.
-/

noncomputable section
open scoped CompactlySupported ZeroAtInfty
namespace BC4lean.ProperActions.Cutoff
open KKTheory OperatorKTheory

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]
  [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X]

/-- The concrete reduced crossed-product cutoff projection. -/
def reducedCutoffProjection (c : CutoffFunction Γ X) :
    ReducedCrossedProduct (CZero.action Γ (X := X)) :=
  algebraicToReducedCrossed (CZero.action Γ) (algebraicProjection c)

theorem reducedCutoffProjection_isStarProjection (c : CutoffFunction Γ X) :
    IsStarProjection (reducedCutoffProjection c) := by
  apply isStarProjection_iff'.mpr
  constructor
  · change algebraicToReducedCrossed _ _ * algebraicToReducedCrossed _ _ = _
    rw [← map_mul, algebraicProjection_mul_self]
    rfl
  · change star (algebraicToReducedCrossed _ _) = _
    rw [← map_star, star_algebraicProjection]
    rfl

/-- A concrete mixed element implements equivalence in the completed algebra. -/
theorem reducedCutoffProjection_partialIsometry (c d : CutoffFunction Γ X) :
    ∃ v : ReducedCrossedProduct (CZero.action Γ (X := X)),
      star v * v = reducedCutoffProjection c ∧
        v * star v = reducedCutoffProjection d := by
  refine ⟨algebraicToReducedCrossed (CZero.action Γ) (mixedAlgebraic d c), ?_, ?_⟩
  · rw [← map_star, ← map_mul, (mixedAlgebraic_partialIsometry d c).1]
    rfl
  · rw [← map_star, ← map_mul, (mixedAlgebraic_partialIsometry d c).2]
    rfl

/-- The cutoff class lies in the actual scalar-kernel definition of operator K₀. -/
def cutoffK0 (c : CutoffFunction Γ X) :
    OperatorK0 (ReducedCrossedProduct (CZero.action Γ (X := X))) :=
  nonunitalProjectionK0 (reducedCutoffProjection c) (reducedCutoffProjection_isStarProjection c)

/-- No chosen cutoff occurs in the resulting operator K₀ class. -/
theorem cutoffK0_independent (c d : CutoffFunction Γ X) : cutoffK0 c = cutoffK0 d := by
  obtain ⟨v, hv, hv'⟩ := reducedCutoffProjection_partialIsometry c d
  exact nonunitalProjectionK0_eq_of_partialIsometry
    (reducedCutoffProjection_isStarProjection c) (reducedCutoffProjection_isStarProjection d) v hv hv'

end BC4lean.ProperActions.Cutoff
