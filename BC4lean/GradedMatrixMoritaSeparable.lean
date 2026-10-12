import BC4lean.GradedMatrixMoritaMatrix

/-! # Separability of the actual finite C⋆ matrix algebra

The pinned CStarMatrix topology is the actual finite matrix entry topology,
proved compatible with its C⋆ norm in Mathlib. Finite products therefore
preserve separability for the possibly nonunital coefficient algebra.
-/

namespace BC4lean.KKTheory
variable {C : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]

instance gradedMatrixMoritaSeparable : TopologicalSpace.SeparableSpace (GradedMatrixMoritaMatrix C) := by
  let e : (Fin 2 → Fin 2 → C) ≃L[ℂ] GradedMatrixMoritaMatrix C :=
    CStarMatrix.ofMatrixL
  exact e.surjective.denseRange.separableSpace e.continuous

end BC4lean.KKTheory
