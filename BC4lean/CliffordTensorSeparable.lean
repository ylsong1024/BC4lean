import BC4lean.CliffordTensorOrder
import Mathlib.Topology.Constructions.SumProd

/-! # Separability of the genuine one-Clifford tensor coefficient

The previously constructed coordinate star equivalence is an actual
continuous surjection from B × B onto the complete C⋆ tensor B ⊗ Cl₁.
Its dense range transports the existing product separability. No
separability hypothesis on a multiplier or adjointable algebra is used.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [TopologicalSpace.SeparableSpace B]

instance cliffordTensorSeparableSpace : TopologicalSpace.SeparableSpace (CliffordTensor B) := by
  let e : B × B ≃⋆ₐ[ℂ] CliffordTensor B :=
    (cliffordTensorCoordinateStarAlgEquiv (B := B)).symm
  exact e.surjective.denseRange.separableSpace
    (StarAlgEquiv.isometry (A := B × B) (B := CliffordTensor B) e).continuous

end BC4lean.KKTheory
