import BC4lean.LabeledPrismHomeomorph
import BC4lean.EquivariantCW

/-! # The actual equivariant topological-action isomorphism for the prism telescope -/
noncomputable section
open CategoryTheory
namespace BC4lean.ProperActions.LabeledPrismProjection
variable {Γ : Type*} [Group Γ] [Countable Γ]

/-- The proved inverse homeomorphism, bundled as a continuous equivariant map. -/
def equivariantInverse : EquivariantMap Γ (LabeledOrbitTelescope.Model Γ)
    (PrismRealization (Γ := Γ)) where
  toFun := inverse
  continuous_toFun := continuous_inverse
  map_smul' := inverse_smul

/-- The prism realization and the geometric telescope are isomorphic as actual
continuous Γ-actions, with the explicit inverse maps. -/
def actionIso : topologicalAction Γ (PrismRealization (Γ := Γ)) ≅
    topologicalAction Γ (LabeledOrbitTelescope.Model Γ) where
  hom := equivariantProjection.toActionHom
  inv := equivariantInverse.toActionHom
  hom_inv_id := by
    apply Action.hom_ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact inverse_projection x
  inv_hom_id := by
    apply Action.hom_ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact projection_inverse x

end BC4lean.ProperActions.LabeledPrismProjection
