import BC4lean.EquivariantCW

/-! # Transport genuine equivariant CW data along an action isomorphism -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- An isomorphism changes the colimit target while preserving every actual
skeletal attachment. No new CW structure is assumed on the target. -/
def EquivariantCWComplex.transportIso {X Y : Action TopCat.{u} Γ}
    (c : EquivariantCWComplex X) (e : X ≅ Y) : EquivariantCWComplex Y where
  __ := c.toTransfiniteCompositionOfShape.ofArrowIso (f' := initial.to Y)
    (Arrow.isoMk (Iso.refl _) e (initialIsInitial.hom_ext _ _))
  attachCells := c.attachCells
end BC4lean.ProperActions
