import BC4lean.LabeledOrbitRealization
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Continuity on products with the weak realization -/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
open Topology
variable {Γ : Type*} [Group Γ]

/-- The disjoint union of charts presents the realization as a quotient. -/
def atlas (p : Σ s : LabeledOrbitSimplex Γ, LabeledSimplexCoordinates Γ s) :
    LabeledOrbitRealization Γ := chart p.1 p.2

theorem atlas_isQuotientMap : IsQuotientMap (atlas (Γ := Γ)) := by
  refine ⟨.of_isOpen_preimage_iff_isOpen ?_, ?_⟩
  · intro U
    rw [isOpen_sigma_iff]
    exact (isOpen_iff U).symm
  · intro x
    obtain ⟨s, hs⟩ := x.property
    exact ⟨⟨s, ⟨x.val, hs⟩⟩, rfl⟩

/-- Homotopies out of the weak realization can be checked on finite charts.
Local compactness of the parameter space is the essential product hypothesis. -/
theorem continuous_product_iff {T Y : Type*} [TopologicalSpace T]
    [LocallyCompactSpace T] [TopologicalSpace Y]
    (f : LabeledOrbitRealization Γ × T → Y) :
    Continuous f ↔ ∀ s, Continuous (fun p : LabeledSimplexCoordinates Γ s × T =>
      f (chart s p.1, p.2)) := by
  constructor
  · intro hf s
    exact hf.comp ((continuous_chart s).prodMap continuous_id)
  · intro hf
    apply atlas_isQuotientMap.continuous_lift_prod_left
    let e := Homeomorph.sigmaProdDistrib (X := fun s : LabeledOrbitSimplex Γ =>
      LabeledSimplexCoordinates Γ s) (Y := T)
    have hc : Continuous (fun p : Σ s : LabeledOrbitSimplex Γ,
        LabeledSimplexCoordinates Γ s × T => f (chart p.1 p.2.1, p.2.2)) :=
      continuous_sigma hf
    exact hc.comp e.continuous

end BC4lean.ProperActions.LabeledOrbitRealization
