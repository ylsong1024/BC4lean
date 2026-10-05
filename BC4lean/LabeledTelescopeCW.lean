import BC4lean.EquivariantCWTransport
import BC4lean.LabeledAllowedCW
import BC4lean.LabeledPrismActionIso
import BC4lean.TelescopeFixedContraction
import BC4lean.CellularHomotopy

/-! # A genuine locally compact second-countable universal proper CW model

The staircase prism subcomplex has actual orbit-disk CW attachments. The
proved equivariant homeomorphism transports those witnesses to the geometric
telescope, whose topological and fixed-point properties are proved separately.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitTelescope
universe u
variable (Γ : Type u) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- Actual CW structure on the geometric telescope, transported through its
proved action isomorphism from the invariant staircase prism subcomplex. -/
def equivariantCWComplex : EquivariantCWComplex (topologicalAction Γ (Model Γ)) :=
  (LabeledOrbitRealization.allowedEquivariantCWComplex
    (LabeledTelescopePrisms.allowed (Γ := Γ))
    (fun hs ht => LabeledTelescopePrisms.allowed_downward hs ht)).transportIso
      (LabeledPrismProjection.actionIso (Γ := Γ))

/-- All requirements of the chosen model hold for the same concrete space. -/
theorem universalProperCWModel :
    Nonempty (EquivariantCWComplex (topologicalAction Γ (Model Γ))) ∧
      ProperSMul Γ (Model Γ) ∧ LocallyCompactSpace (Model Γ) ∧
      SecondCountableTopology (Model Γ) ∧ FixedPointCriterion Γ (Model Γ) :=
  ⟨⟨equivariantCWComplex Γ⟩, proper Γ, inferInstance, inferInstance, fixedPointCriterion Γ⟩

/-- The concrete locally compact model has the full cellular mapping property. -/
theorem homotopyTerminal {A : Type u} [TopologicalSpace A] [MulAction Γ A]
    [ContinuousConstSMul Γ A] (c : EquivariantCWComplex (topologicalAction Γ A)) :
    HomotopyTerminalFor Γ A (Model Γ) :=
  c.homotopyTerminal (fixedPointCriterion Γ)

/-- This concrete model agrees up to equivariant homotopy with every genuine
CW model satisfying the subgroup fixed-point criterion. -/
theorem unique {A : Type u} [TopologicalSpace A] [MulAction Γ A]
    [ContinuousConstSMul Γ A] (c : EquivariantCWComplex (topologicalAction Γ A))
    (h : FixedPointCriterion Γ A) : Nonempty (EquivariantHomotopyEquiv Γ A (Model Γ)) :=
  c.fixedPointCriterion_unique (equivariantCWComplex Γ) h (fixedPointCriterion Γ)
end BC4lean.ProperActions.LabeledOrbitTelescope
