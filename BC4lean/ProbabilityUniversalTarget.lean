import BC4lean.ProbabilityFixedPoints
import BC4lean.ProbabilityProperAction
import BC4lean.ProperActionPullback
import BC4lean.CellularHomotopy

/-! # A concrete proper target for the cellular mapping theorem

This module does not equip the probability simplex with a CW structure and
does not assert that it is locally compact. It constructs the target and
proves the mapping property for equivariant CW sources.
-/

namespace BC4lean.ProperActions

universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {A : Type u} [TopologicalSpace A] [MulAction Γ A] [ContinuousConstSMul Γ A]

/-- Every finite-isotropy equivariant CW complex maps to the explicit probability simplex,
uniquely up to equivariant homotopy. -/
theorem EquivariantCWComplex.probability_homotopyTerminal
    (c : EquivariantCWComplex (topologicalAction Γ A)) :
    HomotopyTerminalFor Γ A (ProbabilitySimplex Γ) :=
  c.homotopyTerminal ProbabilitySimplex.fixedPointCriterion

omit [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- For countable Γ, the explicit target has a countable base. -/
theorem ProbabilitySimplex.secondCountable [Countable Γ] :
    SecondCountableTopology (ProbabilitySimplex Γ) := inferInstance

/-- For a countable group, the concrete target is proper and has the full cellular mapping property. -/
theorem probability_proper_universal_target [Countable Γ]
    (c : EquivariantCWComplex (topologicalAction Γ A)) :
    ProperSMul Γ (ProbabilitySimplex Γ) ∧ HomotopyTerminalFor Γ A (ProbabilitySimplex Γ) :=
  ⟨ProbabilitySimplex.proper, c.probability_homotopyTerminal⟩

/-- A Hausdorff finite-isotropy equivariant CW space has a proper action for countable Γ.
The following unconditional result supplies Hausdorffness from the categorical CW data. -/
theorem EquivariantCWComplex.proper_of_t2 [Countable Γ] [T2Space A]
    (c : EquivariantCWComplex (topologicalAction Γ A)) : ProperSMul Γ A := by
  let : ProperSMul Γ (ProbabilitySimplex Γ) := ProbabilitySimplex.proper
  let : ContinuousSMul Γ A := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  obtain ⟨f⟩ := c.probability_homotopyTerminal.1
  exact f.properSMul


/-- A finite-isotropy equivariant CW space has a proper action for every countable discrete group.
Hausdorffness is derived from the cellular data, rather than imposed as a separate hypothesis. -/
theorem EquivariantCWComplex.proper [Countable Γ]
    (c : EquivariantCWComplex (topologicalAction Γ A)) : ProperSMul Γ A := by
  let : T2Space A := c.t2Space
  exact c.proper_of_t2

end BC4lean.ProperActions

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace BC4lean.ProperActions
universe u
variable (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

namespace UniversalZeroSkeleton
/-- The constructed universal zero-skeleton is a proper Γ-space. -/
theorem proper [Countable Γ] : ProperSMul Γ (UniversalZeroSkeleton Γ) := cwComplex.proper

/-- Infinite subgroups have no fixed vertices. -/
theorem infinite_fixedPoints_empty [Countable Γ] (H : Subgroup Γ) [Infinite H] :
    IsEmpty (FixedPointSpace H (UniversalZeroSkeleton Γ)) := by
  let := proper Γ
  exact fixedPointSpace_isEmpty H
end UniversalZeroSkeleton

/-- A concrete one-orbit zero-dimensional CW model for a finite group. -/
abbrev FiniteGroupCWModel [Finite Γ] :=
  OrbitZeroSkeleton (fun _ : PUnit.{u+1} => (⟨⊤, inferInstance⟩ : FiniteIsotropy Γ))

namespace FiniteGroupCWModel
variable [Finite Γ]
instance : Subsingleton (FiniteGroupCWModel Γ) := by
  let : Subsingleton (Γ ⧸ (⊤ : Subgroup Γ)) := QuotientGroup.subsingleton_quotient_top
  change Subsingleton (Σ _ : PUnit.{u+1}, OrbitCell (⊤ : Subgroup Γ) (TopCat.disk.{u} 0))
  let : Subsingleton (OrbitCell (⊤ : Subgroup Γ) (TopCat.disk.{u} 0)) :=
    inferInstanceAs (Subsingleton ((Γ ⧸ (⊤ : Subgroup Γ)) × TopCat.disk.{u} 0))
  constructor
  rintro ⟨⟨⟩, x⟩ ⟨⟨⟩, y⟩
  exact congrArg (Sigma.mk PUnit.unit) (Subsingleton.elim x y)
instance : Nonempty (FiniteGroupCWModel Γ) :=
  ⟨⟨PUnit.unit, QuotientGroup.mk 1, ⟨⟨0, by simp⟩⟩⟩⟩

/-- The finite-group model has an actual CW structure with one zero-cell orbit. -/
def cwComplex : EquivariantCWComplex (topologicalAction Γ (FiniteGroupCWModel Γ)) :=
  OrbitZeroSkeleton.cwComplex _

omit [DiscreteTopology Γ] in
/-- Every subgroup fixed-point space of this one-point model is contractible. -/
theorem fixedPoints_contractible (H : Subgroup Γ) :
    ContractibleSpace (FixedPointSpace H (FiniteGroupCWModel Γ)) := by
  let : Nonempty (FixedPointSpace H (FiniteGroupCWModel Γ)) :=
    ⟨⟨Classical.choice inferInstance, fun _ => Subsingleton.elim _ _⟩⟩
  infer_instance

omit [DiscreteTopology Γ] in
/-- For finite groups the explicit CW model satisfies the full fixed-point criterion. -/
theorem fixedPointCriterion : FixedPointCriterion Γ (FiniteGroupCWModel Γ) := by
  refine ⟨fun H _ => fixedPoints_contractible Γ H, ?_⟩
  intro H hH
  let := hH
  exact False.elim (not_finite H)

/-- The finite-group model is proper, locally compact, and second countable. -/
theorem proper_locallyCompact_secondCountable :
    ProperSMul Γ (FiniteGroupCWModel Γ) ∧ LocallyCompactSpace (FiniteGroupCWModel Γ) ∧
      SecondCountableTopology (FiniteGroupCWModel Γ) :=
  ⟨(cwComplex Γ).proper, OrbitZeroSkeleton.locallyCompact _, inferInstance⟩

/-- The finite-group CW model has the universal mapping property for every CW source. -/
theorem homotopyTerminal {A : Type u} [TopologicalSpace A] [MulAction Γ A]
    [ContinuousConstSMul Γ A] (c : EquivariantCWComplex (topologicalAction Γ A)) :
    HomotopyTerminalFor Γ A (FiniteGroupCWModel Γ) :=
  c.homotopyTerminal (fixedPointCriterion Γ)
end FiniteGroupCWModel
end BC4lean.ProperActions

end
