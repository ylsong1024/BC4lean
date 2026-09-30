import BC4lean.HomotopyTerminal
import Mathlib.Topology.Homotopy.Contractible

/-! # The fixed-point criterion and the finite-group point model

This predicate records the fixed-point condition on a prospective model. It is
not a definition of an equivariant CW complex, nor a proof of the general model
existence or of the cellular universal mapping theorem.
-/
namespace BC4lean.ProperActions

/-- The fixed-point condition expected of a universal proper model. -/
def FixedPointCriterion (Γ X : Type*) [Group Γ] [TopologicalSpace X] [MulAction Γ X] : Prop :=
  (∀ H : Subgroup Γ, Finite H → ContractibleSpace (FixedPointSpace H X)) ∧
  (∀ H : Subgroup Γ, Infinite H → IsEmpty (FixedPointSpace H X))

variable {Γ X Y : Type*} [Group Γ] [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction Γ X] [MulAction Γ Y]

/-- The fixed-point criterion is invariant under equivariant homotopy equivalence. -/
theorem FixedPointCriterion.of_equiv (h : FixedPointCriterion Γ X)
    (e : EquivariantHomotopyEquiv Γ X Y) : FixedPointCriterion Γ Y := by
  constructor
  · intro H hH
    exact (e.fixedPoints H).contractibleSpace_iff.mp (h.1 H hH)
  · intro H hH
    let := h.2 H hH
    exact ⟨fun y => isEmptyElim (e.invMap.fixedPointsMap H y)⟩

/-- A one-point space carrying the trivial action. -/
def Point := Unit

namespace Point
instance instUnique : Unique Point := inferInstanceAs (Unique Unit)
instance instTopologicalSpace : TopologicalSpace Point := ⊥
instance instDiscreteTopology : DiscreteTopology Point := ⟨rfl⟩
instance instMulAction : MulAction Γ Point where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Every fixed-point space of the trivial one-point action is contractible. -/
theorem fixedPoints_contractible (H : Subgroup Γ) :
    ContractibleSpace (FixedPointSpace H Point) := by
  let : Nonempty (FixedPointSpace H Point) := ⟨⟨default, fun _ => rfl⟩⟩
  infer_instance

/-- For finite groups the point satisfies the full fixed-point criterion. -/
theorem fixedPointCriterion [Finite Γ] : FixedPointCriterion Γ Point := by
  refine ⟨fun H _ => fixedPoints_contractible H, ?_⟩
  intro H hH
  let := hH
  exact False.elim (not_finite H)

/-- The point has the required mapping property for every source. -/
theorem homotopyTerminal (Γ X : Type*) [Group Γ] [TopologicalSpace X] [MulAction Γ X] :
    HomotopyTerminalFor Γ X Point := by
  constructor
  · exact ⟨{ toFun := fun _ => default, continuous_toFun := continuous_const,
             map_smul' := fun _ _ => rfl }⟩
  · intro f g
    have : f = g := EquivariantMap.ext (fun _ => Subsingleton.elim _ _)
    subst g
    exact EquivariantlyHomotopic.refl f

/-- The one-point action of a finite discrete group is proper. -/
theorem proper [TopologicalSpace Γ] [DiscreteTopology Γ] [Finite Γ] :
    ProperSMul Γ Point := by
  let : ContinuousSMul Γ Point := ⟨continuous_of_discreteTopology⟩
  exact proper_of_finite

end Point
end BC4lean.ProperActions
