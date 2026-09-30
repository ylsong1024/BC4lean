import BC4lean.EquivariantHomotopyEquiv

/-! # Uniqueness from a homotopy-universal mapping property

These lemmas isolate the uniqueness argument. They do not assert that a space
with this mapping property exists, or derive it from fixed-point contractibility.
-/
namespace BC4lean.ProperActions

variable {Γ X Y Z : Type*} [Group Γ]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]

/-- Maps from a specified source exist and are unique up to equivariant homotopy. -/
def HomotopyTerminalFor (Γ X Y : Type*) [Group Γ]
    [TopologicalSpace X] [TopologicalSpace Y] [MulAction Γ X] [MulAction Γ Y] : Prop :=
  Nonempty (EquivariantMap Γ X Y) ∧
    ∀ f g : EquivariantMap Γ X Y, EquivariantlyHomotopic f g

/-- The universal-property uniqueness argument, with its four premises explicit. -/
theorem homotopyTerminal_unique
    (hXY : HomotopyTerminalFor Γ X Y) (hYX : HomotopyTerminalFor Γ Y X)
    (hXX : HomotopyTerminalFor Γ X X) (hYY : HomotopyTerminalFor Γ Y Y) :
    Nonempty (EquivariantHomotopyEquiv Γ X Y) := by
  obtain ⟨f⟩ := hXY.1
  obtain ⟨g⟩ := hYX.1
  exact ⟨⟨f, g, hXX.2 _ _, hYY.2 _ _⟩⟩

/-- Homotopy-terminal targets can be replaced by equivariantly homotopy-equivalent targets. -/
theorem HomotopyTerminalFor.of_equiv (h : HomotopyTerminalFor Γ X Y)
    (e : EquivariantHomotopyEquiv Γ Y Z) : HomotopyTerminalFor Γ X Z := by
  constructor
  · obtain ⟨f⟩ := h.1
    exact ⟨e.toMap.comp f⟩
  · intro f g
    have hf : EquivariantlyHomotopic (e.toMap.comp (e.invMap.comp f)) f := by
      simpa only [← EquivariantMap.comp_assoc, EquivariantMap.id_comp]
        using e.right_inv.comp (EquivariantlyHomotopic.refl f)
    have hg : EquivariantlyHomotopic (e.toMap.comp (e.invMap.comp g)) g := by
      simpa only [← EquivariantMap.comp_assoc, EquivariantMap.id_comp]
        using e.right_inv.comp (EquivariantlyHomotopic.refl g)
    exact hf.symm.trans (((EquivariantlyHomotopic.refl e.toMap).comp
      (h.2 (e.invMap.comp f) (e.invMap.comp g))).trans hg)

/-- Uniqueness also identifies all subgroup fixed-point homotopy types. -/
theorem homotopyTerminal_fixedPoints_unique
    (hXY : HomotopyTerminalFor Γ X Y) (hYX : HomotopyTerminalFor Γ Y X)
    (hXX : HomotopyTerminalFor Γ X X) (hYY : HomotopyTerminalFor Γ Y Y)
    (H : Subgroup Γ) :
    Nonempty (ContinuousMap.HomotopyEquiv (FixedPointSpace H X) (FixedPointSpace H Y)) := by
  obtain ⟨e⟩ := homotopyTerminal_unique hXY hYX hXX hYY
  exact ⟨e.fixedPoints H⟩

end BC4lean.ProperActions
