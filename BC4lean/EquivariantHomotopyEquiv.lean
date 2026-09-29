import BC4lean.EquivariantHomotopy
import Mathlib.Topology.Homotopy.Equiv

/-! # Equivariant homotopy equivalences induce equivalences on fixed-point spaces -/
noncomputable section
namespace BC4lean.ProperActions

/-- Equivariant maps inverse up to jointly continuous equivariant homotopy. -/
structure EquivariantHomotopyEquiv (Γ X Y : Type*) [Group Γ]
    [TopologicalSpace X] [TopologicalSpace Y] [MulAction Γ X] [MulAction Γ Y] where
  toMap : EquivariantMap Γ X Y
  invMap : EquivariantMap Γ Y X
  left_inv : EquivariantlyHomotopic (invMap.comp toMap) EquivariantMap.id
  right_inv : EquivariantlyHomotopic (toMap.comp invMap) EquivariantMap.id

namespace EquivariantHomotopyEquiv
variable {Γ X Y Z : Type*} [Group Γ]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]

/-- The identity equivariant homotopy equivalence. -/
def refl : EquivariantHomotopyEquiv Γ X X where
  toMap := EquivariantMap.id
  invMap := EquivariantMap.id
  left_inv := EquivariantlyHomotopic.refl _
  right_inv := EquivariantlyHomotopic.refl _

/-- Reverse an equivariant homotopy equivalence. -/
def symm (e : EquivariantHomotopyEquiv Γ X Y) : EquivariantHomotopyEquiv Γ Y X where
  toMap := e.invMap
  invMap := e.toMap
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Compose equivariant homotopy equivalences. -/
def trans (e : EquivariantHomotopyEquiv Γ X Y) (d : EquivariantHomotopyEquiv Γ Y Z) :
    EquivariantHomotopyEquiv Γ X Z where
  toMap := d.toMap.comp e.toMap
  invMap := e.invMap.comp d.invMap
  left_inv := by
    have h := (EquivariantlyHomotopic.refl e.invMap).comp
      (d.left_inv.comp (EquivariantlyHomotopic.refl e.toMap))
    simp only [EquivariantMap.comp_assoc, EquivariantMap.id_comp] at h
    exact h.trans e.left_inv
  right_inv := by
    have h := (EquivariantlyHomotopic.refl d.toMap).comp
      (e.right_inv.comp (EquivariantlyHomotopic.refl d.invMap))
    simp only [EquivariantMap.comp_assoc, EquivariantMap.id_comp] at h
    exact h.trans d.right_inv

/-- Taking H-fixed points preserves equivariant homotopy equivalences. -/
def fixedPoints (e : EquivariantHomotopyEquiv Γ X Y) (H : Subgroup Γ) :
    ContinuousMap.HomotopyEquiv (FixedPointSpace H X) (FixedPointSpace H Y) where
  toFun := e.toMap.fixedPointsMap H
  invFun := e.invMap.fixedPointsMap H
  left_inv := by
    simpa only [EquivariantMap.fixedPointsMap_comp, EquivariantMap.fixedPointsMap_id]
      using e.left_inv.onFixedPoints H
  right_inv := by
    simpa only [EquivariantMap.fixedPointsMap_comp, EquivariantMap.fixedPointsMap_id]
      using e.right_inv.onFixedPoints H

@[simp] theorem fixedPoints_toFun_apply (e : EquivariantHomotopyEquiv Γ X Y) (H : Subgroup Γ)
    (x : FixedPointSpace H X) : ((e.fixedPoints H).toFun x : Y) = e.toMap x := rfl

@[simp] theorem fixedPoints_invFun_apply (e : EquivariantHomotopyEquiv Γ X Y) (H : Subgroup Γ)
    (y : FixedPointSpace H Y) : ((e.fixedPoints H).invFun y : X) = e.invMap y := rfl

end EquivariantHomotopyEquiv
end BC4lean.ProperActions
