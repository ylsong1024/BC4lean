import BC4lean.ProperFixedPoints
import Mathlib.GroupTheory.GroupAction.Hom

/-! # Continuous equivariant maps and their restrictions to fixed points -/
namespace BC4lean.ProperActions

/-- A continuous map commuting with the action of the same group on source and target. -/
structure EquivariantMap (Γ X Y : Type*) [Group Γ] [TopologicalSpace X]
    [TopologicalSpace Y] [MulAction Γ X] [MulAction Γ Y] extends C(X, Y) where
  map_smul' : ∀ (g : Γ) (x : X), toFun (g • x) = g • toFun x

namespace EquivariantMap
variable {Γ X Y Z W : Type*} [Group Γ]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
variable [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z] [MulAction Γ W]

instance instFunLike : FunLike (EquivariantMap Γ X Y) X Y where
  coe f := f.toContinuousMap
  coe_injective f g h := by
    cases f with
    | mk f hf =>
      cases g with
      | mk g hg =>
        have hfg : f = g := ContinuousMap.ext (congrFun h)
        cases hfg
        rfl

@[ext] theorem ext {f g : EquivariantMap Γ X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp] theorem map_smul (f : EquivariantMap Γ X Y) (g : Γ) (x : X) :
    f (g • x) = g • f x := f.map_smul' g x

theorem continuous (f : EquivariantMap Γ X Y) : Continuous f := f.toContinuousMap.continuous

/-- Forget topology, retaining Mathlib's existing equivariant-map structure. -/
def toMulActionHom (f : EquivariantMap Γ X Y) : X →[Γ] Y where
  toFun := f
  map_smul' := f.map_smul

/-- The equivariant identity map. -/
def id : EquivariantMap Γ X X where
  toContinuousMap := ContinuousMap.id X
  map_smul' _ _ := rfl

/-- Composition of continuous equivariant maps. -/
def comp (g : EquivariantMap Γ Y Z) (f : EquivariantMap Γ X Y) : EquivariantMap Γ X Z where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  map_smul' a x := by
    change g (f (a • x)) = a • g (f x)
    rw [f.map_smul, g.map_smul]

@[simp] theorem id_apply (x : X) : id (Γ := Γ) x = x := rfl
@[simp] theorem comp_apply (g : EquivariantMap Γ Y Z) (f : EquivariantMap Γ X Y) (x : X) :
    g.comp f x = g (f x) := rfl
@[simp] theorem id_comp (f : EquivariantMap Γ X Y) : id.comp f = f := by ext; rfl
@[simp] theorem comp_id (f : EquivariantMap Γ X Y) : f.comp id = f := by ext; rfl
theorem comp_assoc (h : EquivariantMap Γ Z W) (g : EquivariantMap Γ Y Z)
    (f : EquivariantMap Γ X Y) : (h.comp g).comp f = h.comp (g.comp f) := by ext; rfl

/-- An equivariant map sends subgroup fixed points to subgroup fixed points. -/
theorem map_fixedPoint (f : EquivariantMap Γ X Y) (H : Subgroup Γ) {x : X}
    (hx : x ∈ MulAction.fixedPoints H X) : f x ∈ MulAction.fixedPoints H Y := by
  intro h
  change (h : Γ) • f x = f x
  rw [← f.map_smul]
  exact congrArg f (hx h)

/-- Restrict an equivariant map to the H-fixed-point subspaces. -/
def fixedPointsMap (f : EquivariantMap Γ X Y) (H : Subgroup Γ) :
    C(FixedPointSpace H X, FixedPointSpace H Y) where
  toFun x := ⟨f x, f.map_fixedPoint H x.property⟩
  continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem fixedPointsMap_apply (f : EquivariantMap Γ X Y) (H : Subgroup Γ)
    (x : FixedPointSpace H X) : (f.fixedPointsMap H x : Y) = f x := rfl

@[simp] theorem fixedPointsMap_id (H : Subgroup Γ) :
    (id (Γ := Γ) (X := X)).fixedPointsMap H = ContinuousMap.id (FixedPointSpace H X) := by
  ext; rfl

@[simp] theorem fixedPointsMap_comp (g : EquivariantMap Γ Y Z) (f : EquivariantMap Γ X Y)
    (H : Subgroup Γ) :
    (g.comp f).fixedPointsMap H = (g.fixedPointsMap H).comp (f.fixedPointsMap H) := by
  ext; rfl

end EquivariantMap
end BC4lean.ProperActions
