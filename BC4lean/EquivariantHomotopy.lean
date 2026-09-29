import BC4lean.EquivariantMaps
import Mathlib.Topology.Homotopy.Basic

/-! # Jointly continuous equivariant homotopies and fixed-point restriction -/
noncomputable section
namespace BC4lean.ProperActions
variable {Γ X Y Z : Type*} [Group Γ]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]

/-- A jointly continuous homotopy all of whose time slices are equivariant. -/
abbrev EquivariantHomotopy (f g : EquivariantMap Γ X Y) :=
  ContinuousMap.HomotopyWith f.toContinuousMap g.toContinuousMap
    (fun k => ∀ (a : Γ) (x : X), k (a • x) = a • k x)

namespace EquivariantHomotopy
variable {f₀ f₁ f₂ : EquivariantMap Γ X Y}

/-- The constant equivariant homotopy. -/
def refl (f : EquivariantMap Γ X Y) : EquivariantHomotopy f f :=
  ContinuousMap.HomotopyWith.refl f.toContinuousMap f.map_smul

/-- Reverse an equivariant homotopy. -/
def symm (F : EquivariantHomotopy f₀ f₁) : EquivariantHomotopy f₁ f₀ :=
  ContinuousMap.HomotopyWith.symm F

/-- Concatenate equivariant homotopies using the usual half-interval parametrization. -/
def trans (F : EquivariantHomotopy f₀ f₁) (G : EquivariantHomotopy f₁ f₂) :
    EquivariantHomotopy f₀ f₂ := ContinuousMap.HomotopyWith.trans F G

/-- Compose two equivariant homotopies at the same time parameter. -/
def comp {g₀ g₁ : EquivariantMap Γ Y Z} (G : EquivariantHomotopy g₀ g₁)
    (F : EquivariantHomotopy f₀ f₁) : EquivariantHomotopy (g₀.comp f₀) (g₁.comp f₁) where
  toHomotopy := G.toHomotopy.comp F.toHomotopy
  prop' t a x := by
    change G (t, F (t, a • x)) = a • G (t, F (t, x))
    have hF : F (t, a • x) = a • F (t, x) := F.prop t a x
    rw [hF]
    exact G.prop t a (F (t, x))

/-- Each time slice is itself a continuous equivariant map. -/
def atTime (F : EquivariantHomotopy f₀ f₁) (t : unitInterval) : EquivariantMap Γ X Y where
  toContinuousMap := F.toHomotopy.curry t
  map_smul' := F.prop t

@[simp] theorem at_apply (F : EquivariantHomotopy f₀ f₁) (t : unitInterval) (x : X) :
    F.atTime t x = F (t, x) := rfl
@[simp] theorem at_zero (F : EquivariantHomotopy f₀ f₁) : F.atTime 0 = f₀ := by
  ext x
  exact F.apply_zero x
@[simp] theorem at_one (F : EquivariantHomotopy f₀ f₁) : F.atTime 1 = f₁ := by
  ext x
  exact F.apply_one x

/-- Restrict the whole jointly continuous homotopy to subgroup fixed-point spaces. -/
def onFixedPoints (F : EquivariantHomotopy f₀ f₁) (H : Subgroup Γ) :
    ContinuousMap.Homotopy (f₀.fixedPointsMap H) (f₁.fixedPointsMap H) where
  toFun p := (F.atTime p.1).fixedPointsMap H p.2
  continuous_toFun := (F.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (F.apply_zero x.val)
  map_one_left x := Subtype.ext (F.apply_one x.val)

@[simp] theorem onFixedPoints_apply (F : EquivariantHomotopy f₀ f₁) (H : Subgroup Γ)
    (t : unitInterval) (x : FixedPointSpace H X) :
    (F.onFixedPoints H (t, x) : Y) = F (t, x.val) := rfl

@[simp] theorem onFixedPoints_refl (f : EquivariantMap Γ X Y) (H : Subgroup Γ) :
    (refl f).onFixedPoints H = ContinuousMap.Homotopy.refl (f.fixedPointsMap H) := by
  ext p; rfl

@[simp] theorem onFixedPoints_symm (F : EquivariantHomotopy f₀ f₁) (H : Subgroup Γ) :
    (symm F).onFixedPoints H = (F.onFixedPoints H).symm := by
  ext p; rfl

theorem onFixedPoints_trans (F : EquivariantHomotopy f₀ f₁) (G : EquivariantHomotopy f₁ f₂)
    (H : Subgroup Γ) : (trans F G).onFixedPoints H =
      (F.onFixedPoints H).trans (G.onFixedPoints H) := by
  ext ⟨t, x⟩
  simp only [onFixedPoints_apply, trans, ContinuousMap.HomotopyWith.trans_apply,
    ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

theorem onFixedPoints_comp {g₀ g₁ : EquivariantMap Γ Y Z}
    (G : EquivariantHomotopy g₀ g₁) (F : EquivariantHomotopy f₀ f₁) (H : Subgroup Γ) :
    (comp G F).onFixedPoints H = (G.onFixedPoints H).comp (F.onFixedPoints H) := by
  ext p; rfl
end EquivariantHomotopy

/-- Existence of a jointly continuous equivariant homotopy. -/
def EquivariantlyHomotopic (f g : EquivariantMap Γ X Y) : Prop :=
  Nonempty (EquivariantHomotopy f g)

namespace EquivariantlyHomotopic
variable {f₀ f₁ f₂ : EquivariantMap Γ X Y}

theorem refl (f : EquivariantMap Γ X Y) : EquivariantlyHomotopic f f :=
  ⟨EquivariantHomotopy.refl f⟩
theorem symm (h : EquivariantlyHomotopic f₀ f₁) : EquivariantlyHomotopic f₁ f₀ :=
  h.elim (fun F => ⟨EquivariantHomotopy.symm F⟩)
theorem trans (h : EquivariantlyHomotopic f₀ f₁) (k : EquivariantlyHomotopic f₁ f₂) :
    EquivariantlyHomotopic f₀ f₂ :=
  h.elim (fun F => k.elim (fun G => ⟨EquivariantHomotopy.trans F G⟩))
theorem comp {g₀ g₁ : EquivariantMap Γ Y Z} (h : EquivariantlyHomotopic g₀ g₁)
    (k : EquivariantlyHomotopic f₀ f₁) : EquivariantlyHomotopic (g₀.comp f₀) (g₁.comp f₁) :=
  h.elim (fun G => k.elim (fun F => ⟨EquivariantHomotopy.comp G F⟩))

/-- Fixed-point restriction sends equivariant homotopy to ordinary homotopy. -/
theorem onFixedPoints (h : EquivariantlyHomotopic f₀ f₁) (H : Subgroup Γ) :
    ContinuousMap.Homotopic (f₀.fixedPointsMap H) (f₁.fixedPointsMap H) :=
  h.elim (fun F => ⟨F.onFixedPoints H⟩)
end EquivariantlyHomotopic
end BC4lean.ProperActions
