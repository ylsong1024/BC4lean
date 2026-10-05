import BC4lean.LabeledOrbitSkeleta
import BC4lean.EquivariantCW

/-! # Equivariant skeletal subspaces and their inclusions -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

abbrev SkeletalSpace (n : ℕ) := skeletalCarrier (Γ := Γ) n

instance (n : ℕ) : MulAction Γ (SkeletalSpace (Γ := Γ) n) where
  smul g x := ⟨g • x.val, skeletalCarrier_smul n g x.property⟩
  one_smul x := Subtype.ext (one_smul Γ x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance (n : ℕ) : ContinuousConstSMul Γ (SkeletalSpace (Γ := Γ) n) where
  continuous_const_smul g := (continuous_const_smul g).subtype_map
    (fun _ hx => skeletalCarrier_smul n g hx)

def skeletalInclusion (n : ℕ) : EquivariantMap Γ (SkeletalSpace (Γ := Γ) n)
    (LabeledOrbitRealization Γ) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  map_smul' _ _ := rfl

def skeletalMap {m n : ℕ} (h : m ≤ n) :
    EquivariantMap Γ (SkeletalSpace (Γ := Γ) m) (SkeletalSpace (Γ := Γ) n) where
  toFun x := ⟨x.val, skeletalCarrier_mono h x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _
  map_smul' _ _ := rfl

/-- The actual dimension filtration as a functor of topological actions. -/
def skeletalSequence : ℕ ⥤ Action TopCat Γ where
  obj n := topologicalAction Γ (SkeletalSpace (Γ := Γ) n)
  map f := (skeletalMap (Γ := Γ) (leOfHom f)).toActionHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

def skeletalCocone : Cocone (skeletalSequence (Γ := Γ)) where
  pt := topologicalAction Γ (LabeledOrbitRealization Γ)
  ι := {
    app := fun n => (skeletalInclusion (Γ := Γ) n).toActionHom
    naturality := fun _ _ _ => by ext x; rfl }

/-- Every finite simplex chart factors continuously through its dimension stage. -/
def skeletalChart (s : LabeledOrbitSimplex Γ) :
    LabeledSimplexCoordinates Γ s → SkeletalSpace (Γ := Γ) s.vertices.card :=
  fun w => ⟨chart s w, (mem_skeletalCarrier_iff _ _).mpr ⟨s, le_rfl, w.property⟩⟩

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem continuous_skeletalChart (s : LabeledOrbitSimplex Γ) :
    Continuous (skeletalChart (Γ := Γ) s) := (continuous_chart s).subtype_mk _

end BC4lean.ProperActions.LabeledOrbitRealization
