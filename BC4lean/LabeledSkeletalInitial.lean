import BC4lean.LabeledSkeletalAction

/-! # The empty initial skeletal stage -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BC4lean.ProperActions.LabeledOrbitRealization
universe u
variable {Γ : Type u} [Group Γ]

instance skeletalSpaceZero_isEmpty : IsEmpty (SkeletalSpace (Γ := Γ) 0) := by
  change IsEmpty (skeletalCarrier (Γ := Γ) 0)
  rw [skeletalCarrier_zero]
  infer_instance

/-- The empty stage is initial as an actual topological Γ-action. -/
def skeletalZero_isInitial :
    IsInitial (topologicalAction Γ (SkeletalSpace (Γ := Γ) 0)) := by
  let : IsEmpty ((topologicalAction Γ (SkeletalSpace (Γ := Γ) 0)).V) :=
    ⟨fun x => isEmptyElim (show SkeletalSpace (Γ := Γ) 0 from x)⟩
  let h (Y : Action TopCat.{u} Γ) : Unique
      (topologicalAction Γ (SkeletalSpace (Γ := Γ) 0) ⟶ Y) :=
    { default :=
        { hom := TopCat.ofHom ⟨fun x => isEmptyElim x, by fun_prop⟩
          comm := fun _ => by ext x; exact isEmptyElim x }
      uniq := fun f => by ext x; exact isEmptyElim x }
  exact IsInitial.ofUnique _

/-- The dimension filtration starts at the initial topological action. -/
def skeletalIsoBot : (⊥_ (Action TopCat.{u} Γ)) ≅ (skeletalSequence (Γ := Γ)).obj 0 :=
  initialIsInitial.uniqueUpToIso skeletalZero_isInitial

end BC4lean.ProperActions.LabeledOrbitRealization
