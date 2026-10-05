import BC4lean.LabeledAllowedSkeletalColimit

/-! # Initial stage and chart detection of skeletal maps for allowed families -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BC4lean.ProperActions.LabeledOrbitRealization
universe u
variable {Γ : Type u} [Group Γ]
variable (A : Set (LabeledOrbitSimplex Γ))

instance allowedSkeletalZero_isEmpty : IsEmpty (allowedSkeletalCarrier A 0) :=
  ⟨fun x => by
    have hx : x.val.val ∈ skeletalCarrier (Γ := Γ) 0 := x.property
    rw [skeletalCarrier_zero] at hx
    exact hx⟩

variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]

def allowedSkeletalZero_isInitial :
    IsInitial (topologicalAction Γ (allowedSkeletalCarrier A 0)) := by
  let : IsEmpty ((topologicalAction Γ (allowedSkeletalCarrier A 0)).V) :=
    ⟨fun x => isEmptyElim (show allowedSkeletalCarrier A 0 from x)⟩
  let h (Y : Action TopCat.{u} Γ) : Unique
      (topologicalAction Γ (allowedSkeletalCarrier A 0) ⟶ Y) :=
    { default :=
        { hom := TopCat.ofHom ⟨fun x => isEmptyElim x, by fun_prop⟩
          comm := fun _ => by ext x; exact isEmptyElim x }
      uniq := fun f => by ext x; exact isEmptyElim x }
  exact IsInitial.ofUnique _

def allowedSkeletalIsoBot :
    (⊥_ (Action TopCat.{u} Γ)) ≅ (allowedSkeletalSequence A).obj 0 :=
  initialIsInitial.uniqueUpToIso (allowedSkeletalZero_isInitial A)

variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

theorem allowed_skeletal_hom_ext {Y : Type*} (n : ℕ)
    {f g : allowedSkeletalCarrier A (n + 1) → Y}
    (hold : ∀ x, f (allowedSkeletalMap A (Nat.le_succ n) x) =
      g (allowedSkeletalMap A (Nat.le_succ n) x))
    (hchart : ∀ s (hs : s ∈ A) (hn : s.vertices.card = n + 1) w,
      f (boundedAllowedSkeletalChart A hA (n + 1) s hs (by omega) w) =
        g (boundedAllowedSkeletalChart A hA (n + 1) s hs (by omega) w)) : f = g := by
  funext x
  by_cases hx : x.val ∈ allowedSkeletalCarrier A n
  · exact hold ⟨x.val, hx⟩
  · let s := supportSimplex x.val.val
    have hs : s ∈ A := x.val.property
    have hn : s.vertices.card = n + 1 := by
      have hl := x.property
      change s.vertices.card ≤ n + 1 at hl
      change ¬ s.vertices.card ≤ n at hx
      omega
    exact hchart s hs hn ⟨x.val.val.val, mem_coordinates_supportSimplex x.val.val⟩

end BC4lean.ProperActions.LabeledOrbitRealization
