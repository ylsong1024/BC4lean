import BC4lean.LabeledSkeletalAction

/-! # The weak realization is the colimit of its dimension filtration -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

def canonicalStagePoint (x : LabeledOrbitRealization Γ) :
    SkeletalSpace (Γ := Γ) (supportSimplex x).vertices.card := ⟨x, by change (supportSimplex x).vertices.card ≤ (supportSimplex x).vertices.card; exact le_rfl⟩

def skeletalDescValue (c : Cocone (skeletalSequence (Γ := Γ)))
    (x : LabeledOrbitRealization Γ) : c.pt.V :=
  (c.ι.app (supportSimplex x).vertices.card).hom (canonicalStagePoint x)

theorem skeletalDescValue_eq (c : Cocone (skeletalSequence (Γ := Γ)))
    (n : ℕ) (x : LabeledOrbitRealization Γ) (hx : x ∈ skeletalCarrier n) :
    skeletalDescValue c x = (c.ι.app n).hom ⟨x, hx⟩ := by
  have h : (supportSimplex x).vertices.card ≤ n := hx
  have he := ConcreteCategory.congr_hom
    (congrArg Action.Hom.hom (c.w (homOfLE h))) (canonicalStagePoint x)
  change (c.ι.app n).hom ⟨x, hx⟩ = skeletalDescValue c x at he
  exact he.symm

theorem continuous_skeletalDescValue (c : Cocone (skeletalSequence (Γ := Γ))) :
    Continuous (skeletalDescValue c) := by
  apply (continuous_iff _).mpr
  intro s
  have hc := (c.ι.app s.vertices.card).hom.hom.continuous.comp (continuous_skeletalChart s)
  have he : (fun w => skeletalDescValue c (chart s w)) =
      (fun w => (c.ι.app s.vertices.card).hom (skeletalChart s w)) := by
    funext w
    exact skeletalDescValue_eq c s.vertices.card (chart s w)
      ((mem_skeletalCarrier_iff _ _).mpr ⟨s, le_rfl, w.property⟩)
  change Continuous (fun w => skeletalDescValue c (chart s w))
  rw [he]
  exact hc

def skeletalDesc (c : Cocone (skeletalSequence (Γ := Γ))) :
    topologicalAction Γ (LabeledOrbitRealization Γ) ⟶ c.pt where
  hom := TopCat.ofHom ⟨skeletalDescValue c, continuous_skeletalDescValue c⟩
  comm g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro (x : LabeledOrbitRealization Γ)
    let n := (supportSimplex x).vertices.card
    have hx : x ∈ skeletalCarrier n := by change (supportSimplex x).vertices.card ≤ n; exact le_rfl
    have hgx := skeletalCarrier_smul n g hx
    change skeletalDescValue c (g • x) = (c.pt.ρ g).hom (skeletalDescValue c x)
    rw [skeletalDescValue_eq c n (g • x) hgx, skeletalDescValue_eq c n x hx]
    have he := ConcreteCategory.congr_hom ((c.ι.app n).comm g)
      (⟨x, hx⟩ : SkeletalSpace (Γ := Γ) n)
    change (c.ι.app n).hom ⟨g • x, hgx⟩ =
      (c.pt.ρ g).hom ((c.ι.app n).hom ⟨x, hx⟩) at he
    exact he

/-- Explicit action-valued colimit witness for the weak realization. -/
def skeletalCoconeIsColimit : IsColimit (skeletalCocone (Γ := Γ)) where
  desc := skeletalDesc
  fac c n := by
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change skeletalDescValue c x.val = (c.ι.app n).hom x
    exact skeletalDescValue_eq c n x.val x.property
  uniq c m hm := by
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro (x : LabeledOrbitRealization Γ)
    have he := ConcreteCategory.congr_hom (congrArg Action.Hom.hom
      (hm (supportSimplex x).vertices.card)) (canonicalStagePoint x)
    change m.hom x = skeletalDescValue c x at he
    exact he

end BC4lean.ProperActions.LabeledOrbitRealization
