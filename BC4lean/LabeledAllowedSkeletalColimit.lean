import BC4lean.LabeledAllowedSkeletalTopology
import BC4lean.EquivariantCW

/-! # Actual action-valued skeletal colimit of an invariant face subcomplex -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]

def allowedSkeletalInclusion (n : ℕ) :
    EquivariantMap Γ (allowedSkeletalCarrier A n) (AllowedRealization A) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  map_smul' _ _ := rfl

def allowedSkeletalMap {m n : ℕ} (h : m ≤ n) :
    EquivariantMap Γ (allowedSkeletalCarrier A m) (allowedSkeletalCarrier A n) where
  toFun x := ⟨x.val, allowedSkeletalCarrier_mono A h x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _
  map_smul' _ _ := rfl

def allowedSkeletalSequence : ℕ ⥤ Action TopCat Γ where
  obj n := topologicalAction Γ (allowedSkeletalCarrier A n)
  map f := (allowedSkeletalMap A (leOfHom f)).toActionHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

def allowedSkeletalCocone : Cocone (allowedSkeletalSequence A) where
  pt := topologicalAction Γ (AllowedRealization A)
  ι := {
    app := fun n => (allowedSkeletalInclusion A n).toActionHom
    naturality := fun _ _ _ => by ext x; rfl }

def canonicalAllowedStagePoint (x : AllowedRealization A) :
    allowedSkeletalCarrier A (supportSimplex x.val).vertices.card :=
  ⟨x, by change (supportSimplex x.val).vertices.card ≤ (supportSimplex x.val).vertices.card; exact le_rfl⟩

def allowedSkeletalDescValue (c : Cocone (allowedSkeletalSequence A))
    (x : AllowedRealization A) : c.pt.V :=
  (c.ι.app (supportSimplex x.val).vertices.card).hom (canonicalAllowedStagePoint A x)

theorem allowedSkeletalDescValue_eq (c : Cocone (allowedSkeletalSequence A))
    (n : ℕ) (x : AllowedRealization A) (hx : x ∈ allowedSkeletalCarrier A n) :
    allowedSkeletalDescValue A c x = (c.ι.app n).hom ⟨x, hx⟩ := by
  have h : (supportSimplex x.val).vertices.card ≤ n := hx
  have he := ConcreteCategory.congr_hom
    (congrArg Action.Hom.hom (c.w (homOfLE h))) (canonicalAllowedStagePoint A x)
  change (c.ι.app n).hom ⟨x, hx⟩ = allowedSkeletalDescValue A c x at he
  exact he.symm

variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

include hA in
theorem continuous_allowedSkeletalDescValue (c : Cocone (allowedSkeletalSequence A)) :
    Continuous (allowedSkeletalDescValue A c) := by
  apply (continuous_iff_allowedCharts A hA _).mpr
  intro s hs
  have hc := (c.ι.app s.vertices.card).hom.hom.continuous.comp
    (continuous_boundedAllowedSkeletalChart A hA s.vertices.card s hs le_rfl)
  have he : (fun w => allowedSkeletalDescValue A c (allowedChart A hA s hs w)) =
      (fun w => (c.ι.app s.vertices.card).hom
        (boundedAllowedSkeletalChart A hA s.vertices.card s hs le_rfl w)) := by
    funext w
    exact allowedSkeletalDescValue_eq A c s.vertices.card (allowedChart A hA s hs w)
      ((mem_skeletalCarrier_iff _ _).mpr ⟨s, le_rfl, w.property⟩)
  change Continuous (fun w => allowedSkeletalDescValue A c (allowedChart A hA s hs w))
  rw [he]
  exact hc

def allowedSkeletalDesc (c : Cocone (allowedSkeletalSequence A)) :
    topologicalAction Γ (AllowedRealization A) ⟶ c.pt where
  hom := TopCat.ofHom ⟨allowedSkeletalDescValue A c, continuous_allowedSkeletalDescValue A hA c⟩
  comm g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro (x : AllowedRealization A)
    let n := (supportSimplex x.val).vertices.card
    have hx : x ∈ allowedSkeletalCarrier A n := by
      change (supportSimplex x.val).vertices.card ≤ n
      exact le_rfl
    have hgx : g • x ∈ allowedSkeletalCarrier A n := skeletalCarrier_smul n g hx
    change allowedSkeletalDescValue A c (g • x) = (c.pt.ρ g).hom (allowedSkeletalDescValue A c x)
    rw [allowedSkeletalDescValue_eq A c n (g • x) hgx, allowedSkeletalDescValue_eq A c n x hx]
    have he := ConcreteCategory.congr_hom ((c.ι.app n).comm g)
      (⟨x, hx⟩ : allowedSkeletalCarrier A n)
    change (c.ι.app n).hom ⟨g • x, hgx⟩ =
      (c.pt.ρ g).hom ((c.ι.app n).hom ⟨x, hx⟩) at he
    exact he

def allowedSkeletalCoconeIsColimit : IsColimit (allowedSkeletalCocone A) where
  desc := allowedSkeletalDesc A hA
  fac c n := by
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change allowedSkeletalDescValue A c x.val = (c.ι.app n).hom x
    exact allowedSkeletalDescValue_eq A c n x.val x.property
  uniq c m hm := by
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro (x : AllowedRealization A)
    have he := ConcreteCategory.congr_hom (congrArg Action.Hom.hom
      (hm (supportSimplex x.val).vertices.card)) (canonicalAllowedStagePoint A x)
    change m.hom x = allowedSkeletalDescValue A c x at he
    exact he

end BC4lean.ProperActions.LabeledOrbitRealization
