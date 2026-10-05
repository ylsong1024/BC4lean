import BC4lean.LabeledAttachmentDescent
import BC4lean.LabeledSkeletalInitial
import BC4lean.LabeledSkeletalColimit

/-! # Actual equivariant CW structure of the labeled weak realization

Every stage is a proved pushout of finite-isotropy orbit disks. The weak
realization is the proved colimit of these stages. No CW structure is assumed.
-/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open CategoryTheory CategoryTheory.Limits LabeledOrbitSimplex LabeledOrbitRealization

/-- Each finite top-dimensional chart is the image of its actual orbit disk. -/
theorem chart_stage_eq_disk (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s.vertices.card = n + 1) (w : LabeledSimplexCoordinates Γ s) :
    boundedSkeletalChart (n + 1) s (by omega) w =
      labeledDiskSum n ⟨chartCellOrbit n s hs,chartCellLift n s hs w⟩ := by
  apply Subtype.ext
  exact (chartCellLift_characteristic n s hs w).symm

/-- Topological descent commutes with the actual action on every stage. -/
theorem attachmentContinuousDesc_comm (n : ℕ)
    (c : PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom) (g : Γ)
    (x : SkeletalSpace (Γ := Γ) (n + 1)) :
    attachmentContinuousDesc n c (g • x) =
      (c.pt.ρ g).hom (attachmentContinuousDesc n c x) := by
  have he : (fun x => attachmentContinuousDesc n c (g • x)) =
      (fun x => (c.pt.ρ g).hom (attachmentContinuousDesc n c x)) := by
    apply skeletal_hom_ext n
    · intro y
      have hy : g • skeletalMap (Nat.le_succ n) y = skeletalMap (Nat.le_succ n) (g • y) := rfl
      rw [hy, attachmentContinuousDesc_old, attachmentContinuousDesc_old]
      exact ConcreteCategory.congr_hom (c.inl.comm g) y
    · intro s hs w
      let p : SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.disk.{u} n) :=
        ⟨chartCellOrbit n s hs,chartCellLift n s hs w⟩
      rw [chart_stage_eq_disk n s hs w]
      calc
        attachmentContinuousDesc n c (g • labeledDiskSum n p) =
            attachmentContinuousDesc n c (labeledDiskSum n (g • p)) :=
          congrArg (attachmentContinuousDesc n c) ((labeledDiskSum n).map_smul g p).symm
        _ = c.inr.hom (g • p) := attachmentContinuousDesc_disk n c (g • p)
        _ = (c.pt.ρ g).hom (c.inr.hom p) := ConcreteCategory.congr_hom (c.inr.comm g) p
        _ = _ := congrArg (fun z => (c.pt.ρ g).hom z) (attachmentContinuousDesc_disk n c p).symm
  exact congrFun he x

/-- The descended map is a genuine morphism of topological actions. -/
def attachmentActionDesc (n : ℕ)
    (c : PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom) :
    topologicalAction Γ (SkeletalSpace (Γ := Γ) (n + 1)) ⟶ c.pt where
  hom := TopCat.ofHom (attachmentContinuousDesc n c)
  comm g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact attachmentContinuousDesc_comm n c g x

/-- Full universal-property witness for the orbit-disk attaching pushout. -/
def labeledAttachmentIsColimit (n : ℕ) : IsColimit (labeledAttachmentCocone (Γ := Γ) n) := by
  refine PushoutCocone.IsColimit.mk _ (attachmentActionDesc n) ?_ ?_ ?_
  · intro c
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact attachmentContinuousDesc_old n c x
  · intro c
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    exact attachmentContinuousDesc_disk n c p
  · intro c m hleft hright
    have hmfun : (fun x : SkeletalSpace (Γ := Γ) (n + 1) => m.hom x) =
        (fun x => attachmentContinuousDesc n c x) := by
      apply skeletal_hom_ext n
      · intro x
        have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom hleft) x
        change m.hom (skeletalMap (Nat.le_succ n) x) = c.inl.hom x at h
        rw [attachmentContinuousDesc_old]
        exact h
      · intro s hs w
        rw [chart_stage_eq_disk n s hs w]
        have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom hright)
          (⟨chartCellOrbit n s hs,chartCellLift n s hs w⟩ : SigmaOrbitCells
            (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.disk.{u} n))
        exact h.trans (attachmentContinuousDesc_disk n c _).symm
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact congrFun hmfun x

/-- The skeletal transition attaches exactly the proved dimension-n orbit disks. -/
def labeledCellAttachment (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u} (equivariantBasicCell (Γ := Γ) n)
      (skeletalMap (Γ := Γ) (Nat.le_succ n)).toActionHom where
  ι := CellOrbit Γ n
  π := labeledCellIsotropy
  cofan₁ := orbitCellCofan labeledCellIsotropy (TopCat.diskBoundary.{u} n)
  cofan₂ := orbitCellCofan labeledCellIsotropy (TopCat.disk.{u} n)
  isColimit₁ := orbitCellCofan_isColimit _ _
  isColimit₂ := orbitCellCofan_isColimit _ _
  m := (labeledSphereSum n).toActionHom
  hm _ := rfl
  g₁ := (labeledBoundarySum n).toActionHom
  g₂ := (labeledDiskSum n).toActionHom
  isPushout := IsPushout.of_isColimit (labeledAttachmentIsColimit n)

namespace LabeledOrbitRealization
/-- A genuine finite-isotropy equivariant CW structure, with actual disk pushouts
and the actual weak-topology skeletal colimit. -/
def equivariantCWComplex : EquivariantCWComplex (topologicalAction Γ (LabeledOrbitRealization Γ)) where
  F := skeletalSequence
  isoBot := skeletalIsoBot.symm
  incl := skeletalCocone.ι
  isColimit := skeletalCoconeIsColimit
  fac := initialIsInitial.hom_ext _ _
  attachCells n _ := labeledCellAttachment n

end LabeledOrbitRealization
end BC4lean.ProperActions
