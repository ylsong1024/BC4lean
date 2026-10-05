import BC4lean.LabeledAllowedDescent
import BC4lean.LabeledAllowedInitial

/-! # Actual equivariant CW structure of invariant face subcomplexes

Every allowed dimension stage is a proved pushout of finite-isotropy orbit
disks. The actual induced subcomplex is the proved colimit of these stages.
Only invariance and closure under faces are hypotheses.
-/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open CategoryTheory CategoryTheory.Limits LabeledOrbitSimplex LabeledOrbitRealization
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]
variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

/-- Each finite top-dimensional chart is the image of its actual orbit disk. -/
theorem allowed_chart_stage_eq_disk (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (ha : s ∈ A) (hs : s.vertices.card = n + 1) (w : LabeledSimplexCoordinates Γ s) :
    boundedAllowedSkeletalChart A hA (n + 1) s ha (by omega) w =
      allowedDiskSum A hA n ⟨allowedChartCellOrbit A n s ha hs,allowedChartCellLift A n s ha hs w⟩ := by
  exact (allowedChartCellLift_characteristic A hA n s ha hs w).symm

/-- Topological descent commutes with the actual action on every stage. -/
theorem allowedAttachmentContinuousDesc_comm (n : ℕ)
    (c : PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom) (g : Γ)
    (x : allowedSkeletalCarrier A (n + 1)) :
    allowedAttachmentContinuousDesc A hA n c (g • x) =
      (c.pt.ρ g).hom (allowedAttachmentContinuousDesc A hA n c x) := by
  have he : (fun x => allowedAttachmentContinuousDesc A hA n c (g • x)) =
      (fun x => (c.pt.ρ g).hom (allowedAttachmentContinuousDesc A hA n c x)) := by
    apply allowed_skeletal_hom_ext A hA n
    · intro y
      have hy : g • allowedSkeletalMap A (Nat.le_succ n) y = allowedSkeletalMap A (Nat.le_succ n) (g • y) := rfl
      rw [hy, allowedAttachmentContinuousDesc_old, allowedAttachmentContinuousDesc_old]
      exact ConcreteCategory.congr_hom (c.inl.comm g) y
    · intro s ha hs w
      let p : SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.disk.{u} n) :=
        ⟨allowedChartCellOrbit A n s ha hs,allowedChartCellLift A n s ha hs w⟩
      rw [allowed_chart_stage_eq_disk A hA n s ha hs w]
      calc
        allowedAttachmentContinuousDesc A hA n c (g • allowedDiskSum A hA n p) =
            allowedAttachmentContinuousDesc A hA n c (allowedDiskSum A hA n (g • p)) :=
          congrArg (allowedAttachmentContinuousDesc A hA n c) ((allowedDiskSum A hA n).map_smul g p).symm
        _ = c.inr.hom (g • p) := allowedAttachmentContinuousDesc_disk A hA n c (g • p)
        _ = (c.pt.ρ g).hom (c.inr.hom p) := ConcreteCategory.congr_hom (c.inr.comm g) p
        _ = _ := congrArg (fun z => (c.pt.ρ g).hom z) (allowedAttachmentContinuousDesc_disk A hA n c p).symm
  exact congrFun he x

/-- The descended map is a genuine morphism of topological actions. -/
def allowedAttachmentActionDesc (n : ℕ)
    (c : PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom) :
    topologicalAction Γ (allowedSkeletalCarrier A (n + 1)) ⟶ c.pt where
  hom := TopCat.ofHom (allowedAttachmentContinuousDesc A hA n c)
  comm g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact allowedAttachmentContinuousDesc_comm A hA n c g x

/-- Full universal-property witness for the orbit-disk attaching pushout. -/
def allowedAttachmentIsColimit (n : ℕ) : IsColimit (allowedAttachmentCocone A hA n) := by
  refine PushoutCocone.IsColimit.mk _ (allowedAttachmentActionDesc A hA n) ?_ ?_ ?_
  · intro c
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact allowedAttachmentContinuousDesc_old A hA n c x
  · intro c
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    exact allowedAttachmentContinuousDesc_disk A hA n c p
  · intro c m hleft hright
    have hmfun : (fun x : allowedSkeletalCarrier A (n + 1) => m.hom x) =
        (fun x => allowedAttachmentContinuousDesc A hA n c x) := by
      apply allowed_skeletal_hom_ext A hA n
      · intro x
        have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom hleft) x
        change m.hom (allowedSkeletalMap A (Nat.le_succ n) x) = c.inl.hom x at h
        rw [allowedAttachmentContinuousDesc_old]
        exact h
      · intro s ha hs w
        rw [allowed_chart_stage_eq_disk A hA n s ha hs w]
        have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom hright)
          (⟨allowedChartCellOrbit A n s ha hs,allowedChartCellLift A n s ha hs w⟩ : SigmaOrbitCells
            (allowedCellIsotropy A (n := n)) (TopCat.disk.{u} n))
        exact h.trans (allowedAttachmentContinuousDesc_disk A hA n c _).symm
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact congrFun hmfun x

/-- The skeletal transition attaches exactly the proved dimension-n orbit disks. -/
def allowedCellAttachment (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u} (equivariantBasicCell (Γ := Γ) n)
      (allowedSkeletalMap A (Nat.le_succ n)).toActionHom where
  ι := AllowedCellOrbit A n
  π := allowedCellIsotropy A
  cofan₁ := orbitCellCofan (allowedCellIsotropy A) (TopCat.diskBoundary.{u} n)
  cofan₂ := orbitCellCofan (allowedCellIsotropy A) (TopCat.disk.{u} n)
  isColimit₁ := orbitCellCofan_isColimit _ _
  isColimit₂ := orbitCellCofan_isColimit _ _
  m := (allowedSphereSum A n).toActionHom
  hm _ := rfl
  g₁ := (allowedBoundarySum A hA n).toActionHom
  g₂ := (allowedDiskSum A hA n).toActionHom
  isPushout := IsPushout.of_isColimit (allowedAttachmentIsColimit A hA n)

namespace LabeledOrbitRealization
/-- A genuine finite-isotropy equivariant CW structure, with actual disk pushouts
and the actual weak-topology skeletal colimit. -/
def allowedEquivariantCWComplex : EquivariantCWComplex (topologicalAction Γ (AllowedRealization A)) where
  F := allowedSkeletalSequence A
  isoBot := (allowedSkeletalIsoBot A).symm
  incl := (allowedSkeletalCocone A).ι
  isColimit := allowedSkeletalCoconeIsColimit A hA
  fac := initialIsInitial.hom_ext _ _
  attachCells n _ := allowedCellAttachment A hA n

end LabeledOrbitRealization
end BC4lean.ProperActions
