import BC4lean.LabeledAllowedChartLift
import BC4lean.LabeledAllowedGluing
import BC4lean.LabeledAttachmentDescent

/-! # Genuine pushout descent for an invariant face subcomplex -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open CategoryTheory CategoryTheory.Limits LabeledOrbitSimplex LabeledOrbitRealization
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]
variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

def allowedAttachmentChartMap (n : ℕ)
    (c : PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom)
    (s : LabeledOrbitSimplex Γ) (ha : s ∈ A) (hs : s.vertices.card = n + 1) :
    C(LabeledSimplexCoordinates Γ s,c.pt.V) :=
  c.inr.hom.hom.comp
    ((SigmaOrbitCells.inclusion _ (allowedChartCellOrbit A n s ha hs)).toContinuousMap.comp
      (allowedChartCellLift A n s ha hs))

theorem allowedAttachmentChartMap_boundary (n : ℕ)
    (c : PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom)
    (s : LabeledOrbitSimplex Γ) (ha : s ∈ A) (hs : s.vertices.card = n + 1)
    (w : LabeledSimplexCoordinates Γ s) (hw : w ∈ chartBoundary s) :
    allowedAttachmentChartMap A hA n c s ha hs w =
      c.inl.hom (allowedBoundaryPoint A hA n s ha hs w hw) := by
  obtain ⟨b,hb⟩ := chartCellLift_exists_boundary n s hs w hw
  let q := allowedChartCellOrbit A n s ha hs
  have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom c.condition)
    (⟨q,b⟩ : SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.diskBoundary.{u} n))
  change c.inl.hom (allowedCellBoundary A hA q b) =
    c.inr.hom ⟨q, OrbitCell.boundaryInclusion _ n b⟩ at h
  have hx : allowedCellBoundary A hA q b = allowedBoundaryPoint A hA n s ha hs w hw := by
    apply Subtype.ext
    apply Subtype.ext
    change labeledCellCharacteristic _ (OrbitCell.boundaryInclusion _ n b) = chart s w
    rw [hb]
    exact chartCellLift_characteristic n s hs w
  calc
    allowedAttachmentChartMap A hA n c s ha hs w =
        c.inr.hom ⟨q,OrbitCell.boundaryInclusion _ n b⟩ :=
      congrArg (fun z => c.inr.hom ⟨q,z⟩) hb.symm
    _ = c.inl.hom (allowedCellBoundary A hA q b) := h.symm
    _ = _ := congrArg (fun z => c.inl.hom z) hx

theorem allowedDiskSum_exists_boundary (n : ℕ)
    (p : SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.disk.{u} n))
    (hp : (allowedDiskSum A hA n p).val ∈ allowedSkeletalCarrier A n) :
    ∃ b : SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.diskBoundary.{u} n),
      allowedSphereSum A n b = p := by
  rcases p with ⟨⟨q,hq⟩,p⟩
  obtain ⟨⟨r,b⟩,hb⟩ := labeledDiskSum_exists_boundary n ⟨q,p⟩ hp
  have hqr : r = q := congrArg Sigma.fst hb
  subst r
  have he : OrbitCell.boundaryInclusion (cellStabilizer q) n b = p :=
    eq_of_heq (Sigma.mk.inj_iff.mp hb).2
  exact ⟨⟨⟨q,hq⟩,b⟩,congrArg (fun z => Sigma.mk (⟨q,hq⟩ : AllowedCellOrbit A n) z) he⟩

def allowedAttachmentContinuousDesc (n : ℕ)
    (c : PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom) :
    C(allowedSkeletalCarrier A (n + 1),c.pt.V) :=
  ⟨allowedGlue A n c.inl.hom.hom (allowedAttachmentChartMap A hA n c),
    continuous_allowedGlue A hA n c.inl.hom.hom (allowedAttachmentChartMap A hA n c)
      (allowedAttachmentChartMap_boundary A hA n c)⟩

theorem allowedAttachmentContinuousDesc_old (n : ℕ)
    (c : PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom) (x : allowedSkeletalCarrier A n) :
    allowedAttachmentContinuousDesc A hA n c (allowedSkeletalMap A (Nat.le_succ n) x) =
      c.inl.hom x :=
  allowedGlue_old A n c.inl.hom.hom (allowedAttachmentChartMap A hA n c) x

theorem allowedAttachmentContinuousDesc_disk (n : ℕ)
    (c : PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom)
    (p : SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.disk.{u} n)) :
    allowedAttachmentContinuousDesc A hA n c (allowedDiskSum A hA n p) = c.inr.hom p := by
  classical
  by_cases hp : (allowedDiskSum A hA n p).val ∈ allowedSkeletalCarrier A n
  · obtain ⟨b,hb⟩ := allowedDiskSum_exists_boundary A hA n p hp
    have he := congrArg (fun f => f b) (allowedAttachment_square A hA n)
    change allowedSkeletalMap A (Nat.le_succ n) (allowedBoundarySum A hA n b) =
      allowedDiskSum A hA n (allowedSphereSum A n b) at he
    rw [hb] at he
    rw [← he,allowedAttachmentContinuousDesc_old]
    have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom c.condition) b
    change c.inl.hom (allowedBoundarySum A hA n b) = c.inr.hom (allowedSphereSum A n b) at h
    simpa only [hb] using h
  · let x := (allowedDiskSum A hA n p).val
    let s := supportSimplex x.val
    have ha : s ∈ A := x.property
    have hs : s.vertices.card = n + 1 := by
      have h := (allowedDiskSum A hA n p).property
      change s.vertices.card ≤ n + 1 at h
      change ¬s.vertices.card ≤ n at hp
      omega
    let w : LabeledSimplexCoordinates Γ s := ⟨x.val.val,mem_coordinates_supportSimplex x.val⟩
    let p' : SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.disk.{u} n) :=
      ⟨allowedChartCellOrbit A n s ha hs,allowedChartCellLift A n s ha hs w⟩
    have hx : allowedDiskSum A hA n p' = allowedDiskSum A hA n p := by
      apply Subtype.ext
      apply Subtype.ext
      exact chartCellLift_characteristic n s hs w
    have hp' : (allowedDiskSum A hA n p').val ∉ allowedSkeletalCarrier A n := by rw [hx]; exact hp
    have he : p' = p := allowedDiskSum_injective_interior A hA n hp' hp hx
    have hg := allowedGlue_chart A hA n c.inl.hom.hom (allowedAttachmentChartMap A hA n c)
      (allowedAttachmentChartMap_boundary A hA n c) s ha hs w
    change allowedAttachmentContinuousDesc A hA n c (allowedDiskSum A hA n p) = c.inr.hom p' at hg
    simpa only [he] using hg

end BC4lean.ProperActions
