import BC4lean.LabeledCellInteriors
import BC4lean.LabeledCellChartLift
import BC4lean.LabeledSkeletalGluing

/-! # Descent data from the actual orbit-disk attachment cocone -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open CategoryTheory CategoryTheory.Limits LabeledOrbitSimplex LabeledOrbitRealization

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- Pulling a translated chart back preserves its entire face boundary. -/
theorem labeledChartTransport_boundary (g : Γ) (s t : LabeledOrbitSimplex Γ)
    (he : g • s = t) (w : LabeledSimplexCoordinates Γ t)
    (hw : w ∈ chartBoundary t) :
    labeledChartTransport g s t he w ∈ chartBoundary s := by
  rcases hw with ⟨v,hv,hz⟩
  refine ⟨g⁻¹ • v, ?_, ?_⟩
  · classical
    rw [← he] at hv
    change v ∈ s.vertices.image (fun u => g • u) at hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    simpa using hu
  · change w.val ((g⁻¹)⁻¹ • (g⁻¹ • v)) = 0
    simpa using hz

omit [DiscreteTopology Γ] in
/-- A boundary chart point lifts through the actual orbit sphere inclusion. -/
theorem chartCellLift_exists_boundary (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s.vertices.card = n + 1) (w : LabeledSimplexCoordinates Γ s)
    (hw : w ∈ chartBoundary s) :
    ∃ b : OrbitCell (cellStabilizer (chartCellOrbit n s hs)) (TopCat.diskBoundary.{u} n),
      OrbitCell.boundaryInclusion _ n b = chartCellLift n s hs w := by
  let q := chartCellOrbit n s hs
  let g := chartCellTranslate n s hs
  let z := labeledChartTransport g (cellRepresentative q).val s (chartCellTranslate_spec n s hs) w
  have hz : z ∈ chartBoundary (cellRepresentative q).val :=
    labeledChartTransport_boundary g _ _ _ w hw
  have hb := (representativeDiskHomeomorph_boundary q z).mp hz
  refine ⟨(QuotientGroup.mk g, ULift.up ⟨(representativeDiskHomeomorph q z).val,hb⟩), ?_⟩
  rfl

/-- Each attachment cocone prescribes a continuous map on every top chart. -/
def attachmentChartMap (n : ℕ)
    (c : PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom)
    (s : LabeledOrbitSimplex Γ) (hs : s.vertices.card = n + 1) :
    C(LabeledSimplexCoordinates Γ s,c.pt.V) :=
  c.inr.hom.hom.comp
    ((SigmaOrbitCells.inclusion _ (chartCellOrbit n s hs)).toContinuousMap.comp
      (chartCellLift n s hs))

/-- The cocone equation gives exact agreement on the full chart boundary. -/
theorem attachmentChartMap_boundary (n : ℕ)
    (c : PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom)
    (s : LabeledOrbitSimplex Γ) (hs : s.vertices.card = n + 1)
    (w : LabeledSimplexCoordinates Γ s) (hw : w ∈ chartBoundary s) :
    attachmentChartMap n c s hs w = c.inl.hom
      ⟨chart s w, by
        have he : s.vertices.card - 1 = n := by omega
        exact he ▸ labeledChartBoundary_mem_skeletal s w hw⟩ := by
  obtain ⟨b,hb⟩ := chartCellLift_exists_boundary n s hs w hw
  have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom c.condition)
    (⟨chartCellOrbit n s hs,b⟩ : SigmaOrbitCells
      (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.diskBoundary.{u} n))
  change c.inl.hom (labeledCellBoundary _ b) =
    c.inr.hom ⟨chartCellOrbit n s hs, OrbitCell.boundaryInclusion _ n b⟩ at h
  have he := chartCellLift_characteristic n s hs w
  have hx : labeledCellBoundary (chartCellOrbit n s hs) b =
      (⟨chart s w, by
        have hn : s.vertices.card - 1 = n := by omega
        exact hn ▸ labeledChartBoundary_mem_skeletal s w hw⟩ : SkeletalSpace (Γ := Γ) n) := by
    apply Subtype.ext
    change labeledCellCharacteristic _ (OrbitCell.boundaryInclusion _ n b) = chart s w
    rw [hb]
    exact he
  calc
    attachmentChartMap n c s hs w =
        c.inr.hom ⟨chartCellOrbit n s hs, OrbitCell.boundaryInclusion _ n b⟩ :=
      congrArg (fun z => c.inr.hom ⟨chartCellOrbit n s hs,z⟩) hb.symm
    _ = c.inl.hom (labeledCellBoundary (chartCellOrbit n s hs) b) := h.symm
    _ = _ := congrArg (fun z => c.inl.hom z) hx

/-- Every disk point whose image is in the old skeleton comes from the actual sphere. -/
theorem labeledDiskSum_exists_boundary (n : ℕ)
    (p : SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.disk.{u} n))
    (hp : (labeledDiskSum n p).val ∈ skeletalCarrier n) :
    ∃ b : SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n))
        (TopCat.diskBoundary.{u} n), labeledSphereSum n b = p := by
  rcases p with ⟨q,⟨a,d⟩⟩
  induction a using QuotientGroup.induction_on with
  | H g =>
    let s := (cellRepresentative q).val
    let w := (representativeDiskHomeomorph q).symm d.down
    have hw : chart s w ∈ skeletalCarrier n := by
      have h := skeletalCarrier_smul n g⁻¹ hp
      change g⁻¹ • (g • chart s w) ∈ skeletalCarrier n at h
      simpa using h
    have hwb : w ∈ chartBoundary s := by
      apply (labeledChart_boundary_iff_skeletal s (cellRepresentative_nonempty q) w).mpr
      have hc : s.vertices.card - 1 = n := by
        rw [(cellRepresentative q).property, Nat.add_sub_cancel]
      exact hc.symm ▸ hw
    have hd : d.down.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      have h := (representativeDiskHomeomorph_boundary q w).mp hwb
      simpa [w] using h
    exact ⟨⟨q,(QuotientGroup.mk g,ULift.up ⟨d.down.val,hd⟩)⟩,rfl⟩

/-- The topological descended map supplied by the whole-chart gluing theorem. -/
def attachmentContinuousDesc (n : ℕ)
    (c : PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom) :
    C(SkeletalSpace (Γ := Γ) (n + 1),c.pt.V) :=
  ⟨skeletalGlue n c.inl.hom.hom (attachmentChartMap n c),
    continuous_skeletalGlue n c.inl.hom.hom (attachmentChartMap n c)
      (attachmentChartMap_boundary n c)⟩

theorem attachmentContinuousDesc_old (n : ℕ)
    (c : PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom)
    (x : SkeletalSpace (Γ := Γ) n) :
    attachmentContinuousDesc n c (skeletalMap (Nat.le_succ n) x) = c.inl.hom x :=
  skeletalGlue_old n c.inl.hom.hom (attachmentChartMap n c) x

/-- The descended map recovers every point of every actual orbit disk. -/
theorem attachmentContinuousDesc_disk (n : ℕ)
    (c : PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom)
    (p : SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.disk.{u} n)) :
    attachmentContinuousDesc n c (labeledDiskSum n p) = c.inr.hom p := by
  classical
  by_cases hp : (labeledDiskSum n p).val ∈ skeletalCarrier n
  · obtain ⟨b,hb⟩ := labeledDiskSum_exists_boundary n p hp
    have he := congrArg (fun f => f b) (labeledAttachment_square (Γ := Γ) n)
    change skeletalMap (Nat.le_succ n) (labeledBoundarySum n b) =
      labeledDiskSum n (labeledSphereSum n b) at he
    rw [hb] at he
    rw [← he, attachmentContinuousDesc_old]
    have h := ConcreteCategory.congr_hom (congrArg Action.Hom.hom c.condition) b
    change c.inl.hom (labeledBoundarySum n b) = c.inr.hom (labeledSphereSum n b) at h
    simpa only [hb] using h
  · let x := (labeledDiskSum n p).val
    let s := supportSimplex x
    have hs : s.vertices.card = n + 1 := by
      have h := (labeledDiskSum n p).property
      change s.vertices.card ≤ n + 1 at h
      change ¬s.vertices.card ≤ n at hp
      omega
    let w : LabeledSimplexCoordinates Γ s := ⟨x.val,mem_coordinates_supportSimplex x⟩
    let p' : SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.disk.{u} n) :=
      ⟨chartCellOrbit n s hs,chartCellLift n s hs w⟩
    have hx : labeledDiskSum n p' = labeledDiskSum n p := by
      apply Subtype.ext
      exact chartCellLift_characteristic n s hs w
    have hp' : (labeledDiskSum n p').val ∉ skeletalCarrier n := by rw [hx]; exact hp
    have he : p' = p := labeledDiskSum_injective_interior n hp' hp hx
    have hg := skeletalGlue_chart n c.inl.hom.hom (attachmentChartMap n c)
      (attachmentChartMap_boundary n c) s hs w
    change attachmentContinuousDesc n c (labeledDiskSum n p) = c.inr.hom p' at hg
    simpa only [he] using hg
end BC4lean.ProperActions
