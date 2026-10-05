import BC4lean.LabeledSimplexDisks
import BC4lean.LabeledOrbitRealizationAction
import BC4lean.OrbitCellMaps
import BC4lean.LabeledSkeletalAction

/-! # Genuine orbit-disk characteristic maps for labeled simplices -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- Pull a translated simplex chart back to its chosen representative. The
coordinate map is continuous and retains all face identifications. -/
def labeledChartTransport (g : Γ) (s t : LabeledOrbitSimplex Γ) (he : g • s = t) :
    C(LabeledSimplexCoordinates Γ t, LabeledSimplexCoordinates Γ s) := by
  have ht : t.translate g⁻¹ = s := by
    change g⁻¹ • t = s
    rw [← he]
    simp
  let e := Homeomorph.setCongr (congrArg (LabeledSimplexCoordinates Γ) ht)
  exact (⟨e, e.continuous⟩ : C(_, _)).comp
    ⟨LabeledOrbitRealization.translateCoordinates g⁻¹ t,
      LabeledOrbitRealization.continuous_translateCoordinates g⁻¹ t⟩

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- Translating the pulled-back chart recovers the original realization point. -/
theorem labeledChartTransport_chart (g : Γ) (s t : LabeledOrbitSimplex Γ)
    (he : g • s = t) (w : LabeledSimplexCoordinates Γ t) :
    g • LabeledOrbitRealization.chart s (labeledChartTransport g s t he w) =
      LabeledOrbitRealization.chart t w := by
  apply Subtype.ext
  funext v
  change (labeledChartTransport g s t he w).val (g⁻¹ • v) = w.val v
  change w.val ((g⁻¹)⁻¹ • (g⁻¹ • v)) = w.val v
  simp

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- Simplex stabilizers fix every point of the whole chart. -/
theorem labeledChart_fixed (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) :
    ∀ h : MulAction.stabilizer Γ s,
      (h : Γ) • LabeledOrbitRealization.chart s w = LabeledOrbitRealization.chart s w := by
  apply (LabeledOrbitRealization.fixed_iff_support_fixed (MulAction.stabilizer Γ s)
    (LabeledOrbitRealization.chart s w)).mpr
  intro v hv h
  have hvs : v ∈ s.vertices := by
    by_contra he
    exact hv (w.property.2.1 v he)
  exact s.fixes_vertex_of_stabilizes
    ((s.stabilizes_iff_smul_eq h.val).mpr h.property) hvs

/-- The full chart is a continuous family of stabilizer-fixed points. -/
def labeledChartFixed (s : LabeledOrbitSimplex Γ) :
    C(LabeledSimplexCoordinates Γ s,
      FixedPointSpace (MulAction.stabilizer Γ s) (LabeledOrbitRealization Γ)) :=
  ⟨fun w => ⟨LabeledOrbitRealization.chart s w, labeledChart_fixed s w⟩,
    (LabeledOrbitRealization.continuous_chart s).subtype_mk _⟩

/-- Choose the proved disk-pair homeomorphism of a nonempty labeled simplex. -/
def labeledDiskHomeomorph (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    LabeledSimplexCoordinates Γ s ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (s.vertices.card - 1))) 1 :=
  Classical.choose (exists_labeledSimplexDiskHomeomorph s hne)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem labeledDiskHomeomorph_boundary (s : LabeledOrbitSimplex Γ)
    (hne : s.vertices.Nonempty) (w : LabeledSimplexCoordinates Γ s) :
    w ∈ LabeledOrbitRealization.chartBoundary s ↔
      (labeledDiskHomeomorph s hne w).val ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (s.vertices.card - 1))) 1 :=
  Classical.choose_spec (exists_labeledSimplexDiskHomeomorph s hne) w

/-- The fixed-point slice of the orbit-disk map is the actual simplex chart. -/
def labeledDiskFixed (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    C(TopCat.disk.{u} (s.vertices.card - 1),
      FixedPointSpace (MulAction.stabilizer Γ s) (LabeledOrbitRealization Γ)) :=
  (labeledChartFixed s).comp
    ((⟨(labeledDiskHomeomorph s hne).symm, (labeledDiskHomeomorph s hne).symm.continuous⟩ : C(_, _)).comp
      ⟨Homeomorph.ulift, Homeomorph.ulift.continuous⟩)

/-- Actual equivariant characteristic map of a finite-isotropy orbit disk. -/
def labeledOrbitDisk (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    EquivariantMap Γ (OrbitCell (MulAction.stabilizer Γ s)
      (TopCat.disk.{u} (s.vertices.card - 1))) (LabeledOrbitRealization Γ) :=
  cellFromFixed (MulAction.stabilizer Γ s) (labeledDiskFixed s hne)

@[simp] theorem labeledOrbitDisk_mk (s : LabeledOrbitSimplex Γ)
    (hne : s.vertices.Nonempty) (g : Γ) (d : TopCat.disk.{u} (s.vertices.card - 1)) :
    labeledOrbitDisk s hne (QuotientGroup.mk g, d) =
      g • LabeledOrbitRealization.chart s ((labeledDiskHomeomorph s hne).symm d.down) := rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The entire simplex chart belongs to its dimension stage. -/
theorem labeledChart_mem_skeletal (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) :
    LabeledOrbitRealization.chart s w ∈ LabeledOrbitRealization.skeletalCarrier s.vertices.card :=
  (LabeledOrbitRealization.mem_skeletalCarrier_iff _ _).mpr ⟨s, le_rfl, w.property⟩

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The full face boundary lies in the preceding skeleton. -/
theorem labeledChartBoundary_mem_skeletal (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (hw : w ∈ LabeledOrbitRealization.chartBoundary s) :
    LabeledOrbitRealization.chart s w ∈
      LabeledOrbitRealization.skeletalCarrier (s.vertices.card - 1) := by
  classical
  let : DecidableEq (LabeledOrbitVertex Γ) :=
    LabeledOrbitRealization.instDecidableEqLabeledOrbitVertex
  obtain ⟨v,hv,hz⟩ := hw
  apply (LabeledOrbitRealization.mem_skeletalCarrier_iff _ _).mpr
  refine ⟨_, ?_, LabeledOrbitRealization.mem_erased_face s w v hz⟩
  dsimp only [LabeledOrbitSimplex.ofSubset]
  rw [Finset.card_erase_of_mem hv]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- Interior barycentric coordinates recover exactly the original simplex. -/
theorem supportSimplex_chart_eq_iff (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) :
    LabeledOrbitRealization.supportSimplex (LabeledOrbitRealization.chart s w) = s ↔
      ∀ v ∈ s.vertices, w.val v ≠ 0 := by
  classical
  constructor
  · intro he v hv
    change (LabeledOrbitRealization.chart s w).val v ≠ 0
    apply (LabeledOrbitRealization.mem_supportSimplex (LabeledOrbitRealization.chart s w) v).mp
    rw [he]
    exact hv
  · intro hw
    apply LabeledOrbitSimplex.ext
    ext v
    rw [LabeledOrbitRealization.mem_supportSimplex]
    constructor
    · intro hv
      by_contra he
      exact hv (w.property.2.1 v he)
    · exact hw v

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- A chart meets the preceding skeleton precisely along its full face boundary. -/
theorem labeledChart_boundary_iff_skeletal (s : LabeledOrbitSimplex Γ)
    (hne : s.vertices.Nonempty) (w : LabeledSimplexCoordinates Γ s) :
    w ∈ LabeledOrbitRealization.chartBoundary s ↔
      LabeledOrbitRealization.chart s w ∈
        LabeledOrbitRealization.skeletalCarrier (s.vertices.card - 1) := by
  constructor
  · exact labeledChartBoundary_mem_skeletal s w
  · intro hs
    by_contra hn
    have hw : ∀ v ∈ s.vertices, w.val v ≠ 0 := by
      intro v hv hz
      exact hn ⟨v,hv,hz⟩
    have he := (supportSimplex_chart_eq_iff s w).mpr hw
    change (LabeledOrbitRealization.supportSimplex
      (LabeledOrbitRealization.chart s w)).vertices.card ≤ s.vertices.card - 1 at hs
    rw [he] at hs
    have hp := Finset.card_pos.mpr hne
    omega

/-- The orbit-disk characteristic map lands in the intended skeletal stage. -/
theorem labeledOrbitDisk_mem_skeletal (s : LabeledOrbitSimplex Γ)
    (hne : s.vertices.Nonempty) (p : OrbitCell (MulAction.stabilizer Γ s)
      (TopCat.disk.{u} (s.vertices.card - 1))) :
    labeledOrbitDisk s hne p ∈ LabeledOrbitRealization.skeletalCarrier s.vertices.card := by
  rcases p with ⟨q,d⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    exact LabeledOrbitRealization.skeletalCarrier_smul _ g
      (labeledChart_mem_skeletal s ((labeledDiskHomeomorph s hne).symm d.down))

/-- The boundary map lands in the preceding skeleton. -/
theorem labeledOrbitBoundary_mem_skeletal (s : LabeledOrbitSimplex Γ)
    (hne : s.vertices.Nonempty) (p : OrbitCell (MulAction.stabilizer Γ s)
      (TopCat.diskBoundary.{u} (s.vertices.card - 1))) :
    labeledOrbitDisk s hne (OrbitCell.boundaryInclusion _ _ p) ∈
      LabeledOrbitRealization.skeletalCarrier (s.vertices.card - 1) := by
  rcases p with ⟨q,d⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    change g • LabeledOrbitRealization.chart s
      ((labeledDiskHomeomorph s hne).symm ⟨d.down.val, le_of_eq d.down.property⟩) ∈
        LabeledOrbitRealization.skeletalCarrier (s.vertices.card - 1)
    apply LabeledOrbitRealization.skeletalCarrier_smul _ g
    apply labeledChartBoundary_mem_skeletal
    apply (labeledDiskHomeomorph_boundary s hne _).mpr
    rw [(labeledDiskHomeomorph s hne).apply_symm_apply]
    exact d.down.property

/-- Distinct interior points of a single orbit disk remain distinct. Boundary
identifications are the only identifications inside this characteristic map. -/
theorem labeledOrbitDisk_injective_interior (s : LabeledOrbitSimplex Γ)
    (hne : s.vertices.Nonempty) :
    Set.InjOn (labeledOrbitDisk s hne)
      {p | labeledOrbitDisk s hne p ∉
        LabeledOrbitRealization.skeletalCarrier (s.vertices.card - 1)} := by
  classical
  rintro ⟨q,d⟩ hx ⟨q',d'⟩ hy he
  induction q using QuotientGroup.induction_on with | H g =>
    induction q' using QuotientGroup.induction_on with | H h =>
      let w := (labeledDiskHomeomorph s hne).symm d.down
      let w' := (labeledDiskHomeomorph s hne).symm d'.down
      have hw : ∀ v ∈ s.vertices, w.val v ≠ 0 := by
        intro v hv hz
        exact hx (LabeledOrbitRealization.skeletalCarrier_smul _ g
          (labeledChartBoundary_mem_skeletal s w ⟨v,hv,hz⟩))
      have hw' : ∀ v ∈ s.vertices, w'.val v ≠ 0 := by
        intro v hv hz
        exact hy (LabeledOrbitRealization.skeletalCarrier_smul _ h
          (labeledChartBoundary_mem_skeletal s w' ⟨v,hv,hz⟩))
      have hs := congrArg LabeledOrbitRealization.supportSimplex he
      have hsw := (supportSimplex_chart_eq_iff s w).mpr hw
      have hsw' := (supportSimplex_chart_eq_iff s w').mpr hw'
      change LabeledOrbitRealization.supportSimplex (g • LabeledOrbitRealization.chart s w) =
        LabeledOrbitRealization.supportSimplex (h • LabeledOrbitRealization.chart s w') at hs
      rw [LabeledOrbitRealization.supportSimplex_smul,
        LabeledOrbitRealization.supportSimplex_smul, hsw, hsw'] at hs
      have hstab : g⁻¹ * h ∈ MulAction.stabilizer Γ s := by
        change (g⁻¹ * h) • s = s
        have hi := congrArg (fun t : LabeledOrbitSimplex Γ => g⁻¹ • t) hs
        simpa [mul_smul] using hi.symm
      have hq : (QuotientGroup.mk g : Γ ⧸ MulAction.stabilizer Γ s) =
          QuotientGroup.mk h := QuotientGroup.eq.mpr hstab
      have hfix : (g⁻¹ * h) • LabeledOrbitRealization.chart s w' =
          LabeledOrbitRealization.chart s w' :=
        (labeledChartFixed s w').property ⟨g⁻¹ * h,hstab⟩
      have hc : LabeledOrbitRealization.chart s w = LabeledOrbitRealization.chart s w' := by
        have hi := congrArg (fun x : LabeledOrbitRealization Γ => g⁻¹ • x) he
        change g⁻¹ • (g • LabeledOrbitRealization.chart s w) =
          g⁻¹ • (h • LabeledOrbitRealization.chart s w') at hi
        simpa only [← mul_smul, inv_mul_cancel, one_smul, hfix] using hi
      have hew : w = w' := (LabeledOrbitRealization.chart_isClosedEmbedding s).injective hc
      have hd : d = d' := by
        apply ULift.ext
        exact (labeledDiskHomeomorph s hne).symm.injective hew
      exact Prod.ext hq hd

/-- A genuine orbit-disk map into the next skeleton. -/
def labeledOrbitDiskStage (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    EquivariantMap Γ (OrbitCell (MulAction.stabilizer Γ s)
      (TopCat.disk.{u} (s.vertices.card - 1)))
      (LabeledOrbitRealization.SkeletalSpace (Γ := Γ) s.vertices.card) where
  toFun p := ⟨labeledOrbitDisk s hne p, labeledOrbitDisk_mem_skeletal s hne p⟩
  continuous_toFun := (labeledOrbitDisk s hne).continuous.subtype_mk _
  map_smul' g p := Subtype.ext ((labeledOrbitDisk s hne).map_smul g p)

/-- Its full orbit-sphere boundary maps into the preceding skeleton. -/
def labeledOrbitBoundaryStage (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    EquivariantMap Γ (OrbitCell (MulAction.stabilizer Γ s)
      (TopCat.diskBoundary.{u} (s.vertices.card - 1)))
      (LabeledOrbitRealization.SkeletalSpace (Γ := Γ) (s.vertices.card - 1)) where
  toFun p := ⟨labeledOrbitDisk s hne (OrbitCell.boundaryInclusion _ _ p),
    labeledOrbitBoundary_mem_skeletal s hne p⟩
  continuous_toFun := ((labeledOrbitDisk s hne).continuous.comp
    (OrbitCell.boundaryInclusion _ _).continuous).subtype_mk _
  map_smul' g p := Subtype.ext (by
    change labeledOrbitDisk s hne (OrbitCell.boundaryInclusion _ _ (g • p)) =
      g • labeledOrbitDisk s hne (OrbitCell.boundaryInclusion _ _ p)
    rw [(OrbitCell.boundaryInclusion _ _).map_smul, (labeledOrbitDisk s hne).map_smul])

/-- The orbit-disk and boundary characteristic maps form the actual skeletal square. -/
theorem labeledOrbitCell_square (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    (LabeledOrbitRealization.skeletalMap (Nat.sub_le s.vertices.card 1)).comp
      (labeledOrbitBoundaryStage s hne) =
    (labeledOrbitDiskStage s hne).comp (OrbitCell.boundaryInclusion _ _) := by
  ext p
  rfl

end BC4lean.ProperActions
