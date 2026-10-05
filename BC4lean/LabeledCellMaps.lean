import BC4lean.LabeledOrbitCells
import BC4lean.LabeledSimplexOrbits

/-! # Dimension-indexed orbit-cell maps for the skeletal attachment square -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open LabeledOrbitSimplex LabeledOrbitRealization

/-- The actual finite stabilizer subgroup of a chosen simplex representative. -/
def labeledCellIsotropy {n : ℕ} (q : CellOrbit Γ n) : FiniteIsotropy Γ :=
  ⟨cellStabilizer q, inferInstance⟩

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The disk pair of a representative, indexed by its actual cell dimension. -/
theorem exists_representativeDiskHomeomorph {n : ℕ} (q : CellOrbit Γ n) :
    ∃ e : LabeledSimplexCoordinates Γ (cellRepresentative q).val ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ w, w ∈ chartBoundary (cellRepresentative q).val ↔
        (e w).val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  have h := exists_labeledSimplexDiskHomeomorph (cellRepresentative q).val
    (cellRepresentative_nonempty q)
  rw [(cellRepresentative q).property, Nat.add_sub_cancel] at h
  exact h

def representativeDiskHomeomorph {n : ℕ} (q : CellOrbit Γ n) :
    LabeledSimplexCoordinates Γ (cellRepresentative q).val ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  Classical.choose (exists_representativeDiskHomeomorph q)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem representativeDiskHomeomorph_boundary {n : ℕ} (q : CellOrbit Γ n)
    (w : LabeledSimplexCoordinates Γ (cellRepresentative q).val) :
    w ∈ chartBoundary (cellRepresentative q).val ↔
      (representativeDiskHomeomorph q w).val ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  Classical.choose_spec (exists_representativeDiskHomeomorph q) w

/-- A dimension-indexed representative chart as a fixed-point disk slice. -/
def representativeDiskFixed {n : ℕ} (q : CellOrbit Γ n) :
    C(TopCat.disk.{u} n, FixedPointSpace (cellStabilizer q) (LabeledOrbitRealization Γ)) :=
  (labeledChartFixed (cellRepresentative q).val).comp
    ((⟨(representativeDiskHomeomorph q).symm, (representativeDiskHomeomorph q).symm.continuous⟩ : C(_, _)).comp
      ⟨Homeomorph.ulift, Homeomorph.ulift.continuous⟩)

/-- The representative's orbit disk in the full realization. -/
def labeledCellCharacteristic {n : ℕ} (q : CellOrbit Γ n) :
    EquivariantMap Γ (OrbitCell (cellStabilizer q) (TopCat.disk.{u} n))
      (LabeledOrbitRealization Γ) :=
  cellFromFixed (cellStabilizer q) (representativeDiskFixed q)

@[simp] theorem labeledCellCharacteristic_mk {n : ℕ} (q : CellOrbit Γ n)
    (g : Γ) (d : TopCat.disk.{u} n) :
    labeledCellCharacteristic q (QuotientGroup.mk g, d) =
      g • chart (cellRepresentative q).val ((representativeDiskHomeomorph q).symm d.down) := rfl

theorem labeledCellCharacteristic_mem {n : ℕ} (q : CellOrbit Γ n)
    (p : OrbitCell (cellStabilizer q) (TopCat.disk.{u} n)) :
    labeledCellCharacteristic q p ∈ skeletalCarrier (n + 1) := by
  rcases p with ⟨a,d⟩
  induction a using QuotientGroup.induction_on with
  | H g =>
    apply skeletalCarrier_smul _ g
    exact (mem_skeletalCarrier_iff _ _).mpr
      ⟨(cellRepresentative q).val, (cellRepresentative q).property.le,
        ((representativeDiskHomeomorph q).symm d.down).property⟩

theorem labeledCellBoundary_mem {n : ℕ} (q : CellOrbit Γ n)
    (p : OrbitCell (cellStabilizer q) (TopCat.diskBoundary.{u} n)) :
    labeledCellCharacteristic q (OrbitCell.boundaryInclusion _ _ p) ∈ skeletalCarrier n := by
  rcases p with ⟨a,d⟩
  induction a using QuotientGroup.induction_on with
  | H g =>
    change g • chart (cellRepresentative q).val
      ((representativeDiskHomeomorph q).symm ⟨d.down.val, le_of_eq d.down.property⟩) ∈
        skeletalCarrier n
    apply skeletalCarrier_smul _ g
    have hw : (representativeDiskHomeomorph q).symm
        ⟨d.down.val, le_of_eq d.down.property⟩ ∈ chartBoundary (cellRepresentative q).val := by
      apply (representativeDiskHomeomorph_boundary q _).mpr
      rw [(representativeDiskHomeomorph q).apply_symm_apply]
      exact d.down.property
    have hm := labeledChartBoundary_mem_skeletal (cellRepresentative q).val _ hw
    simpa only [(cellRepresentative q).property, Nat.add_sub_cancel] using hm

/-- The representative's disk map into the next stage. -/
def labeledCellDisk {n : ℕ} (q : CellOrbit Γ n) :
    EquivariantMap Γ (OrbitCell (cellStabilizer q) (TopCat.disk.{u} n))
      (SkeletalSpace (Γ := Γ) (n + 1)) where
  toFun p := ⟨labeledCellCharacteristic q p, labeledCellCharacteristic_mem q p⟩
  continuous_toFun := (labeledCellCharacteristic q).continuous.subtype_mk _
  map_smul' g p := Subtype.ext ((labeledCellCharacteristic q).map_smul g p)

/-- The representative's sphere map into the preceding stage. -/
def labeledCellBoundary {n : ℕ} (q : CellOrbit Γ n) :
    EquivariantMap Γ (OrbitCell (cellStabilizer q) (TopCat.diskBoundary.{u} n))
      (SkeletalSpace (Γ := Γ) n) where
  toFun p := ⟨labeledCellCharacteristic q (OrbitCell.boundaryInclusion _ _ p),
    labeledCellBoundary_mem q p⟩
  continuous_toFun := ((labeledCellCharacteristic q).continuous.comp
    (OrbitCell.boundaryInclusion _ _).continuous).subtype_mk _
  map_smul' g p := Subtype.ext (by
    change labeledCellCharacteristic q (OrbitCell.boundaryInclusion _ _ (g • p)) =
      g • labeledCellCharacteristic q (OrbitCell.boundaryInclusion _ _ p)
    rw [(OrbitCell.boundaryInclusion _ _).map_smul, (labeledCellCharacteristic q).map_smul])

/-- Every indexed finite-isotropy disk is attached along its actual full sphere. -/
theorem labeledCell_square {n : ℕ} (q : CellOrbit Γ n) :
    (skeletalMap (Nat.le_succ n)).comp (labeledCellBoundary q) =
      (labeledCellDisk q).comp (OrbitCell.boundaryInclusion _ n) := by
  ext p
  rfl

end BC4lean.ProperActions
