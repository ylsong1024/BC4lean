import BC4lean.LabeledCellMaps

/-! # Continuous lifts of top-dimensional charts to their orbit disks -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open LabeledOrbitSimplex LabeledOrbitRealization

/-- The unique orbit index of a top-dimensional simplex. -/
def chartCellOrbit (n : ℕ) (s : LabeledOrbitSimplex Γ) (hs : s.vertices.card = n + 1) :
    CellOrbit Γ n := Quotient.mk _ (⟨s,hs⟩ : DimensionSimplex Γ n)

/-- A translate taking the chosen representative to the given simplex. -/
def chartCellTranslate (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s.vertices.card = n + 1) : Γ :=
  Classical.choose (exists_smul_cellRepresentative (⟨s,hs⟩ : DimensionSimplex Γ n))

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem chartCellTranslate_spec (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s.vertices.card = n + 1) :
    chartCellTranslate n s hs • (cellRepresentative (chartCellOrbit n s hs)).val = s :=
  congrArg Subtype.val (Classical.choose_spec
    (exists_smul_cellRepresentative (⟨s,hs⟩ : DimensionSimplex Γ n)))

/-- A simplex chart lifts continuously into one actual orbit disk. No choice of
representative varies with the point inside the chart. -/
def chartCellLift (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s.vertices.card = n + 1) :
    C(LabeledSimplexCoordinates Γ s,
      OrbitCell (cellStabilizer (chartCellOrbit n s hs)) (TopCat.disk.{u} n)) := by
  let q := chartCellOrbit n s hs
  let g := chartCellTranslate n s hs
  let t := labeledChartTransport g (cellRepresentative q).val s (chartCellTranslate_spec n s hs)
  let e := representativeDiskHomeomorph q
  let d : C(LabeledSimplexCoordinates Γ s, TopCat.disk.{u} n) :=
    (⟨Homeomorph.ulift.symm, Homeomorph.ulift.symm.continuous⟩ : C(_, _)).comp
      ((⟨e, e.continuous⟩ : C(_, _)).comp t)
  exact ⟨fun w => (QuotientGroup.mk g, d w), continuous_const.prodMk d.continuous⟩

/-- The orbit-disk characteristic map exactly recovers the entire chart,
including every boundary face. -/
theorem chartCellLift_characteristic (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s.vertices.card = n + 1) (w : LabeledSimplexCoordinates Γ s) :
    labeledCellCharacteristic (chartCellOrbit n s hs) (chartCellLift n s hs w) = chart s w := by
  change chartCellTranslate n s hs • chart (cellRepresentative (chartCellOrbit n s hs)).val
    ((representativeDiskHomeomorph (chartCellOrbit n s hs)).symm
      (representativeDiskHomeomorph (chartCellOrbit n s hs)
        (labeledChartTransport (chartCellTranslate n s hs)
          (cellRepresentative (chartCellOrbit n s hs)).val s
          (chartCellTranslate_spec n s hs) w))) = chart s w
  rw [(representativeDiskHomeomorph (chartCellOrbit n s hs)).symm_apply_apply]
  exact labeledChartTransport_chart _ _ _ _ w

end BC4lean.ProperActions
