import BC4lean.LabeledCellMaps
import BC4lean.OrbitCellCoproduct

/-! # The actual coproduct orbit-disk skeletal attachment square -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open CategoryTheory CategoryTheory.Limits LabeledOrbitSimplex LabeledOrbitRealization

/-- Coproduct of all finite-isotropy sphere maps in a fixed dimension. -/
def labeledBoundarySum (n : ℕ) :
    EquivariantMap Γ (SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n))
      (TopCat.diskBoundary.{u} n)) (SkeletalSpace (Γ := Γ) n) :=
  SigmaOrbitCells.fold _ (fun q => labeledCellBoundary q)

/-- Coproduct of all finite-isotropy characteristic disk maps. -/
def labeledDiskSum (n : ℕ) :
    EquivariantMap Γ (SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n))
      (TopCat.disk.{u} n)) (SkeletalSpace (Γ := Γ) (n + 1)) :=
  SigmaOrbitCells.fold _ (fun q => labeledCellDisk q)

/-- Coproduct of actual unit-sphere inclusions into unit disks. -/
def labeledSphereSum (n : ℕ) :
    EquivariantMap Γ (SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n))
      (TopCat.diskBoundary.{u} n))
      (SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.disk.{u} n)) :=
  SigmaOrbitCells.map _ (TopCat.diskBoundaryInclusion n).hom

/-- The disk/sphere coproduct maps agree on their full attaching locus. -/
theorem labeledAttachment_square (n : ℕ) :
    (skeletalMap (Γ := Γ) (Nat.le_succ n)).comp (labeledBoundarySum (Γ := Γ) n) =
      (labeledDiskSum (Γ := Γ) n).comp (labeledSphereSum (Γ := Γ) n) := by
  ext p
  exact congrArg Subtype.val (congrArg (fun f => f p.2) (labeledCell_square p.1))

/-- The actual topological-action cocone for the skeletal attachment. -/
def labeledAttachmentCocone (n : ℕ) :
    PushoutCocone (labeledBoundarySum (Γ := Γ) n).toActionHom
      (labeledSphereSum (Γ := Γ) n).toActionHom :=
  PushoutCocone.mk (skeletalMap (Γ := Γ) (Nat.le_succ n)).toActionHom
    (labeledDiskSum (Γ := Γ) n).toActionHom (by
      have h := congrArg EquivariantMap.toActionHom (labeledAttachment_square (Γ := Γ) n)
      simpa only [EquivariantMap.toActionHom_comp] using h)

end BC4lean.ProperActions
