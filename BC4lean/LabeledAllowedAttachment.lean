import BC4lean.LabeledAllowedCellMaps
import BC4lean.OrbitCellCoproduct

/-! # Actual orbit-disk attaching cocone of an invariant face family -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open CategoryTheory CategoryTheory.Limits LabeledOrbitSimplex LabeledOrbitRealization
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]
variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

def allowedBoundarySum (n : ℕ) :
    EquivariantMap Γ (SigmaOrbitCells (allowedCellIsotropy A (n := n))
      (TopCat.diskBoundary.{u} n)) (allowedSkeletalCarrier A n) :=
  SigmaOrbitCells.fold _ (fun q => allowedCellBoundary A hA q)

def allowedDiskSum (n : ℕ) :
    EquivariantMap Γ (SigmaOrbitCells (allowedCellIsotropy A (n := n))
      (TopCat.disk.{u} n)) (allowedSkeletalCarrier A (n + 1)) :=
  SigmaOrbitCells.fold _ (fun q => allowedCellDisk A hA q)

def allowedSphereSum (n : ℕ) :
    EquivariantMap Γ (SigmaOrbitCells (allowedCellIsotropy A (n := n))
      (TopCat.diskBoundary.{u} n))
      (SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.disk.{u} n)) :=
  SigmaOrbitCells.map _ (TopCat.diskBoundaryInclusion n).hom

theorem allowedAttachment_square (n : ℕ) :
    (allowedSkeletalMap A (Nat.le_succ n)).comp (allowedBoundarySum A hA n) =
      (allowedDiskSum A hA n).comp (allowedSphereSum A n) := by
  ext p
  rfl

def allowedAttachmentCocone (n : ℕ) :
    PushoutCocone (allowedBoundarySum A hA n).toActionHom
      (allowedSphereSum A n).toActionHom :=
  PushoutCocone.mk (allowedSkeletalMap A (Nat.le_succ n)).toActionHom
    (allowedDiskSum A hA n).toActionHom (by
      have h := congrArg EquivariantMap.toActionHom (allowedAttachment_square A hA n)
      simpa only [EquivariantMap.toActionHom_comp] using h)

end BC4lean.ProperActions
