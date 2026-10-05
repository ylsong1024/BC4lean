import BC4lean.LabeledAllowedCellOrbits
import BC4lean.LabeledCellMaps
import BC4lean.LabeledAllowedSkeletalColimit

/-! # Genuine orbit disks in an invariant face subcomplex -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open LabeledOrbitSimplex LabeledOrbitRealization
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]
variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

/-- The finite stabilizer of an actual allowed simplex orbit. -/
def allowedCellIsotropy {n : ℕ} (q : AllowedCellOrbit A n) : FiniteIsotropy Γ :=
  labeledCellIsotropy q.val

include hA in
/-- Every point in an allowed orbit disk has support in the same face family. -/
theorem labeledCellCharacteristic_mem_allowed {n : ℕ} (q : AllowedCellOrbit A n)
    (p : OrbitCell (cellStabilizer q.val) (TopCat.disk.{u} n)) :
    supportSimplex (labeledCellCharacteristic q.val p) ∈ A := by
  rcases p with ⟨a,d⟩
  induction a using QuotientGroup.induction_on with
  | H g =>
    let s := (cellRepresentative q.val).val
    let w := (representativeDiskHomeomorph q.val).symm d.down
    change supportSimplex (g • chart s w) ∈ A
    rw [supportSimplex_smul]
    apply (Fact.out : ∀ g s, s ∈ A → g • s ∈ A) g
    exact (allowedChart A hA s q.property w).property

/-- The actual characteristic disk map into the allowed next skeleton. -/
def allowedCellDisk {n : ℕ} (q : AllowedCellOrbit A n) :
    EquivariantMap Γ (OrbitCell (cellStabilizer q.val) (TopCat.disk.{u} n))
      (allowedSkeletalCarrier A (n + 1)) where
  toFun p := ⟨⟨labeledCellCharacteristic q.val p,
    labeledCellCharacteristic_mem_allowed A hA q p⟩, labeledCellCharacteristic_mem q.val p⟩
  continuous_toFun := ((labeledCellCharacteristic q.val).continuous_toFun.subtype_mk _).subtype_mk _
  map_smul' g p := Subtype.ext (Subtype.ext ((labeledCellCharacteristic q.val).map_smul g p))

/-- The actual sphere map into the allowed preceding skeleton. -/
def allowedCellBoundary {n : ℕ} (q : AllowedCellOrbit A n) :
    EquivariantMap Γ (OrbitCell (cellStabilizer q.val) (TopCat.diskBoundary.{u} n))
      (allowedSkeletalCarrier A n) where
  toFun p := ⟨⟨labeledCellCharacteristic q.val (OrbitCell.boundaryInclusion _ n p),
    labeledCellCharacteristic_mem_allowed A hA q (OrbitCell.boundaryInclusion _ n p)⟩,
    labeledCellBoundary_mem q.val p⟩
  continuous_toFun := (((labeledCellCharacteristic q.val).continuous_toFun.comp
    (OrbitCell.boundaryInclusion _ n).continuous_toFun).subtype_mk _).subtype_mk _
  map_smul' g p := by
    apply Subtype.ext
    apply Subtype.ext
    change labeledCellCharacteristic q.val (OrbitCell.boundaryInclusion _ n (g • p)) =
      g • labeledCellCharacteristic q.val (OrbitCell.boundaryInclusion _ n p)
    rw [(OrbitCell.boundaryInclusion _ n).map_smul,
      (labeledCellCharacteristic q.val).map_smul]

end BC4lean.ProperActions
