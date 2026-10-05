import BC4lean.LabeledAllowedAttachment
import BC4lean.LabeledCellChartLift
import BC4lean.LabeledCellInteriors

/-! # Actual chart lifts and uniqueness for allowed orbit disks -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open LabeledOrbitSimplex LabeledOrbitRealization
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]
variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

def allowedChartCellOrbit (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (ha : s ∈ A) (hs : s.vertices.card = n + 1) : AllowedCellOrbit A n :=
  ⟨chartCellOrbit n s hs, by
    apply (smul_mem_allowed_iff A (chartCellTranslate n s hs) _).mp
    rw [chartCellTranslate_spec]
    exact ha⟩

def allowedChartCellLift (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (ha : s ∈ A) (hs : s.vertices.card = n + 1) :
    C(LabeledSimplexCoordinates Γ s,
      OrbitCell (cellStabilizer (allowedChartCellOrbit A n s ha hs).val) (TopCat.disk.{u} n)) :=
  chartCellLift n s hs

theorem allowedChartCellLift_characteristic (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (ha : s ∈ A) (hs : s.vertices.card = n + 1) (w : LabeledSimplexCoordinates Γ s) :
    allowedDiskSum A hA n ⟨allowedChartCellOrbit A n s ha hs,allowedChartCellLift A n s ha hs w⟩ =
      boundedAllowedSkeletalChart A hA (n + 1) s ha (by omega) w := by
  apply Subtype.ext
  apply Subtype.ext
  exact chartCellLift_characteristic n s hs w

/-- Forgetting the allowed index preserves the full actual orbit-disk point. -/
def forgetAllowedDisk (n : ℕ)
    (p : SigmaOrbitCells (allowedCellIsotropy A (n := n)) (TopCat.disk.{u} n)) :
    SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n)) (TopCat.disk.{u} n) :=
  ⟨p.1.val,p.2⟩

omit [TopologicalSpace Γ] [DiscreteTopology Γ]
  [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)] in
theorem forgetAllowedDisk_injective (n : ℕ) : Function.Injective (forgetAllowedDisk A n) := by
  rintro ⟨⟨q,hq⟩,p⟩ ⟨⟨r,hr⟩,z⟩ he
  change (⟨q,p⟩ : SigmaOrbitCells (labeledCellIsotropy (Γ := Γ) (n := n)) _) = ⟨r,z⟩ at he
  have hqr : q = r := congrArg Sigma.fst he
  subst r
  have hp : p = z := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  subst z
  rfl

theorem allowedDiskSum_injective_interior (n : ℕ) :
    Set.InjOn (allowedDiskSum A hA n)
      {p | (allowedDiskSum A hA n p).val ∉ allowedSkeletalCarrier A n} := by
  intro p hp q hq he
  apply forgetAllowedDisk_injective A n
  apply labeledDiskSum_injective_interior n
  · exact hp
  · exact hq
  · exact congrArg (fun x => (⟨x.val.val,x.property⟩ : SkeletalSpace (Γ := Γ) (n + 1))) he

end BC4lean.ProperActions
