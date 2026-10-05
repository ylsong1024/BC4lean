import BC4lean.FixedLabeledOrbitSimplices

/-! # Collision-free partial shifts for labeled joins

The partial shift at threshold k leaves labels below k unchanged and moves
all labels at least k one place to the right. Consecutive partial shifts
share an admissible finite carrier, as required for affine interpolation.
-/
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]

def partialShiftLabel (k n : ℕ) : ℕ := if n < k then n else n + 1

theorem partialShiftLabel_injective (k : ℕ) : Function.Injective (partialShiftLabel k) := by
  intro n m h
  unfold partialShiftLabel at h
  split_ifs at h <;> omega

def partialShiftVertex (k : ℕ) (v : LabeledOrbitVertex Γ) : LabeledOrbitVertex Γ :=
  (partialShiftLabel k v.1, v.2)

theorem partialShiftVertex_injective (k : ℕ) :
    Function.Injective (partialShiftVertex (Γ := Γ) k) := by
  intro v w h
  apply Prod.ext
  · exact partialShiftLabel_injective k (congrArg Prod.fst h)
  · simpa only [partialShiftVertex] using congrArg (fun z : LabeledOrbitVertex Γ => z.2) h

@[simp] theorem partialShiftVertex_smul (k : ℕ) (g : Γ) (v : LabeledOrbitVertex Γ) :
    partialShiftVertex k (g • v) = g • partialShiftVertex k v := rfl

namespace LabeledOrbitSimplex
noncomputable def partialShift (s : LabeledOrbitSimplex Γ) (k : ℕ) :
    LabeledOrbitSimplex Γ := by
  classical
  refine ⟨s.vertices.image (partialShiftVertex k), ?_⟩
  intro v hv w hw he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
  exact congrArg (partialShiftVertex k) (s.labels_injective ha hb
    (partialShiftLabel_injective k he))

/-- Consecutive partial shifts cannot place distinct vertices in one factor. -/
theorem consecutive_shift_label_eq (s : LabeledOrbitSimplex Γ) (k : ℕ)
    {v w : LabeledOrbitVertex Γ} (hv : v ∈ s.vertices) (hw : w ∈ s.vertices)
    (he : (partialShiftVertex (k+1) v).1 = (partialShiftVertex k w).1) :
    partialShiftVertex (k+1) v = partialShiftVertex k w := by
  have hl : v.1 = w.1 := by
    change partialShiftLabel (k+1) v.1 = partialShiftLabel k w.1 at he
    unfold partialShiftLabel at he
    split_ifs at he <;> omega
  have hvw := s.labels_injective hv hw hl
  apply Prod.ext he
  change v.2 = w.2
  exact congrArg (fun z : LabeledOrbitVertex Γ => z.2) hvw

/-- The union chart contains both endpoints of one shift interpolation. -/
noncomputable def shiftCarrier (s : LabeledOrbitSimplex Γ) (k : ℕ) :
    LabeledOrbitSimplex Γ := by
  classical
  refine ⟨(s.partialShift (k+1)).vertices ∪ (s.partialShift k).vertices, ?_⟩
  intro v hv w hw he
  rcases Finset.mem_union.mp hv with hv | hv <;>
    rcases Finset.mem_union.mp hw with hw | hw
  · exact (s.partialShift (k+1)).labels_injective hv hw he
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    exact s.consecutive_shift_label_eq k ha hb he
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    exact (s.consecutive_shift_label_eq k hb ha he.symm).symm
  · exact (s.partialShift k).labels_injective hv hw he

@[simp] theorem partialShift_zero_label (s : LabeledOrbitSimplex Γ)
    {v : LabeledOrbitVertex Γ} (hv : v ∈ (s.partialShift 0).vertices) : v.1 ≠ 0 := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
  simp [partialShiftVertex, partialShiftLabel]

theorem partialShift_eq_self (s : LabeledOrbitSimplex Γ) (k : ℕ)
    (hk : ∀ v ∈ s.vertices, v.1 < k) : s.partialShift k = s := by
  classical
  apply ext
  change s.vertices.image (partialShiftVertex k) = s.vertices
  calc
    s.vertices.image (partialShiftVertex k) = s.vertices.image id := by
      apply Finset.image_congr
      intro v hv
      apply Prod.ext
      · simp [partialShiftVertex, partialShiftLabel, hk v hv]
      · rfl
    _ = s.vertices := Finset.image_id

/-- Every chart is eventually unchanged as the shift threshold tends to infinity. -/
theorem partialShift_freshLabel (s : LabeledOrbitSimplex Γ) :
    s.partialShift s.freshLabel = s :=
  s.partialShift_eq_self _ (fun _ hv => s.label_lt_freshLabel hv)

/-- Relabeling preserves pointwise fixed vertices. -/
theorem partialShift_fixed (s : LabeledOrbitSimplex Γ) (k : ℕ) (g : Γ)
    (hs : g • s = s) : g • s.partialShift k = s.partialShift k := by
  classical
  apply ((s.partialShift k).smul_eq_iff_vertices g).mpr
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  rw [← partialShiftVertex_smul, (s.smul_eq_iff_vertices g).mp hs a ha]

/-- Both interpolation endpoints and their shared carrier remain fixed. -/
theorem shiftCarrier_fixed (s : LabeledOrbitSimplex Γ) (k : ℕ) (g : Γ)
    (hs : g • s = s) : g • s.shiftCarrier k = s.shiftCarrier k := by
  classical
  apply ((s.shiftCarrier k).smul_eq_iff_vertices g).mpr
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact ((s.partialShift (k+1)).smul_eq_iff_vertices g).mp
      (s.partialShift_fixed (k+1) g hs) v hv
  · exact ((s.partialShift k).smul_eq_iff_vertices g).mp
      (s.partialShift_fixed k g hs) v hv

end LabeledOrbitSimplex
end BC4lean.ProperActions

namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]

def partialUnshiftVertex (k : ℕ) (v : LabeledOrbitVertex Γ) : LabeledOrbitVertex Γ :=
  (if v.1 < k then v.1 else v.1 - 1, v.2)

@[simp] theorem partialUnshift_shift (k : ℕ) (v : LabeledOrbitVertex Γ) :
    partialUnshiftVertex k (partialShiftVertex k v) = v := by
  apply Prod.ext
  · simp only [partialUnshiftVertex, partialShiftVertex, partialShiftLabel]
    split_ifs <;> omega
  · rfl

theorem partialShift_not_gap (k : ℕ) (v : LabeledOrbitVertex Γ) :
    (partialShiftVertex k v).1 ≠ k := by
  simp only [partialShiftVertex, partialShiftLabel]
  split_ifs <;> omega

theorem partialShift_unshift (k : ℕ) (v : LabeledOrbitVertex Γ) (hv : v.1 ≠ k) :
    partialShiftVertex k (partialUnshiftVertex k v) = v := by
  apply Prod.ext
  · simp only [partialUnshiftVertex, partialShiftVertex, partialShiftLabel]
    split_ifs <;> omega
  · rfl

end BC4lean.ProperActions
