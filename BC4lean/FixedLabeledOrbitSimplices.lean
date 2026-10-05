import BC4lean.LabeledOrbitSimplices
import Mathlib.Data.Finset.Lattice.Fold

/-! # Fixed labeled simplices and fresh fixed vertices

These are combinatorial extension lemmas. No topology or realization is constructed here.
-/
namespace BC4lean.ProperActions.LabeledOrbitSimplex

open scoped Classical

variable {Γ : Type*} [Group Γ]

/-- A simplex is fixed exactly when each of its vertices is fixed. -/
theorem smul_eq_iff_vertices (s : LabeledOrbitSimplex Γ) (g : Γ) :
    g • s = s ↔ ∀ v ∈ s.vertices, g • v = v := by
  classical
  constructor
  · intro hg v hv
    exact s.fixes_vertex_of_stabilizes ((s.stabilizes_iff_smul_eq g).mpr hg) hv
  · intro hg
    apply ext
    apply Finset.ext
    intro v
    change v ∈ s.vertices.image (fun v => g • v) ↔ v ∈ s.vertices
    constructor
    · intro hv
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
      rw [hg w hw] at he
      simpa [← he] using hw
    · intro hv
      exact Finset.mem_image.mpr ⟨v, hv, hg v hv⟩

/-- Fixedness under a subgroup is pointwise fixedness of all vertices. -/
theorem subgroup_fixed_iff_vertices (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ) :
    (∀ h : H, (h : Γ) • s = s) ↔
      ∀ v ∈ s.vertices, ∀ h : H, (h : Γ) • v = v := by
  constructor
  · intro hs v hv h
    exact (s.smul_eq_iff_vertices h).mp (hs h) v hv
  · intro hs h
    exact (s.smul_eq_iff_vertices h).mpr (fun v hv => hs v hv h)

/-- A label strictly beyond every label occurring in a finite simplex. -/
def freshLabel (s : LabeledOrbitSimplex Γ) : ℕ := s.vertices.sup Prod.fst + 1

theorem label_lt_freshLabel (s : LabeledOrbitSimplex Γ)
    {v : LabeledOrbitVertex Γ} (hv : v ∈ s.vertices) : v.1 < s.freshLabel :=
  lt_of_le_of_lt (Finset.le_sup hv) (Nat.lt_succ_self _)

/-- Adjoining a vertex with a fresh factor label preserves admissibility. -/
noncomputable def adjoinVertex (s : LabeledOrbitSimplex Γ) (v : LabeledOrbitVertex Γ)
    (hf : ∀ w ∈ s.vertices, w.1 ≠ v.1) : LabeledOrbitSimplex Γ := by
  classical
  refine ⟨insert v s.vertices, ?_⟩
  intro x hxinsert y hyinsert he
  rcases Finset.mem_insert.mp hxinsert with rfl | hxold
  · rcases Finset.mem_insert.mp hyinsert with rfl | hyold
    · rfl
    · exact False.elim (hf y hyold he.symm)
  · rcases Finset.mem_insert.mp hyinsert with rfl | hyold
    · exact False.elim (hf x hxold he)
    · exact s.labels_injective hxold hyold he

/-- A finite subgroup supplies a fixed vertex at the fresh label. -/
def freshFixedVertex (H : Subgroup Γ) [Finite H] (s : LabeledOrbitSimplex Γ) :
    LabeledOrbitVertex Γ := fixedOrbitVertex Γ H s.freshLabel

theorem freshFixedVertex_label_new (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) {v : LabeledOrbitVertex Γ} (hv : v ∈ s.vertices) :
    v.1 ≠ (freshFixedVertex H s).1 :=
  ne_of_lt (s.label_lt_freshLabel hv)

theorem freshFixedVertex_not_mem (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) : freshFixedVertex H s ∉ s.vertices := by
  intro hv
  exact s.freshFixedVertex_label_new H hv rfl

theorem freshFixedVertex_fixed (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (h : H) :
    (h : Γ) • freshFixedVertex H s = freshFixedVertex H s :=
  fixedOrbitVertex_fixed Γ H s.freshLabel h

/-- The finite simplex obtained by adjoining the fresh subgroup-fixed vertex. -/
noncomputable def fixedExtension (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) : LabeledOrbitSimplex Γ :=
  s.adjoinVertex (freshFixedVertex H s) (fun _ hv => s.freshFixedVertex_label_new H hv)

@[simp] theorem fixedExtension_vertices (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) :
    (s.fixedExtension H).vertices = insert (freshFixedVertex H s) s.vertices := rfl

theorem vertices_subset_fixedExtension (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) : s.vertices ⊆ (s.fixedExtension H).vertices := by
  classical
  exact Finset.subset_insert _ _

theorem freshFixedVertex_mem_fixedExtension (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) : freshFixedVertex H s ∈ (s.fixedExtension H).vertices := by
  classical
  exact Finset.mem_insert_self _ _

/-- Adjoining the fresh vertex preserves subgroup fixedness of the whole simplex. -/
theorem fixedExtension_fixed (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (hs : ∀ h : H, (h : Γ) • s = s) :
    ∀ h : H, (h : Γ) • s.fixedExtension H = s.fixedExtension H := by
  classical
  intro h
  apply ((s.fixedExtension H).smul_eq_iff_vertices h).mpr
  intro v hvinsert
  rcases Finset.mem_insert.mp hvinsert with rfl | hvold
  · exact s.freshFixedVertex_fixed H h
  · exact (s.smul_eq_iff_vertices h).mp (hs h) v hvold

/-- Every finite fixed simplex has a strictly larger finite fixed extension. -/
theorem exists_fixed_extension (H : Subgroup Γ) [Finite H]
    (s : LabeledOrbitSimplex Γ) (hs : ∀ h : H, (h : Γ) • s = s) :
    ∃ (v : LabeledOrbitVertex Γ) (t : LabeledOrbitSimplex Γ),
      v ∉ s.vertices ∧ t.vertices = insert v s.vertices ∧
      (∀ h : H, (h : Γ) • v = v) ∧ (∀ h : H, (h : Γ) • t = t) :=
  ⟨freshFixedVertex H s, s.fixedExtension H, s.freshFixedVertex_not_mem H,
    s.fixedExtension_vertices H, s.freshFixedVertex_fixed H, s.fixedExtension_fixed H hs⟩

end BC4lean.ProperActions.LabeledOrbitSimplex
