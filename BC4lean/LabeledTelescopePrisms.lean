import BC4lean.LabeledOrbitExhaustion
import Mathlib.Data.Nat.Pairing

/-! # Ordered prism simplices for the geometric telescope

Height tagging retains the old orbit vertex. The two copies of the cut vertex
are distinct, and the cut is selected using the invariant old natural label.
These are combinatorial cells; this module asserts no CW realization theorem.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledTelescopePrisms
variable {Γ : Type*} [Group Γ]

/-- Encode the integer height and the old join label in a new join label. -/
def vertex (n : ℕ) (v : LabeledOrbitVertex Γ) : LabeledOrbitVertex Γ :=
  (Nat.pair n v.1, v.2)

@[simp] theorem vertex_smul (n : ℕ) (g : Γ) (v : LabeledOrbitVertex Γ) :
    vertex n (g • v) = g • vertex n v := rfl

theorem vertex_injective (n : ℕ) : Function.Injective (vertex (Γ := Γ) n) := by
  intro a b h
  have hl := Nat.pair_eq_pair.mp (congrArg Prod.fst h)
  have hsnd := congrArg (fun v : LabeledOrbitVertex Γ => v.2) h
  exact Prod.ext hl.2 hsnd

theorem vertex_ne_vertex_succ (n : ℕ) (a b : LabeledOrbitVertex Γ) :
    vertex n a ≠ vertex (n + 1) b := by
  intro h
  have hl := Nat.pair_eq_pair.mp (congrArg Prod.fst h)
  exact Nat.ne_of_lt (Nat.lt_succ_self n) hl.1

/-- The ordered staircase simplex in the prism over s, cut at label k. -/
def vertices (n k : ℕ) (s : LabeledOrbitSimplex Γ) :
    Finset (LabeledOrbitVertex Γ) := by
  classical
  exact ((s.vertices.filter (fun v => v.1 ≤ k)).image (vertex n)) ∪
    ((s.vertices.filter (fun v => k ≤ v.1)).image (vertex (n + 1)))

/-- Every staircase prism is an admissible simplex in the same labeled join. -/
def simplex (n k : ℕ) (s : LabeledOrbitSimplex Γ) : LabeledOrbitSimplex Γ := by
  classical
  refine ⟨vertices n k s, ?_⟩
  intro x hx y hy hxy
  change x ∈ vertices n k s at hx
  change y ∈ vertices n k s at hy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  all_goals
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab := Nat.pair_eq_pair.mp hxy
  · exact congrArg (vertex n)
      (s.labels_injective (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab.2)
  · exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self n) hab.1)
  · exact False.elim (Nat.ne_of_gt (Nat.lt_succ_self n) hab.1)
  · exact congrArg (vertex (n + 1))
      (s.labels_injective (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab.2)

/-- The common ambient coordinate chart for every cut of one cylinder. -/
def boxVertices (n : ℕ) (s : LabeledOrbitSimplex Γ) : Finset (LabeledOrbitVertex Γ) := by
  classical
  exact s.vertices.image (vertex n) ∪ s.vertices.image (vertex (n + 1))

def boxSimplex (n : ℕ) (s : LabeledOrbitSimplex Γ) : LabeledOrbitSimplex Γ := by
  classical
  refine ⟨boxVertices n s, ?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  all_goals
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab := Nat.pair_eq_pair.mp hxy
  · exact congrArg (vertex n) (s.labels_injective ha hb hab.2)
  · exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self n) hab.1)
  · exact False.elim (Nat.ne_of_gt (Nat.lt_succ_self n) hab.1)
  · exact congrArg (vertex (n + 1)) (s.labels_injective ha hb hab.2)

theorem simplex_subset_box (n k : ℕ) (s : LabeledOrbitSimplex Γ) :
    (simplex n k s).vertices ⊆ (boxSimplex n s).vertices := by
  classical
  apply Finset.union_subset_union
  · exact Finset.image_subset_image (Finset.filter_subset _ _)
  · exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem simplex_smul (n k : ℕ) (s : LabeledOrbitSimplex Γ) (g : Γ) :
    simplex n k (g • s) = g • simplex n k s := by
  classical
  apply LabeledOrbitSimplex.ext
  change vertices n k (g • s) = (vertices n k s).image (fun v => g • v)
  have hvertices : (g • s).vertices = s.vertices.image (fun v => g • v) := rfl
  simp only [vertices, hvertices, Finset.image_union,
    Finset.filter_image, Finset.image_image, Function.comp_def]
  rfl

/-- Faces of all ordered prisms over the n-th orbit-finite stage. -/
def allowed [Countable Γ] : Set (LabeledOrbitSimplex Γ) :=
  {t | ∃ n k s, s ∈ LabeledOrbitSimplex.exhaustion n ∧
    t.vertices ⊆ (simplex n k s).vertices}

theorem allowed_downward [Countable Γ] {s t : LabeledOrbitSimplex Γ}
    (hs : s ∈ allowed) (ht : t.vertices ⊆ s.vertices) : t ∈ allowed := by
  obtain ⟨n, k, r, hr, hsr⟩ := hs
  exact ⟨n, k, r, hr, ht.trans hsr⟩

theorem allowed_smul [Countable Γ] {t : LabeledOrbitSimplex Γ}
    (ht : t ∈ allowed) (g : Γ) : g • t ∈ allowed := by
  obtain ⟨n, k, s, hs, hts⟩ := ht
  refine ⟨n, k, g • s, LabeledOrbitSimplex.orbitFaces_smul hs g, ?_⟩
  rw [simplex_smul]
  exact LabeledOrbitSimplex.translate_subset g hts

/-- The standard labeled-simplex no-inversions theorem applies to every prism. -/
theorem fixes_vertex_of_stabilizes (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    {g : Γ} (hg : (simplex n k s).Stabilizes g) {v : LabeledOrbitVertex Γ}
    (hv : v ∈ (simplex n k s).vertices) : g • v = v :=
  (simplex n k s).fixes_vertex_of_stabilizes hg hv

/-- Every nonempty prism face has finite stabilizer, including new vertical cells. -/
theorem finite_stabilizer (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (hne : (simplex n k s).vertices.Nonempty) :
    ({g : Γ | (simplex n k s).Stabilizes g} : Set Γ).Finite :=
  (simplex n k s).finite_stabilizer hne

end BC4lean.ProperActions.LabeledTelescopePrisms
