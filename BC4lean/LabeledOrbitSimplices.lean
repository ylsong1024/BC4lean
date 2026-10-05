import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Finset.Image

/-! # Labeled finite-isotropy orbit simplices

This module supplies only the combinatorics for a possible join realization.
It makes no assertion about realization, CW structure, or contractibility.
-/
namespace BC4lean.ProperActions

variable (Γ : Type*) [Group Γ]

/-- Orbit vertices, tagged by their finite isotropy subgroup. -/
abbrev FiniteOrbitVertex := Σ H : {H : Subgroup Γ // Finite H}, Γ ⧸ H.val

namespace FiniteOrbitVertex

instance : MulAction Γ (FiniteOrbitVertex Γ) where
  smul g v := ⟨v.1, g • v.2⟩
  one_smul v := by
    change Sigma.mk v.1 ((1 : Γ) • v.2) = v
    simp only [one_smul]
  mul_smul g h v := by
    change (⟨v.1, (g * h) • v.2⟩ : FiniteOrbitVertex Γ) = ⟨v.1, g • h • v.2⟩
    rw [mul_smul]

/-- Each orbit vertex has genuinely finite isotropy. -/
theorem finite_fixing (v : FiniteOrbitVertex Γ) :
    ({g : Γ | g • v = v} : Set Γ).Finite := by
  rcases v with ⟨H, q⟩
  let : Finite H.val := H.property
  induction q using QuotientGroup.induction_on with | H a =>
    apply (Set.finite_range (fun h : H.val => a * (h : Γ) * a⁻¹)).subset
    intro g hg
    have he : (QuotientGroup.mk (g * a) : Γ ⧸ H.val) = QuotientGroup.mk a := by
      change (⟨H, g • (QuotientGroup.mk a : Γ ⧸ H.val)⟩ : FiniteOrbitVertex Γ) =
        ⟨H, (QuotientGroup.mk a : Γ ⧸ H.val)⟩ at hg
      exact eq_of_heq (Sigma.mk.inj_iff.mp hg).2
    have hm : a⁻¹ * (g * a) ∈ H.val := QuotientGroup.eq.mp he.symm
    refine ⟨⟨a⁻¹ * (g * a), hm⟩, ?_⟩
    simp [mul_assoc]

end FiniteOrbitVertex

/-- Distinct join factors are distinguished by natural-number labels. -/
abbrev LabeledOrbitVertex := ℕ × FiniteOrbitVertex Γ

instance : MulAction Γ (LabeledOrbitVertex Γ) where
  smul g v := (v.1, g • v.2)
  one_smul v := Prod.ext rfl (one_smul Γ v.2)
  mul_smul g h v := Prod.ext rfl (mul_smul g h v.2)

/-- The identity coset supplies a fixed vertex at every factor label. -/
def fixedOrbitVertex (H : Subgroup Γ) [Finite H] (n : ℕ) : LabeledOrbitVertex Γ :=
  (n, ⟨⟨H, inferInstance⟩, QuotientGroup.mk 1⟩)

/-- Every element of the chosen finite subgroup fixes its labeled vertex. -/
theorem fixedOrbitVertex_fixed (H : Subgroup Γ) [Finite H] (n : ℕ) (h : H) :
    (h : Γ) • fixedOrbitVertex Γ H n = fixedOrbitVertex Γ H n := by
  have he : (h : Γ) • (QuotientGroup.mk 1 : Γ ⧸ H) = QuotientGroup.mk 1 := by
    change (QuotientGroup.mk ((h : Γ) * 1) : Γ ⧸ H) = QuotientGroup.mk 1
    apply QuotientGroup.eq.mpr
    simp
  exact congrArg (fun q : Γ ⧸ H =>
    (n, (⟨⟨H, inferInstance⟩, q⟩ : FiniteOrbitVertex Γ))) he

/-- A finite simplex uses at most one vertex from each join factor. -/
structure LabeledOrbitSimplex where
  vertices : Finset (LabeledOrbitVertex Γ)
  labels_injective : Set.InjOn Prod.fst (vertices : Set (LabeledOrbitVertex Γ))

namespace LabeledOrbitSimplex

variable {Γ}

@[ext] theorem ext {s t : LabeledOrbitSimplex Γ} (h : s.vertices = t.vertices) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- Translation preserves labels and therefore preserves admissible simplices. -/
noncomputable def translate (g : Γ) (s : LabeledOrbitSimplex Γ) :
    LabeledOrbitSimplex Γ := by
  classical
  refine ⟨s.vertices.image (fun v => g • v), ?_⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  exact congrArg (fun v : LabeledOrbitVertex Γ => g • v)
    (s.labels_injective ha hb hxy)

noncomputable instance : MulAction Γ (LabeledOrbitSimplex Γ) where
  smul := translate
  one_smul s := by
    classical
    apply ext
    change s.vertices.image (fun v => (1 : Γ) • v) = s.vertices
    simp
  mul_smul g h s := by
    classical
    apply ext
    change s.vertices.image (fun v => (g * h) • v) =
      (s.vertices.image (fun v => h • v)).image (fun v => g • v)
    rw [Finset.image_image]
    simp only [mul_smul, Function.comp_def]

/-- Every finite face is again an admissible labeled simplex. -/
def ofSubset (s : LabeledOrbitSimplex Γ) (t : Finset (LabeledOrbitVertex Γ))
    (h : t ⊆ s.vertices) : LabeledOrbitSimplex Γ :=
  ⟨t, fun _ hx _ hy he => s.labels_injective (h hx) (h hy) he⟩

/-- Setwise stabilization of the vertices. -/
def Stabilizes (s : LabeledOrbitSimplex Γ) (g : Γ) : Prop :=
  ∀ v, v ∈ s.vertices ↔ g • v ∈ s.vertices

/-- Unique factor labels forbid nontrivial permutations of simplex vertices. -/
theorem fixes_vertex_of_stabilizes (s : LabeledOrbitSimplex Γ) {g : Γ}
    (hg : s.Stabilizes g) {v : LabeledOrbitVertex Γ} (hv : v ∈ s.vertices) :
    g • v = v :=
  s.labels_injective ((hg v).mp hv) hv rfl

/-- A nonempty simplex has finite setwise isotropy. -/
theorem finite_stabilizer (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    ({g : Γ | s.Stabilizes g} : Set Γ).Finite := by
  obtain ⟨v, hv⟩ := hne
  apply (FiniteOrbitVertex.finite_fixing Γ v.2).subset
  intro g hg
  exact congrArg Prod.snd (s.fixes_vertex_of_stabilizes hg hv)

end LabeledOrbitSimplex
end BC4lean.ProperActions

namespace BC4lean.ProperActions.LabeledOrbitSimplex
variable {Γ : Type*} [Group Γ]

/-- The setwise fixing predicate agrees with the actual simplex action. -/
theorem stabilizes_iff_smul_eq (s : LabeledOrbitSimplex Γ) (g : Γ) :
    s.Stabilizes g ↔ g • s = s := by
  classical
  constructor
  · intro hg
    apply ext
    apply Finset.ext
    intro v
    change v ∈ s.vertices.image (fun v => g • v) ↔ v ∈ s.vertices
    constructor
    · rintro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (hg w).mp hw
    · intro hv
      have hw : g⁻¹ • v ∈ s.vertices :=
        (hg (g⁻¹ • v)).mpr (by simpa using hv)
      exact Finset.mem_image.mpr ⟨g⁻¹ • v, hw, by simp⟩
  · intro hg v
    have hv : (g • s).vertices = s.vertices := congrArg vertices hg
    change s.vertices.image (fun v => g • v) = s.vertices at hv
    constructor
    · intro h
      rw [← hv]
      exact Finset.mem_image.mpr ⟨v, h, rfl⟩
    · intro h
      rw [← hv] at h
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      have : w = v := (MulAction.injective g) he
      simpa [this] using hw

/-- Nonempty simplices have finite stabilizer subgroups for the actual action. -/
theorem stabilizer_finite (s : LabeledOrbitSimplex Γ) (hne : s.vertices.Nonempty) :
    Finite (MulAction.stabilizer Γ s) := by
  apply Set.Finite.to_subtype
  apply (s.finite_stabilizer hne).subset
  intro g hg
  exact (s.stabilizes_iff_smul_eq g).mpr hg

end BC4lean.ProperActions.LabeledOrbitSimplex
