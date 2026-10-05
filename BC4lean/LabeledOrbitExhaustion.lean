import BC4lean.LabeledOrbitCountability
import BC4lean.LabeledOrbitRealizationAction
import Mathlib.Data.Finset.Powerset

/-! # Finite-orbit subcomplex exhaustion

These are collections of simplices, with explicit finite orbit representatives.
No topological telescope or local compactness conclusion is asserted.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitSimplex
variable {Γ : Type*} [Group Γ]

/-- Faces of all translates of a finite family of generators. -/
def orbitFaces (F : Finset (LabeledOrbitSimplex Γ)) : Set (LabeledOrbitSimplex Γ) :=
  {t | ∃ s ∈ F, ∃ g : Γ, t.vertices ⊆ (g • s).vertices}

theorem orbitFaces_downward {F : Finset (LabeledOrbitSimplex Γ)}
    {s t : LabeledOrbitSimplex Γ} (hs : s ∈ orbitFaces F)
    (ht : t.vertices ⊆ s.vertices) : t ∈ orbitFaces F := by
  obtain ⟨r, hr, g, hg⟩ := hs
  exact ⟨r, hr, g, ht.trans hg⟩

theorem orbitFaces_mono {F G : Finset (LabeledOrbitSimplex Γ)} (h : F ⊆ G) :
    orbitFaces F ⊆ orbitFaces G := by
  rintro t ⟨s, hs, g, hg⟩
  exact ⟨s, h hs, g, hg⟩

theorem translate_subset {s t : LabeledOrbitSimplex Γ} (g : Γ)
    (h : s.vertices ⊆ t.vertices) : (g • s).vertices ⊆ (g • t).vertices := by
  classical
  exact Finset.image_subset_image h

theorem orbitFaces_smul {F : Finset (LabeledOrbitSimplex Γ)}
    {s : LabeledOrbitSimplex Γ} (hs : s ∈ orbitFaces F) (g : Γ) :
    g • s ∈ orbitFaces F := by
  obtain ⟨r, hr, k, hk⟩ := hs
  refine ⟨r, hr, g * k, ?_⟩
  simpa [mul_smul] using translate_subset g hk

/-- Representatives are untransformed faces of the chosen generators. -/
def faceRepresentatives (F : Finset (LabeledOrbitSimplex Γ)) : Set (LabeledOrbitSimplex Γ) :=
  {t | ∃ s ∈ F, t.vertices ⊆ s.vertices}

theorem finite_faceRepresentatives (F : Finset (LabeledOrbitSimplex Γ)) :
    (faceRepresentatives F).Finite := by
  classical
  let P := F.biUnion (fun s => s.vertices.powerset)
  have hP : (P : Set (Finset (LabeledOrbitVertex Γ))).Finite := P.finite_toSet
  have hpre : (vertices ⁻¹' (P : Set (Finset (LabeledOrbitVertex Γ)))).Finite :=
    hP.preimage (fun _ _ _ _ h => ext h)
  apply hpre.subset
  rintro t ⟨s, hs, ht⟩
  exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_powerset.mpr ht⟩

/-- Every generated simplex is a translate of one of finitely many faces. -/
theorem exists_faceRepresentative {F : Finset (LabeledOrbitSimplex Γ)}
    {t : LabeledOrbitSimplex Γ} (ht : t ∈ orbitFaces F) :
    ∃ r ∈ faceRepresentatives F, ∃ g : Γ, g • r = t := by
  obtain ⟨s, hs, g, hg⟩ := ht
  refine ⟨g⁻¹ • t, ⟨s, hs, ?_⟩, g, by simp⟩
  simpa using translate_subset g⁻¹ hg

section Countable
variable [Countable Γ]

/-- The finite family of simplices whose injective encoding is at most n. -/
def exhaustionGenerators (n : ℕ) : Finset (LabeledOrbitSimplex Γ) := by
  let := Encodable.ofCountable (LabeledOrbitSimplex Γ)
  exact (Set.finite_Iic n).preimage Encodable.encode_injective.injOn |>.toFinset

/-- Increasing invariant face collections, each with finitely many orbit representatives. -/
def exhaustion (n : ℕ) : Set (LabeledOrbitSimplex Γ) := orbitFaces (exhaustionGenerators n)

theorem exhaustionGenerators_mono : Monotone (exhaustionGenerators (Γ := Γ)) := by
  intro n m h t ht
  classical
  let := Encodable.ofCountable (LabeledOrbitSimplex Γ)
  change t ∈ ((Set.finite_Iic n).preimage Encodable.encode_injective.injOn).toFinset at ht
  change t ∈ ((Set.finite_Iic m).preimage Encodable.encode_injective.injOn).toFinset
  simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_Iic] using
    le_trans (by simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_Iic] using ht) h

theorem exhaustion_mono : Monotone (exhaustion (Γ := Γ)) :=
  fun _ _ h => orbitFaces_mono (exhaustionGenerators_mono h)

theorem mem_exhaustion (s : LabeledOrbitSimplex Γ) : ∃ n, s ∈ exhaustion n := by
  classical
  let := Encodable.ofCountable (LabeledOrbitSimplex Γ)
  refine ⟨Encodable.encode s, s, ?_, 1, ?_⟩
  · change s ∈ ((Set.finite_Iic (Encodable.encode s)).preimage
      Encodable.encode_injective.injOn).toFinset
    simp
  · simp

end Countable
end BC4lean.ProperActions.LabeledOrbitSimplex
