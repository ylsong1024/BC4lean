import BC4lean.DirectedAddGroupColimit

/-! # Cofinal independence of filtered additive-group colimits

Restriction along a monotone cofinal map of directed preorders induces a genuine
additive equivalence of the constructed colimit groups. Cofinality is the
explicit upper-bound condition, and injectivity of the indexing map is not needed.
-/

noncomputable section

universe u v uκ uL

namespace BC4lean.DirectedAddGroupDiagram

variable {ι : Type u} [Preorder ι] (D : DirectedAddGroupDiagram.{u, v} ι)
variable {κ : Type uκ} [Preorder κ]

/-- Restrict an additive-group diagram along a monotone indexing map. -/
def restrict (φ : κ →o ι) : DirectedAddGroupDiagram.{uκ, v} κ where
  obj j := D.obj (φ j)
  map i j hij := D.map (φ i) (φ j) (φ.monotone hij)
  map_id i x := D.map_id (φ i) x
  map_comp i j k hij hjk x := D.map_comp (φ i) (φ j) (φ k)
    (φ.monotone hij) (φ.monotone hjk) x

variable [Nonempty ι] [IsDirectedOrder ι] [Nonempty κ] [IsDirectedOrder κ]

/-- The canonical map from a restricted colimit into the original colimit. -/
def reindex (φ : κ →o ι) : (D.restrict φ).Colimit →+ D.Colimit :=
  (D.restrict φ).desc (fun j => D.of (φ j))
    (fun _i _j hij x => D.of_map (φ.monotone hij) x)

@[simp] theorem reindex_of (φ : κ →o ι) (j : κ) (x : D.obj (φ j)) :
    D.reindex φ ((D.restrict φ).of j x) = D.of (φ j) x := rfl

/-- A cofinal indexing map meets an upper bound of every original index. -/
def Cofinal (φ : κ →o ι) : Prop := ∀ i : ι, ∃ j : κ, i ≤ φ j

/-- Cofinality makes the canonical reindexing map surjective. -/
theorem reindex_surjective (φ : κ →o ι) (hφ : Cofinal φ) :
    Function.Surjective (D.reindex φ) := by
  intro z
  obtain ⟨i, x, rfl⟩ := D.exists_of z
  obtain ⟨j, hij⟩ := hφ i
  exact ⟨(D.restrict φ).of j (D.map i (φ j) hij x), D.of_map hij x⟩

/-- Eventual equality in the original system already holds in a cofinal restriction. -/
theorem reindex_injective (φ : κ →o ι) (hφ : Cofinal φ) :
    Function.Injective (D.reindex φ) := by
  intro z w h
  obtain ⟨i, x, rfl⟩ := (D.restrict φ).exists_of z
  obtain ⟨j, y, rfl⟩ := (D.restrict φ).exists_of w
  obtain ⟨k, hik, hjk, hxy⟩ := (D.of_eq_iff x y).mp h
  obtain ⟨s, hks⟩ := hφ k
  obtain ⟨t, hit, hjt, hst⟩ := directed_of₃ (· ≤ ·) i j s
  apply ((D.restrict φ).of_eq_iff x y).mpr
  refine ⟨t, hit, hjt, ?_⟩
  change D.map (φ i) (φ t) (φ.monotone hit) x =
    D.map (φ j) (φ t) (φ.monotone hjt) y
  rw [← D.map_comp (φ i) k (φ t) hik (hks.trans (φ.monotone hst)) x,
    ← D.map_comp (φ j) k (φ t) hjk (hks.trans (φ.monotone hst)) y, hxy]

/-- Cofinal restriction preserves the actual filtered colimit as an additive group. -/
def cofinalEquiv (φ : κ →o ι) (hφ : Cofinal φ) :
    (D.restrict φ).Colimit ≃+ D.Colimit :=
  AddEquiv.ofBijective (D.reindex φ)
    ⟨D.reindex_injective φ hφ, D.reindex_surjective φ hφ⟩

@[simp] theorem cofinalEquiv_of (φ : κ →o ι) (hφ : Cofinal φ)
    (j : κ) (x : D.obj (φ j)) :
    D.cofinalEquiv φ hφ ((D.restrict φ).of j x) = D.of (φ j) x := rfl

/-- The inverse cofinal equivalence sends any original representative to an upper-bound
representative in the restricted diagram. -/
theorem cofinalEquiv_symm_of (φ : κ →o ι) (hφ : Cofinal φ)
    (i : ι) (j : κ) (hij : i ≤ φ j) (x : D.obj i) :
    (D.cofinalEquiv φ hφ).symm (D.of i x) =
      (D.restrict φ).of j (D.map i (φ j) hij x) := by
  apply (D.cofinalEquiv φ hφ).injective
  simp

variable {L : Type uL} [Preorder L] [Nonempty L] [IsDirectedOrder L]

/-- Any two cofinal restrictions of the same diagram have canonically equivalent colimits. -/
def cofinalComparisonEquiv (φ : κ →o ι) (ψ : L →o ι)
    (hφ : Cofinal φ) (hψ : Cofinal ψ) :
    (D.restrict φ).Colimit ≃+ (D.restrict ψ).Colimit :=
  (D.cofinalEquiv φ hφ).trans (D.cofinalEquiv ψ hψ).symm

end BC4lean.DirectedAddGroupDiagram
