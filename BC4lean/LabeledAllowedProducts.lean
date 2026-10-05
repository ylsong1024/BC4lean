import BC4lean.LabeledAllowedRealization
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Quotient atlases and product continuity for allowed realizations

A downward family has its actual induced subspace topology. Its finite allowed
charts form a quotient atlas, so products with locally compact parameters retain
the chartwise continuity criterion.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
open Topology
variable {Γ : Type*} [Group Γ]

/-- Open sets of an allowed realization can be checked on its allowed charts. -/
theorem isOpen_iff_allowedCharts (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    (U : Set (AllowedRealization A)) :
    IsOpen U ↔ ∀ s (hs : s ∈ A), IsOpen ((allowedChart A hA s hs) ⁻¹' U) := by
  simpa only [Set.preimage_compl, isClosed_compl_iff] using
    (isClosed_iff_allowedCharts A hA Uᶜ)

/-- The disjoint union of allowed finite charts. -/
def allowedAtlas (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    (p : Σ s : {s : LabeledOrbitSimplex Γ // s ∈ A}, LabeledSimplexCoordinates Γ s.val) :
    AllowedRealization A := allowedChart A hA p.1.val p.1.property p.2

/-- The actual subspace topology is the quotient topology of allowed finite charts. -/
theorem allowedAtlas_isQuotientMap (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A) :
    IsQuotientMap (allowedAtlas A hA) := by
  refine ⟨.of_isOpen_preimage_iff_isOpen ?_, ?_⟩
  · intro U
    rw [isOpen_sigma_iff]
    constructor
    · intro hU
      apply (isOpen_iff_allowedCharts A hA U).mpr
      intro s hs
      exact hU ⟨s, hs⟩
    · intro hU s
      exact (isOpen_iff_allowedCharts A hA U).mp hU s.val s.property
  · intro x
    refine ⟨⟨⟨supportSimplex x.val, x.property⟩,
      ⟨x.val.val, mem_coordinates_supportSimplex x.val⟩⟩, ?_⟩
    rfl

/-- Products with locally compact parameters retain the allowed chart criterion. -/
theorem continuous_allowed_product_iff (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    {T Y : Type*} [TopologicalSpace T] [LocallyCompactSpace T] [TopologicalSpace Y]
    (f : AllowedRealization A × T → Y) :
    Continuous f ↔ ∀ s (hs : s ∈ A),
      Continuous (fun p : LabeledSimplexCoordinates Γ s × T =>
        f (allowedChart A hA s hs p.1, p.2)) := by
  constructor
  · intro hf s hs
    exact hf.comp ((continuous_allowedChart A hA s hs).prodMap continuous_id)
  · intro hf
    apply (allowedAtlas_isQuotientMap A hA).continuous_lift_prod_left
    let e := Homeomorph.sigmaProdDistrib
      (X := fun s : {s : LabeledOrbitSimplex Γ // s ∈ A} =>
        LabeledSimplexCoordinates Γ s.val) (Y := T)
    have hc : Continuous
        (fun p : Σ s : {s : LabeledOrbitSimplex Γ // s ∈ A},
          LabeledSimplexCoordinates Γ s.val × T =>
          f (allowedChart A hA p.1.val p.1.property p.2.1, p.2.2)) :=
      continuous_sigma (fun s => hf s.val s.property)
    exact hc.comp e.continuous

end BC4lean.ProperActions.LabeledOrbitRealization
