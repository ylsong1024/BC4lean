import BC4lean.CocompactPieces

/-! # Compact orbit representatives

A weakly locally compact space with compact orbit quotient has a compact set
meeting every orbit. The argument uses the openness of the orbit map; it does
not require properness, Hausdorffness, or second countability.
-/
namespace BC4lean.ProperActions
open Topology

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]

/-- Compactness of the orbit quotient gives compact representatives for all orbits. -/
theorem exists_compact_orbit_representatives
    [ContinuousConstSMul Γ X] [WeaklyLocallyCompactSpace X]
    [CompactSpace (Quotient (MulAction.orbitRel Γ X))] :
    ∃ K : Set X, IsCompact K ∧
      ∀ x : X, ∃ g : Γ, ∃ y : X, y ∈ K ∧ g • y = x := by
  classical
  choose K hKc hKn using (fun x : X => exists_compact_mem_nhds x)
  let q : X → Quotient (MulAction.orbitRel Γ X) :=
    Quotient.mk (MulAction.orbitRel Γ X)
  let U : X → Set (Quotient (MulAction.orbitRel Γ X)) :=
    fun x => q '' interior (K x)
  have hq : IsOpenMap q :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  have hU (x : X) : IsOpen (U x) := hq _ isOpen_interior
  have hcover : (Set.univ : Set (Quotient (MulAction.orbitRel Γ X))) ⊆ ⋃ x, U x := by
    intro z _
    induction z using Quotient.inductionOn with
    | _ x =>
      exact Set.mem_iUnion.mpr
        ⟨x, x, mem_interior_iff_mem_nhds.mpr (hKn x), rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨⋃ x ∈ s, K x, s.isCompact_biUnion (fun x _ => hKc x), ?_⟩
  intro x
  obtain ⟨z, hzs, hxz⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (q x)))
  obtain ⟨y, hy, hyx⟩ := hxz
  have horbit : MulAction.orbitRel Γ X x y := Quotient.exact hyx.symm
  obtain ⟨g, hg⟩ := horbit
  exact ⟨g, y, Set.mem_iUnion₂.mpr ⟨z, hzs, interior_subset hy⟩, hg⟩

end BC4lean.ProperActions
