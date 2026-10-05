import BC4lean.CompactModuleOperator
import BC4lean.EquivariantHilbertModule

/-! # Group transport of compact Hilbert C⋆-module maps

Compatible module actions preserve the rank-one span and its operator-norm
closure, including when the action on the coefficient algebra is nontrivial.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E F : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  {α : CStarAlgebraAction Γ B}

namespace EquivariantHilbertModule

/-- Transport by compatible actions, as a bounded complex-linear map on the
space of adjointable maps. -/
def conjugateMapContinuousLinearMap (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) :
    AdjointableMap B E F →L[ℂ] AdjointableMap B E F :=
  LinearMap.mkContinuous
    { toFun := U.conjugateMap V g
      map_add' := fun S T => by
        change U.conjugateMap V g (S.add T) =
          (U.conjugateMap V g S).add (U.conjugateMap V g T)
        exact U.conjugateMap_add V g S T
      map_smul' := fun c T => by
        change U.conjugateMap V g (T.smul c) = (U.conjugateMap V g T).smul c
        exact U.conjugateMap_smul V g T c }
    1 (fun T => by
      simp only [AdjointableMap.norm_def, one_mul]
      exact (U.conjugateMap_norm V g T).le)

omit [StarOrderedRing B] in
@[simp] theorem conjugateMapContinuousLinearMap_apply
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule α F)
    (g : Γ) (T : AdjointableMap B E F) :
    U.conjugateMapContinuousLinearMap V g T = U.conjugateMap V g T := rfl

/-- Compatible actions preserve module finite-rank maps. -/
theorem conjugateMap_mem_moduleFiniteRank (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) {T : AdjointableMap B E F}
    (hT : T ∈ moduleFiniteRank B E F) :
    U.conjugateMap V g T ∈ moduleFiniteRank B E F := by
  change U.conjugateMapContinuousLinearMap V g T ∈ moduleFiniteRank B E F
  induction hT using Submodule.span_induction with
  | mem T hT =>
    rcases hT with ⟨⟨x, y⟩, rfl⟩
    simpa only [conjugateMapContinuousLinearMap_apply, conjugateMap_rankOne] using
      moduleRankOne_mem_moduleFiniteRank (V.action g x) (U.action g y)
  | zero =>
    rw [map_zero]
    exact (moduleFiniteRank B E F).zero_mem
  | add S T _ _ hS hT =>
    rw [map_add]
    exact (moduleFiniteRank B E F).add_mem hS hT
  | smul c T _ hT =>
    rw [map_smul]
    exact (moduleFiniteRank B E F).smul_mem _ hT

/-- Compatible actions preserve compact module maps by continuity and the
rank-one transformation identity. -/
theorem conjugateMap_mem_moduleCompact (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) {T : AdjointableMap B E F}
    (hT : T ∈ moduleCompact B E F) : U.conjugateMap V g T ∈ moduleCompact B E F := by
  have h : closure (moduleFiniteRank B E F : Set (AdjointableMap B E F)) ⊆
      U.conjugateMapContinuousLinearMap V g ⁻¹'
        (moduleCompact B E F : Set (AdjointableMap B E F)) :=
    closure_minimal
      (fun _ hS => moduleFiniteRank_le_moduleCompact
        (U.conjugateMap_mem_moduleFiniteRank V g hS))
      (moduleCompact_isClosed.preimage (U.conjugateMapContinuousLinearMap V g).continuous)
  exact h hT

@[simp] theorem conjugateMap_mem_moduleCompact_iff
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule α F)
    (g : Γ) (T : AdjointableMap B E F) :
    U.conjugateMap V g T ∈ moduleCompact B E F ↔ T ∈ moduleCompact B E F := by
  constructor
  · intro hT
    have h := U.conjugateMap_mem_moduleCompact V g⁻¹ hT
    have hInv : U.conjugateMap V g⁻¹ (U.conjugateMap V g T) = T := by
      rw [← conjugateMap_mul, inv_mul_cancel, conjugateMap_one]
    rwa [hInv] at h
  · exact U.conjugateMap_mem_moduleCompact V g

/-- Compact endomorphisms are invariant under conjugation by the module
action. -/
theorem conjugateOperator_mem_moduleCompact (U : EquivariantHilbertModule α E)
    (g : Γ) {T : AdjointableMap B E E} (hT : T ∈ moduleCompact B E E) :
    U.conjugateOperator g T ∈ moduleCompact B E E :=
  U.conjugateMap_mem_moduleCompact U g hT

@[simp] theorem conjugateOperator_mem_moduleCompact_iff
    (U : EquivariantHilbertModule α E) (g : Γ) (T : AdjointableMap B E E) :
    U.conjugateOperator g T ∈ moduleCompact B E E ↔ T ∈ moduleCompact B E E :=
  U.conjugateMap_mem_moduleCompact_iff U g T

end EquivariantHilbertModule

namespace IsModuleCompact

theorem conjugateMap {T : AdjointableMap B E F} (hT : IsModuleCompact T)
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule α F) (g : Γ) :
    IsModuleCompact (U.conjugateMap V g T) := U.conjugateMap_mem_moduleCompact V g hT

theorem conjugateOperator {T : AdjointableMap B E E} (hT : IsModuleCompact T)
    (U : EquivariantHilbertModule α E) (g : Γ) :
    IsModuleCompact (U.conjugateOperator g T) := U.conjugateOperator_mem_moduleCompact g hT

end IsModuleCompact
end BC4lean.KKTheory
