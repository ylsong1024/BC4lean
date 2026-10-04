import BC4lean.DiskExtension
import BC4lean.OrbitCellMaps
import BC4lean.FixedPointCriterion

/-!
# Extension over equivariant disk cells

Contractibility of the H-fixed points gives extension over a Γ/H-cell.
This is the single-cell extension step, not yet the full cellular mapping theorem.
-/

namespace BC4lean.ProperActions

universe u v

variable {Γ : Type u} {X : Type v} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable [TopologicalSpace X] [MulAction Γ X] [ContinuousConstSMul Γ X]

/-- A map on the boundary of an orbit cell extends when the fixed-point target is contractible. -/
theorem orbitCell_extends_of_contractible (H : Subgroup Γ)
    [ContractibleSpace (FixedPointSpace H X)] (n : ℕ)
    (f : EquivariantMap Γ (OrbitCell H (TopCat.diskBoundary.{u} n)) X) :
    ∃ F : EquivariantMap Γ (OrbitCell H (TopCat.disk.{u} n)) X,
      F.comp (OrbitCell.boundaryInclusion H n) = f := by
  apply (orbitCell_extension_iff H (TopCat.diskBoundaryInclusion n).hom f).mpr
  exact contractible_extends_disk n (cellEvaluation H f)

/-- The fixed-point criterion supplies extension for each finite-isotropy orbit cell. -/
theorem FixedPointCriterion.orbitCell_extends (h : FixedPointCriterion Γ X)
    (H : Subgroup Γ) [Finite H] (n : ℕ)
    (f : EquivariantMap Γ (OrbitCell H (TopCat.diskBoundary.{u} n)) X) :
    ∃ F : EquivariantMap Γ (OrbitCell H (TopCat.disk.{u} n)) X,
      F.comp (OrbitCell.boundaryInclusion H n) = f := by
  let := h.1 H inferInstance
  exact orbitCell_extends_of_contractible H n f

end BC4lean.ProperActions
