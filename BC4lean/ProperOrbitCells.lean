import BC4lean.OrbitFixedPoints
import Mathlib.Topology.AlexandrovDiscrete

/-! # Proper homogeneous orbits and orbit cells -/
namespace BC4lean.ProperActions
open scoped Pointwise

variable {Γ X Y : Type*} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- For a finite subgroup of a discrete group, the coset projection is proper. -/
theorem proper_cosetProjection (H : Subgroup Γ) [Finite H] :
    IsProperMap (QuotientGroup.mk : Γ → Γ ⧸ H) := by
  let : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology (isOpen_discrete _)
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨continuous_of_discreteTopology, fun _ _ => isClosed_discrete _, ?_⟩
  intro q
  induction q using QuotientGroup.induction_on with | H g =>
    apply Set.Finite.isCompact
    apply (Set.finite_range (fun h : H => g * (h : Γ))).subset
    intro a ha
    have hga : g⁻¹ * a ∈ H := QuotientGroup.eq.mp (Set.mem_singleton_iff.mp ha).symm
    exact ⟨⟨g⁻¹ * a, hga⟩, mul_inv_cancel_left g a⟩

/-- A homogeneous orbit with finite stabilizer is a proper discrete-group space. -/
theorem proper_orbit (H : Subgroup Γ) [Finite H] : ProperSMul Γ (Γ ⧸ H) := by
  apply MulAction.properSMul_of_proper_orbitMap (x := (QuotientGroup.mk 1 : Γ ⧸ H))
  simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using proper_cosetProjection H

/-- Properness of the homogeneous orbit is equivalent to finiteness of its stabilizer. -/
theorem proper_orbit_iff (H : Subgroup Γ) : ProperSMul Γ (Γ ⧸ H) ↔ Finite H := by
  constructor
  · intro h
    let := h
    exact (finite_subgroup_of_fixedPoint (H := H)
      (x := (QuotientGroup.mk 1 : Γ ⧸ H)) (subgroup_fixes_identity_coset H)).to_subtype
  · intro h
    let := h
    exact proper_orbit H

variable [TopologicalSpace X] [MulAction Γ X] [ContinuousSMul Γ X]
variable [LocallyCompactSpace X] [T2Space X]
variable [TopologicalSpace Y] [MulAction Γ Y] [ProperSMul Γ Y]

/-- An equivariant map to a proper space forces properness of an LCH source. -/
theorem proper_of_equivariantMap (f : EquivariantMap Γ X Y) : ProperSMul Γ X := by
  apply proper_iff_finite_transporters.mpr
  intro K L hK hL
  apply (finite_transporter (Γ := Γ) (hK.image f.continuous) (hL.image f.continuous)).subset
  intro g hg
  obtain ⟨y, hy, hyL⟩ := hg
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨f y, ?_, ⟨y, hyL, rfl⟩⟩
  refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
  change g • f x = f y
  exact (f.map_smul g x).symm.trans (congrArg f hxy)

/-- An orbit cell, with the group acting only on its homogeneous-orbit factor.
Taking `D` to be a disk gives the cells used in equivariant CW constructions. -/
def OrbitCell (H : Subgroup Γ) (D : Type*) := (Γ ⧸ H) × D

namespace OrbitCell
variable (H : Subgroup Γ) (D : Type*) [TopologicalSpace D]

instance instTopologicalSpace : TopologicalSpace (OrbitCell H D) :=
  inferInstanceAs (TopologicalSpace ((Γ ⧸ H) × D))

instance instMulAction : MulAction Γ (OrbitCell H D) where
  smul g p := (g • p.1, p.2)
  one_smul p := Prod.ext (one_smul Γ p.1) rfl
  mul_smul g h p := Prod.ext (mul_smul g h p.1) rfl

instance instContinuousSMul : ContinuousSMul Γ (OrbitCell H D) where
  continuous_smul :=
    (continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd

instance instLocallyCompactSpace [LocallyCompactSpace D] :
    LocallyCompactSpace (OrbitCell H D) := by
  let : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology (isOpen_discrete _)
  exact inferInstanceAs (LocallyCompactSpace ((Γ ⧸ H) × D))

instance instT2Space [T2Space D] : T2Space (OrbitCell H D) := by
  let : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology (isOpen_discrete _)
  exact inferInstanceAs (T2Space ((Γ ⧸ H) × D))

/-- Projection onto the homogeneous-orbit factor. -/
def projection : EquivariantMap Γ (OrbitCell H D) (Γ ⧸ H) where
  toFun p := p.1
  continuous_toFun := continuous_fst
  map_smul' _ _ := rfl

/-- Orbit cells with finite stabilizer and LCH parameter are proper. -/
theorem proper [Finite H] [LocallyCompactSpace D] [T2Space D] :
    ProperSMul Γ (OrbitCell H D) := by
  let := proper_orbit H
  exact proper_of_equivariantMap (projection H D)

end OrbitCell
end BC4lean.ProperActions
