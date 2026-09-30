import BC4lean.EquivariantMaps
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Maps from homogeneous orbits

Evaluation at the identity coset identifies continuous equivariant maps out of
`Γ ⧸ H` with `H`-fixed points. No normality or finiteness hypothesis on `H` is used.
-/
namespace BC4lean.ProperActions

variable {Γ X Y : Type*} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable [TopologicalSpace X] [MulAction Γ X]
variable [TopologicalSpace Y] [MulAction Γ Y]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The identity coset is fixed by the subgroup defining the orbit. -/
theorem subgroup_fixes_identity_coset (H : Subgroup Γ) (h : H) :
    (h : Γ) • (QuotientGroup.mk 1 : Γ ⧸ H) = QuotientGroup.mk 1 := by
  change QuotientGroup.mk ((h : Γ) * 1) = (QuotientGroup.mk 1 : Γ ⧸ H)
  rw [mul_one, QuotientGroup.eq]
  simpa only [mul_one] using H.inv_mem h.property

/-- Descend `g ↦ g • x` to the orbit when `x` is `H`-fixed. -/
def orbitMap (H : Subgroup Γ) (x : FixedPointSpace H X) : EquivariantMap Γ (Γ ⧸ H) X where
  toFun := Quotient.lift (fun g : Γ => g • (x : X)) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hx := x.property ⟨a⁻¹ * b, hab'⟩
    change (a⁻¹ * b) • (x : X) = x at hx
    have := congrArg (fun z : X => a • z) hx
    simpa [mul_smul] using this.symm)
  continuous_toFun := by
    let : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology (isOpen_discrete _)
    exact continuous_of_discreteTopology
  map_smul' g q := by
    induction q using QuotientGroup.induction_on with
    | H a => exact mul_smul g a (x : X)

@[simp] theorem orbitMap_mk (H : Subgroup Γ) (x : FixedPointSpace H X) (g : Γ) :
    orbitMap H x (QuotientGroup.mk g) = g • (x : X) := rfl

/-- Evaluation at the identity coset has values in the fixed-point subspace. -/
def orbitEvaluation (H : Subgroup Γ) (f : EquivariantMap Γ (Γ ⧸ H) X) :
    FixedPointSpace H X :=
  ⟨f (QuotientGroup.mk 1), fun h => by
    change (h : Γ) • f (QuotientGroup.mk 1) = f (QuotientGroup.mk 1)
    rw [← f.map_smul, subgroup_fixes_identity_coset]⟩

omit [DiscreteTopology Γ] in
@[simp] theorem orbitEvaluation_val (H : Subgroup Γ) (f : EquivariantMap Γ (Γ ⧸ H) X) :
    (orbitEvaluation H f : X) = f (QuotientGroup.mk 1) := rfl

/-- The orbit/fixed-point correspondence for continuous equivariant maps. -/
def orbitFixedPointEquiv (H : Subgroup Γ) :
    EquivariantMap Γ (Γ ⧸ H) X ≃ FixedPointSpace H X where
  toFun := orbitEvaluation H
  invFun := orbitMap H
  left_inv f := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H g =>
      change g • f (QuotientGroup.mk 1) = f (QuotientGroup.mk g)
      rw [← f.map_smul]
      congr 1
      change QuotientGroup.mk (g * 1) = (QuotientGroup.mk g : Γ ⧸ H)
      rw [mul_one]
  right_inv x := by
    apply Subtype.ext
    exact one_smul Γ (x : X)

/-- The correspondence commutes with postcomposition. -/
theorem orbitFixedPointEquiv_natural (H : Subgroup Γ)
    (f : EquivariantMap Γ (Γ ⧸ H) X) (g : EquivariantMap Γ X Y) :
    orbitFixedPointEquiv H (g.comp f) = g.fixedPointsMap H (orbitFixedPointEquiv H f) := rfl

end BC4lean.ProperActions
