import BC4lean.EquivariantCW

/-! # Maps from orbit cells and fixed-point extension problems

Continuous equivariant maps Γ/H × D → X are continuous maps D → X^H.
Consequently extension across a parameter map is exactly an ordinary extension
problem in the fixed-point space. This does not assume or prove that those
ordinary extensions exist for contractible targets.
-/
namespace BC4lean.ProperActions

universe u v w

variable {Γ : Type u} {D E : Type v} {X : Type w} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace X]
variable [MulAction Γ X] [ContinuousConstSMul Γ X]

/-- Evaluate an equivariant map on the identity-coset slice. -/
def cellEvaluation (H : Subgroup Γ) (f : EquivariantMap Γ (OrbitCell H D) X) :
    C(D, FixedPointSpace H X) where
  toFun d := ⟨f (QuotientGroup.mk 1, d), fun h => by
    change (h : Γ) • f (QuotientGroup.mk 1, d) = f (QuotientGroup.mk 1, d)
    exact (f.map_smul (h : Γ) (QuotientGroup.mk 1, d)).symm.trans
      (congrArg f (Prod.ext (subgroup_fixes_identity_coset H h) rfl))⟩
  continuous_toFun :=
    (f.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _

/-- Extend a continuous family of fixed points equivariantly over the orbit factor. -/
def cellFromFixed (H : Subgroup Γ) (u : C(D, FixedPointSpace H X)) :
    EquivariantMap Γ (OrbitCell H D) X where
  toFun p := orbitMap H (u p.2) p.1
  continuous_toFun := by
    let : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology (isOpen_discrete _)
    change Continuous (fun p : (Γ ⧸ H) × D => orbitMap H (u p.2) p.1)
    apply continuous_prod_of_discrete_left.mpr
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      change Continuous (fun d => g • (u d : X))
      exact (continuous_const_smul g).comp (continuous_subtype_val.comp u.continuous)
  map_smul' g p := (orbitMap H (u p.2)).map_smul g p.1

/-- The orbit/fixed-point correspondence with a topological parameter. -/
def orbitCellMapEquiv (H : Subgroup Γ) :
    EquivariantMap Γ (OrbitCell H D) X ≃ C(D, FixedPointSpace H X) where
  toFun := cellEvaluation H
  invFun := cellFromFixed H
  left_inv f := by
    ext p
    rcases p with ⟨q, d⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      change g • f (QuotientGroup.mk 1, d) = f (QuotientGroup.mk g, d)
      apply (f.map_smul g (QuotientGroup.mk 1, d)).symm.trans
      apply congrArg f
      change (g • (QuotientGroup.mk 1 : Γ ⧸ H), d) = (QuotientGroup.mk g, d)
      simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  right_inv u := by
    ext d
    exact one_smul Γ (u d : X)

omit [ContinuousConstSMul Γ X] [DiscreteTopology Γ] in
/-- Evaluation commutes with restriction along any continuous parameter map. -/
theorem cellEvaluation_comp (H : Subgroup Γ) (i : C(D, E))
    (f : EquivariantMap Γ (OrbitCell H E) X) :
    cellEvaluation H (f.comp (OrbitCell.map H i)) = (cellEvaluation H f).comp i := by
  ext d
  rfl

/-- An equivariant cell extension exists exactly when its fixed-point slice extends. -/
theorem orbitCell_extension_iff (H : Subgroup Γ) (i : C(D, E))
    (f : EquivariantMap Γ (OrbitCell H D) X) :
    (∃ F : EquivariantMap Γ (OrbitCell H E) X, F.comp (OrbitCell.map H i) = f) ↔
      ∃ u : C(E, FixedPointSpace H X), u.comp i = cellEvaluation H f := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨cellEvaluation H F, (cellEvaluation_comp H i F).symm.trans (congrArg (cellEvaluation H) hF)⟩
  · rintro ⟨u, hu⟩
    refine ⟨cellFromFixed H u, ?_⟩
    apply (orbitCellMapEquiv H).injective
    change cellEvaluation H ((cellFromFixed H u).comp (OrbitCell.map H i)) = cellEvaluation H f
    rw [cellEvaluation_comp]
    have he : cellEvaluation H (cellFromFixed H u) = u := (orbitCellMapEquiv H).apply_symm_apply u
    rw [he, hu]

end BC4lean.ProperActions
