import BC4lean.ClosedStageTelescope
import BC4lean.LabeledOrbitFiniteOrbitSubspace
import BC4lean.ProperActionPullback

/-! # A locally compact second-countable proper telescope

The telescope uses the countable exhaustion by finite-orbit face subspaces.
Its projection to the weak realization is continuous, equivariant and
surjective. No section, CW structure, or fixed-point contractibility is asserted.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitTelescope

variable (Γ : Type*) [Group Γ] [Countable Γ]

/-- The n-th invariant finite-orbit face subspace, as a subset of the realization. -/
def stage (n : ℕ) : Set (LabeledOrbitRealization Γ) :=
  {x | LabeledOrbitRealization.supportSimplex x ∈ LabeledOrbitSimplex.exhaustion n}

theorem stage_mono : Monotone (stage Γ) :=
  fun _ _ h _ hx => LabeledOrbitSimplex.exhaustion_mono h hx

theorem stage_isClosed (n : ℕ) : IsClosed (stage Γ n) :=
  LabeledOrbitRealization.isClosed_orbitFaceSpace (LabeledOrbitSimplex.exhaustionGenerators n)

theorem stages_cover : (⋃ n : ℕ, stage Γ n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := LabeledOrbitSimplex.mem_exhaustion (LabeledOrbitRealization.supportSimplex x)
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

omit [Countable Γ] in
private theorem support_smul (g : Γ) (x : LabeledOrbitRealization Γ) :
    LabeledOrbitRealization.supportSimplex (g • x) =
      g • LabeledOrbitRealization.supportSimplex x := by
  classical
  apply LabeledOrbitSimplex.ext
  apply Finset.ext
  intro v
  rw [LabeledOrbitRealization.mem_supportSimplex, LabeledOrbitRealization.smul_coordinate]
  change x.val (g⁻¹ • v) ≠ 0 ↔
    v ∈ (LabeledOrbitRealization.supportSimplex x).vertices.image (fun v => g • v)
  constructor
  · intro hv
    exact Finset.mem_image.mpr ⟨g⁻¹ • v,
      (LabeledOrbitRealization.mem_supportSimplex x _).mpr hv, by simp⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    simpa using (LabeledOrbitRealization.mem_supportSimplex x w).mp hw

theorem stage_smul (n : ℕ) {x : LabeledOrbitRealization Γ}
    (hx : x ∈ stage Γ n) (g : Γ) : g • x ∈ stage Γ n := by
  change LabeledOrbitRealization.supportSimplex (g • x) ∈ LabeledOrbitSimplex.exhaustion n
  rw [support_smul]
  exact LabeledOrbitSimplex.orbitFaces_smul hx g

/-- The geometric telescope with stage n occupying heights [n,n+1]. -/
abbrev Model := ClosedStageTelescope.Telescope (stage Γ)

instance : MulAction Γ (Model Γ) where
  smul g p := by
    refine ⟨(g • p.val.1, p.val.2), ?_⟩
    obtain ⟨n, hn, ht⟩ := p.property
    exact ⟨n, stage_smul Γ n hn g, ht⟩
  one_smul p := by
    apply Subtype.ext
    exact Prod.ext (one_smul Γ p.val.1) rfl
  mul_smul g h p := by
    apply Subtype.ext
    exact Prod.ext (mul_smul g h p.val.1) rfl

instance : ContinuousConstSMul Γ (Model Γ) where
  continuous_const_smul g := by
    have hb : Continuous (fun p : Model Γ => g • p.val.1) :=
      (continuous_const_smul g).comp (continuous_fst.comp continuous_subtype_val)
    have ht : Continuous (fun p : Model Γ => p.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (hb.prodMk ht).subtype_mk _

/-- Local compactness follows from the verified closed finite-orbit stages. -/
instance : LocallyCompactSpace (Model Γ) := by
  let (n : ℕ) : LocallyCompactSpace (stage Γ n) := by
    change LocallyCompactSpace
      (LabeledOrbitRealization.OrbitFaceSpace (LabeledOrbitSimplex.exhaustionGenerators n))
    infer_instance
  exact ClosedStageTelescope.locallyCompact (stage Γ) (stage_mono Γ) (stage_isClosed Γ)

instance : SecondCountableTopology (Model Γ) := by
  let (n : ℕ) : SecondCountableTopology (stage Γ n) := by
    change SecondCountableTopology
      (LabeledOrbitRealization.OrbitFaceSpace (LabeledOrbitSimplex.exhaustionGenerators n))
    infer_instance
  exact ClosedStageTelescope.secondCountable (stage Γ) (stage_mono Γ)

/-- Forget the telescope height. -/
def projection : EquivariantMap Γ (Model Γ) (LabeledOrbitRealization Γ) where
  toFun p := p.val.1
  continuous_toFun := ClosedStageTelescope.continuous_projection (stage Γ)
  map_smul' _ _ := rfl

/-- Every realization point occurs at some telescope height. -/
theorem projection_surjective : Function.Surjective (projection Γ) := by
  intro x
  obtain ⟨n, hn⟩ := LabeledOrbitSimplex.mem_exhaustion (LabeledOrbitRealization.supportSimplex x)
  refine ⟨⟨(x, (n : ℝ)), n, hn, le_rfl, ?_⟩, rfl⟩
  exact le_add_of_nonneg_right zero_le_one

section Discrete
variable [TopologicalSpace Γ] [DiscreteTopology Γ]

instance : ContinuousSMul Γ (Model Γ) :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

/-- Properness transfers along the genuine equivariant telescope projection. -/
theorem proper : ProperSMul Γ (Model Γ) := by
  let : ProperSMul Γ (LabeledOrbitRealization Γ) := LabeledOrbitRealization.proper
  exact (projection Γ).properSMul

theorem infinite_fixedPoints_empty (H : Subgroup Γ) [Infinite H] :
    IsEmpty (FixedPointSpace H (Model Γ)) := by
  let : ProperSMul Γ (Model Γ) := proper Γ
  exact fixedPointSpace_isEmpty H

end Discrete
end BC4lean.ProperActions.LabeledOrbitTelescope
