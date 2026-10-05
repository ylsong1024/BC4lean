import BC4lean.ProperOrbitCells

/-! # Fixed points of an orbit cell

The parameter has trivial action. Neither subgroup is assumed finite or normal.
-/
namespace BC4lean.ProperActions.OrbitCell
variable {Γ D : Type*} [Group Γ] [TopologicalSpace Γ]
variable [TopologicalSpace D]

/-- Fixed points of an orbit cell split as fixed cosets times the parameter. -/
def fixedSpaceHomeomorph (H K : Subgroup Γ) :
    FixedPointSpace K (OrbitCell H D) ≃ₜ FixedPointSpace K (Γ ⧸ H) × D where
  toFun x := (⟨x.val.1, fun k => congrArg Prod.fst (x.property k)⟩, x.val.2)
  invFun x := ⟨(x.1.val, x.2), fun k => Prod.ext (x.1.property k) rfl⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  continuous_toFun := by
    have hval : Continuous (fun x : FixedPointSpace K (OrbitCell H D) => x.val) :=
      continuous_subtype_val
    exact ((continuous_fst.comp hval).subtype_mk _).prodMk
      (continuous_snd.comp hval)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

@[simp] theorem fixedSpaceHomeomorph_fst (H K : Subgroup Γ)
    (x : FixedPointSpace K (OrbitCell H D)) :
    ((fixedSpaceHomeomorph H K x).1 : Γ ⧸ H) = x.val.1 := rfl

@[simp] theorem fixedSpaceHomeomorph_snd (H K : Subgroup Γ)
    (x : FixedPointSpace K (OrbitCell H D)) :
    (fixedSpaceHomeomorph H K x).2 = x.val.2 := rfl

@[simp] theorem fixedSpaceHomeomorph_symm_coe (H K : Subgroup Γ)
    (x : FixedPointSpace K (Γ ⧸ H) × D) :
    ((fixedSpaceHomeomorph H K).symm x : OrbitCell H D) = (x.1.val, x.2) := rfl

/-- Nonemptiness requires both a fixed coset and a parameter. -/
theorem fixedSpace_nonempty_iff (H K : Subgroup Γ) :
    Nonempty (FixedPointSpace K (OrbitCell H D)) ↔
      Nonempty (FixedPointSpace K (Γ ⧸ H)) ∧ Nonempty D := by
  constructor
  · rintro ⟨x⟩
    exact ⟨⟨(fixedSpaceHomeomorph H K x).1⟩, ⟨(fixedSpaceHomeomorph H K x).2⟩⟩
  · rintro ⟨⟨q⟩, ⟨d⟩⟩
    exact ⟨(fixedSpaceHomeomorph H K).symm (q, d)⟩

/-- Empty fixed cosets give an empty fixed-point cell. -/
theorem fixedSpace_isEmpty_of_cosets (H K : Subgroup Γ)
    [IsEmpty (FixedPointSpace K (Γ ⧸ H))] : IsEmpty (FixedPointSpace K (OrbitCell H D)) :=
  ⟨fun x => isEmptyElim (fixedSpaceHomeomorph H K x).1⟩

/-- An empty parameter gives an empty fixed-point cell. -/
theorem fixedSpace_isEmpty_of_parameter (H K : Subgroup Γ) [IsEmpty D] :
    IsEmpty (FixedPointSpace K (OrbitCell H D)) :=
  ⟨fun x => isEmptyElim (fixedSpaceHomeomorph H K x).2⟩
end BC4lean.ProperActions.OrbitCell
