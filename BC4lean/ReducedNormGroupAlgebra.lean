import BC4lean.ReducedGroupCStar

/-! # The group algebra with its reduced norm

A dedicated type synonym keeps this norm separate from possible ℓ¹ norms.
The algebraic operations are precisely those of `GroupAlgebra Γ`.
-/

noncomputable section
namespace BC4lean

variable (Γ : Type*) [Group Γ]

/-- The complex group algebra, reserved for the reduced-norm topology. -/
def ReducedNormGroupAlgebra := GroupAlgebra Γ

namespace ReducedNormGroupAlgebra

instance instRing : Ring (ReducedNormGroupAlgebra Γ) :=
  inferInstanceAs (Ring (GroupAlgebra Γ))
instance instAlgebra : Algebra ℂ (ReducedNormGroupAlgebra Γ) :=
  inferInstanceAs (Algebra ℂ (GroupAlgebra Γ))
instance instStarRing : StarRing (ReducedNormGroupAlgebra Γ) :=
  inferInstanceAs (StarRing (GroupAlgebra Γ))
instance instStarModule : StarModule ℂ (ReducedNormGroupAlgebra Γ) :=
  inferInstanceAs (StarModule ℂ (GroupAlgebra Γ))

/-- Identity on coefficients; only the choice of topological structure changes. -/
def ofGroupAlgebra : GroupAlgebra Γ ≃⋆ₐ[ℂ] ReducedNormGroupAlgebra Γ :=
  StarAlgEquiv.refl ℂ (GroupAlgebra Γ)

def toReduced : ReducedNormGroupAlgebra Γ →⋆ₐ[ℂ] ReducedGroupCStar Γ :=
  integratedToReduced

theorem toReduced_injective : Function.Injective (toReduced Γ) :=
  integratedToReduced_injective

instance instNormedRing : NormedRing (ReducedNormGroupAlgebra Γ) :=
  NormedRing.induced _ _ (toReduced Γ) (toReduced_injective Γ)
instance instNormedAlgebra : NormedAlgebra ℂ (ReducedNormGroupAlgebra Γ) :=
  NormedAlgebra.induced ℂ _ _ (toReduced Γ)

@[simp] theorem norm_ofGroupAlgebra (a : GroupAlgebra Γ) :
    ‖ofGroupAlgebra Γ a‖ = reducedNorm a := rfl

@[simp] theorem norm_toReduced (a : ReducedNormGroupAlgebra Γ) :
    ‖toReduced Γ a‖ = ‖a‖ := rfl

instance instNormedStarGroup : NormedStarGroup (ReducedNormGroupAlgebra Γ) where
  norm_star_le a := by
    change ‖toReduced Γ (star a)‖ ≤ ‖toReduced Γ a‖
    rw [map_star]
    exact (norm_star (toReduced Γ a)).le

instance instCStarRing : CStarRing (ReducedNormGroupAlgebra Γ) where
  norm_mul_self_le a := by
    change ‖toReduced Γ a‖ * ‖toReduced Γ a‖ ≤ ‖toReduced Γ (star a * a)‖
    rw [map_mul, map_star]
    exact CStarRing.norm_star_mul_self.symm.le

theorem toReduced_isometry : Isometry (toReduced Γ) :=
  AddMonoidHomClass.isometry_of_norm (toReduced Γ) (norm_toReduced Γ)

theorem toReduced_denseRange : DenseRange (toReduced Γ) :=
  denseRange_integratedToReduced

end ReducedNormGroupAlgebra
end BC4lean
