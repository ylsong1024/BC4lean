import BC4lean.LabeledPrismProjectionBijective
import BC4lean.LabeledPrismInverseProjection
import BC4lean.LabeledAllowedProducts
import BC4lean.ClosedStageTelescopeCylinders

/-! # The staircase prism realization is the actual geometric telescope -/
noncomputable section
open Set Topology
namespace BC4lean.ProperActions.LabeledPrismProjection
open LabeledOrbitRealization LabeledTelescopePrisms LabeledPrismInverse
variable {Γ : Type*} [Group Γ] [Countable Γ]

def inverse : LabeledOrbitTelescope.Model Γ → PrismRealization (Γ := Γ) :=
  Function.surjInv (projection_bijective (Γ := Γ)).2

@[simp] theorem projection_inverse (p : LabeledOrbitTelescope.Model Γ) :
    projection (inverse p) = p := Function.surjInv_eq (projection_bijective (Γ := Γ)).2 p

@[simp] theorem inverse_projection (x : PrismRealization (Γ := Γ)) :
    inverse (projection x) = x := by
  apply (projection_bijective (Γ := Γ)).1
  exact projection_inverse (projection x)

def cylinderOffset (n : ℕ) (h : Icc (n : ℝ) ((n : ℝ) + 1)) : unitInterval :=
  ⟨h.val - (n : ℝ), by constructor <;> linarith [h.property.1, h.property.2]⟩

omit [Group Γ] [Countable Γ] in
theorem continuous_cylinderOffset (n : ℕ) : Continuous (cylinderOffset n) :=
  (continuous_subtype_val.sub continuous_const).subtype_mk _

private theorem exhaustion_downward (n : ℕ) {s t : LabeledOrbitSimplex Γ}
    (hs : s ∈ LabeledOrbitSimplex.exhaustion n) (ht : t.vertices ⊆ s.vertices) :
    t ∈ LabeledOrbitSimplex.exhaustion n :=
  LabeledOrbitSimplex.orbitFaces_downward hs ht

/-- The global inverse agrees with the explicit inverse on every finite cylinder chart. -/
theorem inverse_cylinder_chart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s ∈ LabeledOrbitSimplex.exhaustion n)
    (p : LabeledSimplexCoordinates Γ s × Icc (n : ℝ) ((n : ℝ) + 1)) :
    inverse (ClosedStageTelescope.cylinder (LabeledOrbitTelescope.stage Γ) n
      (allowedChart (LabeledOrbitSimplex.exhaustion n) (exhaustion_downward n) s hs p.1, p.2)) =
      inverseCylinderChart n s hs (p.1, cylinderOffset n p.2) := by
  apply (projection_bijective (Γ := Γ)).1
  rw [projection_inverse]
  apply Subtype.ext
  rw [projection_inverseCylinderChart]
  apply Prod.ext
  · rfl
  · change p.2.val = (n : ℝ) + (p.2.val - (n : ℝ))
    linarith

/-- Continuity is proved on genuine cylinders and their finite old charts. -/
theorem continuous_inverse : Continuous (inverse (Γ := Γ)) := by
  apply (ClosedStageTelescope.continuous_iff_cylinders
    (LabeledOrbitTelescope.stage Γ) (LabeledOrbitTelescope.stage_isClosed Γ) _).mpr
  intro n
  change Continuous (fun p : AllowedRealization (LabeledOrbitSimplex.exhaustion n) ×
      Icc (n : ℝ) ((n : ℝ) + 1) =>
    inverse (ClosedStageTelescope.cylinder (LabeledOrbitTelescope.stage Γ) n p))
  apply (continuous_allowed_product_iff (LabeledOrbitSimplex.exhaustion n)
    (exhaustion_downward n) _).mpr
  intro s hs
  exact ((continuous_inverseCylinderChart n s hs).comp
    (continuous_fst.prodMk ((continuous_cylinderOffset n).comp continuous_snd))).congr
      (fun p => (inverse_cylinder_chart n s hs p).symm)

/-- Actual homeomorphism, with both directions carrying their proved continuity. -/
def homeomorph : PrismRealization (Γ := Γ) ≃ₜ LabeledOrbitTelescope.Model Γ where
  toFun := projection
  invFun := inverse
  left_inv := inverse_projection
  right_inv := projection_inverse
  continuous_toFun := continuous_projection
  continuous_invFun := continuous_inverse

theorem inverse_smul (g : Γ) (p : LabeledOrbitTelescope.Model Γ) :
    inverse (g • p) = g • inverse p := by
  apply (projection_bijective (Γ := Γ)).1
  rw [projection_inverse, projection_smul, projection_inverse]

end BC4lean.ProperActions.LabeledPrismProjection
