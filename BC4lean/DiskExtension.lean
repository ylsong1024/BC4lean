import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Extension from the boundary of a disk

A null-homotopic map from a unit sphere extends over the closed unit ball.
The proof descends the null-homotopy through the radial quotient map.
-/

noncomputable section

open Metric
open scoped unitInterval

namespace BC4lean.ProperActions

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Inclusion of the unit sphere into the closed unit ball. -/
def sphereInclusion : C(sphere (0 : E) 1, closedBall (0 : E) 1) :=
  ⟨fun x => ⟨x.1, le_of_eq x.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The radial map from the cylinder on the unit sphere to the unit ball. -/
def radialMap : C(I × sphere (0 : E) 1, closedBall (0 : E) 1) := by
  refine ⟨fun p => ⟨(p.1 : ℝ) • p.2.1, ?_⟩, ?_⟩
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg p.1.2.1, norm_eq_of_mem_sphere, mul_one]
    exact p.1.2.2
  · exact ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The radial coordinate is recovered by taking the norm. -/
theorem radialMap_norm (p : I × sphere (0 : E) 1) :
    ‖(radialMap p : E)‖ = (p.1 : ℝ) := by
  have hs : ‖p.2.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using p.2.2
  simp [radialMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.2.1, hs]

/-- If the sphere is nonempty, every point of the ball has radial coordinates. -/
theorem radialMap_surjective [Nonempty (sphere (0 : E) 1)] :
    Function.Surjective (radialMap (E := E)) := by
  intro x
  by_cases hx : x.1 = 0
  · obtain ⟨s⟩ := ‹Nonempty (sphere (0 : E) 1)›
    exact ⟨(0, s), Subtype.ext (by simp [radialMap, hx])⟩
  · have hn : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let s : sphere (0 : E) 1 := ⟨‖x.1‖⁻¹ • x.1, by
      simp [norm_smul, hn]⟩
    refine ⟨(⟨‖x.1‖, norm_nonneg _, by simpa only [mem_closedBall, dist_zero_right] using x.2⟩, s), ?_⟩
    apply Subtype.ext
    change ‖x.1‖ • (‖x.1‖⁻¹ • x.1) = x.1
    simp [smul_smul, hn]

/-- The radial cylinder is a quotient presentation of the ball. -/
theorem radialMap_isQuotientMap [ProperSpace E] [Nonempty (sphere (0 : E) 1)] :
    Topology.IsQuotientMap (radialMap (E := E)) :=
  .of_surjective_continuous radialMap_surjective radialMap.continuous

variable {Y : Type*} [TopologicalSpace Y]

/-- A homotopy starting at a constant is constant on the radial fibers. -/
theorem homotopy_factorsThrough_radialMap {y : Y} {f : C(sphere (0 : E) 1, Y)}
    (H : (ContinuousMap.const _ y).Homotopy f) :
    Function.FactorsThrough H (radialMap (E := E)) := by
  intro p q hpq
  have ht : p.1 = q.1 := Subtype.ext (by
    simpa only [radialMap_norm] using congrArg (fun x : closedBall (0 : E) 1 => ‖x.1‖) hpq)
  by_cases hzero : p.1 = 0
  · have hzq : q.1 = 0 := ht.symm.trans hzero
    change H (p.1, p.2) = H (q.1, q.2)
    rw [hzero, hzq, H.apply_zero, H.apply_zero]
    rfl
  · have hn : (p.1 : ℝ) ≠ 0 := fun h => hzero (Subtype.ext h)
    have hs : p.2 = q.2 := by
      apply Subtype.ext
      have h := congrArg (fun x : closedBall (0 : E) 1 => x.1) hpq
      change (p.1 : ℝ) • p.2.1 = (q.1 : ℝ) • q.2.1 at h
      rw [← ht] at h
      exact (smul_right_injective E hn) h
    exact congrArg H (Prod.ext ht hs)

/-- A null-homotopic sphere map extends over the closed ball. -/
theorem nullhomotopic_extends_ball [ProperSpace E]
    (f : C(sphere (0 : E) 1, Y)) (hf : f.Nullhomotopic) :
    ∃ F : C(closedBall (0 : E) 1, Y), F.comp sphereInclusion = f := by
  classical
  obtain ⟨y, ⟨H⟩⟩ := hf
  cases isEmpty_or_nonempty (sphere (0 : E) 1) with
  | inl h =>
    exact ⟨ContinuousMap.const _ y, ContinuousMap.ext (fun x => isEmptyElim x)⟩
  | inr h =>
    let q := radialMap_isQuotientMap (E := E)
    let F := q.lift H.symm.toContinuousMap (homotopy_factorsThrough_radialMap H.symm)
    refine ⟨F, ContinuousMap.ext fun s => ?_⟩
    have h := ContinuousMap.congr_fun (q.lift_comp H.symm.toContinuousMap
      (homotopy_factorsThrough_radialMap H.symm)) (1, s)
    change F (radialMap (1, s)) = H.symm (1, s) at h
    rw [H.symm.apply_one] at h
    have he : radialMap (1, s) = sphereInclusion s := Subtype.ext (one_smul ℝ s.1)
    rw [he] at h
    exact h

/-- Every sphere map into a contractible space extends over the ball. -/
theorem contractible_extends_ball [ProperSpace E] [ContractibleSpace Y]
    (f : C(sphere (0 : E) 1, Y)) :
    ∃ F : C(closedBall (0 : E) 1, Y), F.comp sphereInclusion = f := by
  apply nullhomotopic_extends_ball f
  simpa using (id_nullhomotopic Y).comp_left f

/-- Every map from the boundary of a Euclidean disk into a contractible space extends. -/
theorem contractible_extends_disk {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]
    (n : ℕ) (f : C(TopCat.diskBoundary.{u} n, Y)) :
    ∃ F : C(TopCat.disk.{u} n, Y), F.comp (TopCat.diskBoundaryInclusion n).hom = f := by
  let s : TopCat.diskBoundary.{u} n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Homeomorph.ulift
  let d : TopCat.disk.{u} n ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Homeomorph.ulift
  obtain ⟨F, hF⟩ := contractible_extends_ball (f.comp ⟨s.symm, s.symm.continuous⟩)
  refine ⟨F.comp ⟨d, d.continuous⟩, ContinuousMap.ext fun x => ?_⟩
  exact ContinuousMap.congr_fun hF x.down

end BC4lean.ProperActions
