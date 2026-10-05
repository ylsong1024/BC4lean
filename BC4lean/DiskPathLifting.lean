import BC4lean.DiskHomotopyExtension

/-! # Path lifting across the standard disk boundary inclusion -/

noncomputable section
open scoped unitInterval

namespace BC4lean.ProperActions

universe u

/-- A prescribed boundary homotopy extends over a standard disk, with endpoints unchanged. -/
theorem contractible_extends_disk_homotopy {Y : Type*} [TopologicalSpace Y]
    [ContractibleSpace Y] (n : ℕ) (f₀ f₁ : C(TopCat.disk.{u} n, Y))
    (H : (f₀.comp (TopCat.diskBoundaryInclusion n).hom).Homotopy
      (f₁.comp (TopCat.diskBoundaryInclusion n).hom)) :
    ∃ F : f₀.Homotopy f₁, ∀ t s, F (t, (TopCat.diskBoundaryInclusion n) s) = H (t,s) := by
  let b : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, TopCat.disk.{u} n) :=
    ⟨ULift.up, continuous_uliftUp⟩
  let s : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, TopCat.diskBoundary.{u} n) :=
    ⟨ULift.up, continuous_uliftUp⟩
  let h : ((f₀.comp b).comp sphereInclusion).Homotopy ((f₁.comp b).comp sphereInclusion) :=
    H.compContinuousMap s
  obtain ⟨F, hF⟩ := contractible_extends_ball_homotopy (f₀.comp b) (f₁.comp b) h
  let d : C(TopCat.disk.{u} n, Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ⟨ULift.down, continuous_uliftDown⟩
  exact ⟨F.compContinuousMap d, fun t x => hF t x.down⟩

/-- Endpoint-preserving extension of a continuous family of boundary paths. -/
theorem contractible_disk_path_lifting {Y : Type*} [TopologicalSpace Y]
    [ContractibleSpace Y] (n : ℕ)
    (a : C(TopCat.diskBoundary.{u} n, C(I,Y))) (f₀ f₁ : C(TopCat.disk.{u} n, Y))
    (h₀ : ∀ s, a s 0 = f₀ ((TopCat.diskBoundaryInclusion n) s))
    (h₁ : ∀ s, a s 1 = f₁ ((TopCat.diskBoundaryInclusion n) s)) :
    ∃ F : C(TopCat.disk.{u} n, C(I,Y)),
      (∀ s, F ((TopCat.diskBoundaryInclusion n) s) = a s) ∧
      (∀ x, F x 0 = f₀ x) ∧ (∀ x, F x 1 = f₁ x) := by
  let H : (f₀.comp (TopCat.diskBoundaryInclusion n).hom).Homotopy
      (f₁.comp (TopCat.diskBoundaryInclusion n).hom) :=
    { toContinuousMap := a.uncurry.comp ContinuousMap.prodSwap,
      map_zero_left := h₀, map_one_left := h₁ }
  obtain ⟨G, hG⟩ := contractible_extends_disk_homotopy n f₀ f₁ H
  refine ⟨(G.toContinuousMap.comp ContinuousMap.prodSwap).curry, ?_, ?_, ?_⟩
  · intro s
    exact ContinuousMap.ext (fun t => hG t s)
  · exact G.apply_zero
  · exact G.apply_one

end BC4lean.ProperActions
