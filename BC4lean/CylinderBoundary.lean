import BC4lean.DiskExtension

/-! # A quotient presentation of the boundary of a disk cylinder

The product norm on ℝ × E is the max norm. Its unit sphere consists of the
two disk faces and the cylinder on the unit sphere of E.
-/

noncomputable section
open Metric
open scoped unitInterval

namespace BC4lean.ProperActions

variable {E : Type*} [NormedAddCommGroup E]

/-- Affine coordinate identifying the unit interval with [-1,1]. -/
def signedTime (t : I) : ℝ := 2 * (t : ℝ) - 1

@[simp] theorem signedTime_zero : signedTime 0 = -1 := by norm_num [signedTime]
@[simp] theorem signedTime_one : signedTime 1 = 1 := by norm_num [signedTime]

theorem abs_signedTime_le (t : I) : |signedTime t| ≤ 1 := by
  rw [abs_le]
  have h := t.2
  dsimp [signedTime]
  constructor <;> linarith [h.1, h.2]

theorem signedTime_injective : Function.Injective signedTime := by
  intro t u h
  apply Subtype.ext
  dsimp [signedTime] at h
  linarith

/-- The cylinder parametrized as the max-norm ball. -/
def cylinderBall : C(I × closedBall (0 : E) 1, closedBall (0 : ℝ × E) 1) := by
  refine ⟨fun p => ⟨(signedTime p.1, p.2.1), ?_⟩, ?_⟩
  · rw [mem_closedBall, dist_zero_right, Prod.norm_mk, Real.norm_eq_abs, max_le_iff]
    exact ⟨abs_signedTime_le _, by simpa only [mem_closedBall, dist_zero_right] using p.2.2⟩
  · exact (((continuous_subtype_val.comp continuous_fst).const_mul 2 |>.sub continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The lower disk face of the cylinder boundary. -/
def cylinderFaceZero : C(closedBall (0 : E) 1, sphere (0 : ℝ × E) 1) := by
  refine ⟨fun x => ⟨(-1, x.1), ?_⟩, ?_⟩
  · have hx : ‖x.1‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using x.2
    simp only [mem_sphere, dist_zero_right, Prod.norm_mk, norm_neg, norm_one, max_eq_left hx]
  · exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- The upper disk face of the cylinder boundary. -/
def cylinderFaceOne : C(closedBall (0 : E) 1, sphere (0 : ℝ × E) 1) := by
  refine ⟨fun x => ⟨(1, x.1), ?_⟩, ?_⟩
  · have hx : ‖x.1‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using x.2
    simp only [mem_sphere, dist_zero_right, Prod.norm_mk, norm_one, max_eq_left hx]
  · exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- The cylindrical side of the boundary. -/
def cylinderSide : C(I × sphere (0 : E) 1, sphere (0 : ℝ × E) 1) := by
  refine ⟨fun p => ⟨(signedTime p.1, p.2.1), ?_⟩, ?_⟩
  · simp only [mem_sphere, dist_zero_right, Prod.norm_mk, Real.norm_eq_abs,
      norm_eq_of_mem_sphere, max_eq_right (abs_signedTime_le p.1)]
  · exact (((continuous_subtype_val.comp continuous_fst).const_mul 2 |>.sub continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- Disjoint union of the two faces and the cylindrical side. -/
abbrev CylinderBoundaryPieces (E : Type*) [NormedAddCommGroup E] :=
  closedBall (0 : E) 1 ⊕ (closedBall (0 : E) 1 ⊕ (I × sphere (0 : E) 1))

/-- Glue the three boundary pieces into the max-norm unit sphere. -/
def cylinderBoundaryQuotient : C(CylinderBoundaryPieces E, sphere (0 : ℝ × E) 1) :=
  ⟨Sum.elim cylinderFaceZero (Sum.elim cylinderFaceOne cylinderSide),
    continuous_sum_dom.mpr ⟨cylinderFaceZero.continuous,
      continuous_sum_dom.mpr ⟨cylinderFaceOne.continuous, cylinderSide.continuous⟩⟩⟩

/-- The three pieces cover the sphere, including in dimension zero. -/
theorem cylinderBoundaryQuotient_surjective :
    Function.Surjective (cylinderBoundaryQuotient (E := E)) := by
  intro x
  have hx : max |x.1.1| ‖x.1.2‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using x.2
  have hb : ‖x.1.2‖ ≤ 1 := (le_max_right _ _).trans (le_of_eq hx)
  let b : closedBall (0 : E) 1 := ⟨x.1.2, by simpa only [mem_closedBall, dist_zero_right] using hb⟩
  by_cases h0 : x.1.1 = -1
  · exact ⟨Sum.inl b, Subtype.ext (Prod.ext h0.symm rfl)⟩
  by_cases h1 : x.1.1 = 1
  · exact ⟨Sum.inr (Sum.inl b), Subtype.ext (Prod.ext h1.symm rfl)⟩
  have hr : |x.1.1| ≤ 1 := (le_max_left _ _).trans (le_of_eq hx)
  have hn : ‖x.1.2‖ = 1 := by
    rcases max_eq_iff.mp hx with h | h
    · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h.1 with h | h
      · exact False.elim (h1 h)
      · exact False.elim (h0 h)
    · exact h.1
  let t : I := ⟨(x.1.1 + 1) / 2, by constructor <;> linarith [abs_le.mp hr]⟩
  let s : sphere (0 : E) 1 := ⟨x.1.2, by simpa only [mem_sphere, dist_zero_right] using hn⟩
  refine ⟨Sum.inr (Sum.inr (t,s)), Subtype.ext (Prod.ext ?_ rfl)⟩
  change 2 * ((x.1.1 + 1) / 2) - 1 = x.1.1
  ring

/-- Compactness of the pieces makes the boundary presentation a quotient map. -/
theorem cylinderBoundaryQuotient_isQuotientMap [ProperSpace E] :
    Topology.IsQuotientMap (cylinderBoundaryQuotient (E := E)) :=
  .of_surjective_continuous cylinderBoundaryQuotient_surjective cylinderBoundaryQuotient.continuous

end BC4lean.ProperActions
