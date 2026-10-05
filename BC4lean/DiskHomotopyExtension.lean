import BC4lean.CylinderBoundary

/-! # Extending prescribed disk endpoint maps and a boundary homotopy -/

noncomputable section
open Metric
open scoped unitInterval

namespace BC4lean.ProperActions

variable {E Y : Type*} [NormedAddCommGroup E] [TopologicalSpace Y]
variable (f₀ f₁ : C(closedBall (0 : E) 1, Y))
variable (H : (f₀.comp sphereInclusion).Homotopy (f₁.comp sphereInclusion))

/-- Values prescribed on the two disk faces and their common cylindrical side. -/
def cylinderBoundaryData : C(CylinderBoundaryPieces E, Y) :=
  ⟨Sum.elim f₀ (Sum.elim f₁ H),
    continuous_sum_dom.mpr ⟨f₀.continuous,
      continuous_sum_dom.mpr ⟨f₁.continuous, H.continuous⟩⟩⟩

private theorem faceZero_side_agree (x : closedBall (0 : E) 1) (p : I × sphere (0 : E) 1)
    (h : cylinderFaceZero x = cylinderSide p) : f₀ x = H p := by
  have ht : (0 : I) = p.1 := signedTime_injective (by
    rw [signedTime_zero]
    exact congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.1) h)
  have hx : x = sphereInclusion p.2 :=
    Subtype.ext (congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.2) h)
  change f₀ x = H (p.1, p.2)
  rw [← ht, H.apply_zero]
  exact congrArg f₀ hx

private theorem faceOne_side_agree (x : closedBall (0 : E) 1) (p : I × sphere (0 : E) 1)
    (h : cylinderFaceOne x = cylinderSide p) : f₁ x = H p := by
  have ht : (1 : I) = p.1 := signedTime_injective (by
    rw [signedTime_one]
    exact congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.1) h)
  have hx : x = sphereInclusion p.2 :=
    Subtype.ext (congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.2) h)
  change f₁ x = H (p.1, p.2)
  rw [← ht, H.apply_one]
  exact congrArg f₁ hx

/-- The endpoint identities are exactly the compatibility conditions for boundary gluing. -/
theorem cylinderBoundaryData_factorsThrough :
    Function.FactorsThrough (cylinderBoundaryData f₀ f₁ H) cylinderBoundaryQuotient := by
  intro p q h
  rcases p with x | x
  · rcases q with y | y
    · exact congrArg f₀ (Subtype.ext (congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.2) h))
    · rcases y with y | y
      · have ht := congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.1) h
        change (-1 : ℝ) = 1 at ht
        norm_num at ht
      · exact faceZero_side_agree f₀ f₁ H x y h
  · rcases x with x | x
    · rcases q with y | y
      · have ht := congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.1) h
        change (1 : ℝ) = -1 at ht
        norm_num at ht
      · rcases y with y | y
        · exact congrArg f₁ (Subtype.ext (congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.2) h))
        · exact faceOne_side_agree f₀ f₁ H x y h
    · rcases q with y | y
      · exact (faceZero_side_agree f₀ f₁ H y x h.symm).symm
      · rcases y with y | y
        · exact (faceOne_side_agree f₀ f₁ H y x h.symm).symm
        · apply congrArg H
          exact Prod.ext
            (signedTime_injective (congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.1) h))
            (Subtype.ext (congrArg (fun z : sphere (0 : ℝ × E) 1 => z.1.2) h))

/-- Glue endpoint maps and a boundary homotopy into a map on the cylinder boundary. -/
def gluedCylinderBoundary [ProperSpace E] : C(sphere (0 : ℝ × E) 1, Y) :=
  cylinderBoundaryQuotient_isQuotientMap.lift (cylinderBoundaryData f₀ f₁ H)
    (cylinderBoundaryData_factorsThrough f₀ f₁ H)

@[simp] theorem gluedCylinderBoundary_on_piece [ProperSpace E] (p : CylinderBoundaryPieces E) :
    gluedCylinderBoundary f₀ f₁ H (cylinderBoundaryQuotient p) =
      cylinderBoundaryData f₀ f₁ H p :=
  ContinuousMap.congr_fun (cylinderBoundaryQuotient_isQuotientMap.lift_comp
    (cylinderBoundaryData f₀ f₁ H) (cylinderBoundaryData_factorsThrough f₀ f₁ H)) p

variable [NormedSpace ℝ E]

/-- Into a contractible target, a sphere homotopy extends over the ball with both endpoints fixed. -/
theorem contractible_extends_ball_homotopy [ProperSpace E] [ContractibleSpace Y] :
    ∃ F : f₀.Homotopy f₁, ∀ t s, F (t, sphereInclusion s) = H (t, s) := by
  obtain ⟨F, hF⟩ := contractible_extends_ball (gluedCylinderBoundary f₀ f₁ H)
  have he (p : CylinderBoundaryPieces E) :
      F (sphereInclusion (cylinderBoundaryQuotient p)) = cylinderBoundaryData f₀ f₁ H p :=
    (ContinuousMap.congr_fun hF (cylinderBoundaryQuotient p)).trans
      (gluedCylinderBoundary_on_piece f₀ f₁ H p)
  refine ⟨{ toContinuousMap := F.comp cylinderBall,
            map_zero_left := ?_, map_one_left := ?_ }, ?_⟩
  · intro x
    change F (cylinderBall (0,x)) = f₀ x
    calc
      F (cylinderBall (0,x)) = F (sphereInclusion (cylinderBoundaryQuotient (Sum.inl x))) := by
        apply congrArg F
        apply Subtype.ext
        exact Prod.ext signedTime_zero rfl
      _ = _ := he (Sum.inl x)
  · intro x
    change F (cylinderBall (1,x)) = f₁ x
    calc
      F (cylinderBall (1,x)) = F (sphereInclusion (cylinderBoundaryQuotient (Sum.inr (Sum.inl x)))) := by
        apply congrArg F
        apply Subtype.ext
        exact Prod.ext signedTime_one rfl
      _ = _ := he (Sum.inr (Sum.inl x))
  · intro t s
    exact he (Sum.inr (Sum.inr (t,s)))

end BC4lean.ProperActions
