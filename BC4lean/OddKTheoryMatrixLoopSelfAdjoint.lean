import BC4lean.OddKTheoryMatrixLoopPullback

/-! # Selfadjointness of the actual matrix-unitary periodic pullback

The scalar periodic coefficients have exact adjoint symmetries. Genuine
circle CFC and the actual coordinatewise matrix action preserve those
symmetries. Actual signed row-coordinate operators commute with each
coordinatewise coefficient action, so finite reindexing of the two sums
proves the evaluated bounded infinite-row operator selfadjoint.
-/

noncomputable section
namespace BC4lean.KKTheory

section FixedOperators

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

theorem oddKTheoryRowLoopFixedPermutation_diagonal_commute
    (i : Fin 4) (S : AdjointableMap B E E) :
    Commute (oddKTheoryRowLoopFixedPermutation i) (countableModuleDiagonal S) := by
  fin_cases i
  · exact Commute.one_left _
  · exact oddKTheoryRowReflection_diagonal_commute 0 S
  · exact oddKTheoryRowReflection_diagonal_commute (-1) S
  · exact (oddKTheoryRowReflection_diagonal_commute 0 S).mul_left
      (oddKTheoryRowReflection_diagonal_commute (-1) S)

theorem oddKTheoryRowLoopFixedPermutation_star_diagonal_commute
    (i : Fin 4) (S : AdjointableMap B E E) :
    Commute (star (oddKTheoryRowLoopFixedPermutation i)) (countableModuleDiagonal S) := by
  fin_cases i
  · change Commute (star (1 : OddKTheoryCountableOperator B E)) (countableModuleDiagonal S)
    rw [star_one]
    exact Commute.one_left _
  · change Commute (star (oddKTheoryRowReflectionOperator (B := B) (E := E) 0))
      (countableModuleDiagonal S)
    rw [oddKTheoryRowReflectionOperator_star]
    exact oddKTheoryRowReflection_diagonal_commute 0 S
  · change Commute (star (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1)))
      (countableModuleDiagonal S)
    rw [oddKTheoryRowReflectionOperator_star]
    exact oddKTheoryRowReflection_diagonal_commute (-1) S
  · change Commute (star (oddKTheoryRowReflectionOperator (B := B) (E := E) 0 *
      oddKTheoryRowReflectionOperator (-1))) (countableModuleDiagonal S)
    simp only [star_mul, oddKTheoryRowReflectionOperator_star]
    exact (oddKTheoryRowReflection_diagonal_commute (-1) S).mul_left
      (oddKTheoryRowReflection_diagonal_commute 0 S)

theorem oddKTheoryRowLoopFixedOperator_diagonal_commute
    (p : Fin 4 × Fin 4) (S : AdjointableMap B E E) :
    Commute (oddKTheoryRowLoopFixedOperator p) (countableModuleDiagonal S) :=
  ((oddKTheoryRowLoopFixedPermutation_star_diagonal_commute p.1 S).mul_left
    (oddKTheoryRowSign_diagonal_commute S)).mul_left
      (oddKTheoryRowLoopFixedPermutation_diagonal_commute p.2 S)

theorem oddKTheoryRowLoopFixedFiniteOperator_diagonal_commute
    (i : Fin 4) (S : AdjointableMap B E E) :
    Commute (oddKTheoryRowLoopFixedFiniteOperator i) (countableModuleDiagonal S) := by
  fin_cases i
  · exact oddKTheoryRowZeroProjection_diagonal_commute S
  · exact (oddKTheoryRowZeroProjection_diagonal_commute S).mul_left
      (oddKTheoryRowReflection_diagonal_commute (-1) S)
  · exact (oddKTheoryRowReflection_diagonal_commute (-1) S).mul_left
      (oddKTheoryRowZeroProjection_diagonal_commute S)
  · exact ((oddKTheoryRowReflection_diagonal_commute (-1) S).mul_left
      (oddKTheoryRowZeroProjection_diagonal_commute S)).mul_left
      (oddKTheoryRowReflection_diagonal_commute (-1) S)

omit [CompleteSpace E] in
theorem oddKTheoryRowLoopFixedOperator_star [CompleteSpace E] (p : Fin 4 × Fin 4) :
    star (oddKTheoryRowLoopFixedOperator (B := B) (E := E) p) =
      oddKTheoryRowLoopFixedOperator p.swap := by
  simp only [oddKTheoryRowLoopFixedOperator, Prod.swap,
    star_mul, star_star, oddKTheoryRowSignOperator_star, mul_assoc]

theorem oddKTheoryRowLoopFixedFiniteOperator_star (i : Fin 4) :
    star (oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := E) i) =
      oddKTheoryRowLoopFixedFiniteOperator (oddKTheoryFiniteEntryAdjoint i) := by
  fin_cases i
  · change star (oddKTheoryRowZeroProjection (B := B) (E := E)) = oddKTheoryRowZeroProjection
    exact oddKTheoryRowZeroProjection_star
  · change star (oddKTheoryRowZeroProjection (B := B) (E := E) *
      oddKTheoryRowReflectionOperator (-1)) =
      oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection
    rw [star_mul, oddKTheoryRowReflectionOperator_star, oddKTheoryRowZeroProjection_star]
  · change star (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1) *
      oddKTheoryRowZeroProjection) =
      oddKTheoryRowZeroProjection * oddKTheoryRowReflectionOperator (-1)
    rw [star_mul, oddKTheoryRowZeroProjection_star, oddKTheoryRowReflectionOperator_star]
  · change star (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1) *
      oddKTheoryRowZeroProjection * oddKTheoryRowReflectionOperator (-1)) =
      oddKTheoryRowReflectionOperator (-1) * oddKTheoryRowZeroProjection *
        oddKTheoryRowReflectionOperator (-1)
    simp only [star_mul, oddKTheoryRowZeroProjection_star, oddKTheoryRowReflectionOperator_star]
    exact (mul_assoc _ _ _).symm

end FixedOperators

private theorem oddKTheoryFourPair_sum_swap {R : Type*} [AddCommMonoid R]
    (f : Fin 4 × Fin 4 → R) :
    (∑ p : Fin 4 × Fin 4, f p.swap) = ∑ p : Fin 4 × Fin 4, f p :=
  (Equiv.prodComm (Fin 4) (Fin 4)).sum_comp f

private theorem oddKTheoryFourEntry_sum_adjoint {R : Type*} [AddCommMonoid R]
    (f : Fin 4 → R) :
    (∑ i : Fin 4, f (oddKTheoryFiniteEntryAdjoint i)) = ∑ i : Fin 4, f i :=
  oddKTheoryFiniteEntryAdjoint.sum_comp f

section MatrixPullback

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

theorem oddKTheoryMatrixCircleCoefficient_star
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (f : C(Circle, ℂ)) :
    star (oddKTheoryMatrixCircleCoefficient u f) = oddKTheoryMatrixCircleCoefficient u (star f) := by
  rw [oddKTheoryMatrixCircleCoefficient, ← map_star, ← map_star]
  rfl

private theorem oddKTheoryMatrixLoopResidualTerm_star
    {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [Fintype ι] [DecidableEq ι]
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (p : Fin 4 × Fin 4) :
    star (oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p) *
      oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p) =
      oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p.swap) *
        oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p.swap := by
  rw [star_mul, oddKTheoryMatrixCircleCoefficient_star,
    oddKTheoryLoopResidualCircleCoefficient_star, oddKTheoryRowLoopFixedOperator_star]
  let S : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) :=
    unitizedModuleMatrixRepresentation
      (oddKTheoryCircleCFC u (oddKTheoryLoopResidualCircleCoefficient p.swap))
  change oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p.swap *
    countableModuleDiagonal S = countableModuleDiagonal S * oddKTheoryRowLoopFixedOperator p.swap
  have hc : Commute
      (oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p.swap)
      (countableModuleDiagonal S) :=
    oddKTheoryRowLoopFixedOperator_diagonal_commute (B := B) (E := FiniteStandardModule B ι)
      p.swap S
  exact hc.eq

set_option maxHeartbeats 7200000 in
private theorem oddKTheoryMatrixLoopResidualSum_star
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    star (∑ p : Fin 4 × Fin 4,
      oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p) *
        oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p) =
      ∑ p : Fin 4 × Fin 4,
        oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p) *
          oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p := by
  rw [star_sum]
  calc
    _ = ∑ p : Fin 4 × Fin 4,
        oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p.swap) *
          oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p.swap := by
      apply Finset.sum_congr rfl
      intro p _
      exact oddKTheoryMatrixLoopResidualTerm_star (B := B) (ι := ι) u p
    _ = _ := oddKTheoryFourPair_sum_swap (fun p : Fin 4 × Fin 4 =>
      oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p) *
        oddKTheoryRowLoopFixedOperator (B := B) (E := FiniteStandardModule B ι) p)

private theorem oddKTheoryMatrixLoopFiniteSum_star
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    star (∑ i : Fin 4,
      oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i) *
        oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) i) =
      ∑ i : Fin 4,
        oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i) *
          oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) i := by
  let finite : Fin 4 → OddKTheoryMatrixRowOperator B ι := fun i =>
    oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i) *
      oddKTheoryRowLoopFixedFiniteOperator i
  let rowAdd : AddCommMonoid (OddKTheoryMatrixRowOperator B ι) := inferInstance
  have hfiniteReindex : (∑ i : Fin 4, finite (oddKTheoryFiniteEntryAdjoint i)) =
      ∑ i : Fin 4, finite i :=
    @oddKTheoryFourEntry_sum_adjoint (OddKTheoryMatrixRowOperator B ι) rowAdd finite
  change star (∑ i : Fin 4, finite i) = ∑ i : Fin 4, finite i
  calc
    _ = ∑ i, finite (oddKTheoryFiniteEntryAdjoint i) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [finite]
      rw [star_mul, oddKTheoryMatrixCircleCoefficient_star,
        oddKTheoryLoopFiniteCircleCoefficient_star, oddKTheoryRowLoopFixedFiniteOperator_star]
      let S : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) :=
        unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u
          (oddKTheoryLoopFiniteCircleCoefficient (oddKTheoryFiniteEntryAdjoint i)))
      change oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι)
        (oddKTheoryFiniteEntryAdjoint i) * countableModuleDiagonal S =
        countableModuleDiagonal S * oddKTheoryRowLoopFixedFiniteOperator (oddKTheoryFiniteEntryAdjoint i)
      have hc : Commute
          (oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι)
            (oddKTheoryFiniteEntryAdjoint i)) (countableModuleDiagonal S) :=
        oddKTheoryRowLoopFixedFiniteOperator_diagonal_commute (B := B) (E := FiniteStandardModule B ι)
          (oddKTheoryFiniteEntryAdjoint i) S
      exact hc.eq
    _ = _ := hfiniteReindex

set_option maxHeartbeats 3600000 in
/-- The actual bounded matrix-unitary pullback is selfadjoint, proved by the
actual coefficient action and row-coordinate operators. -/
theorem oddKTheoryMatrixLoopPullback_isSelfAdjoint
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    IsSelfAdjoint (oddKTheoryMatrixLoopPullback u) := by
  let residual : Fin 4 × Fin 4 → OddKTheoryMatrixRowOperator B ι := fun p =>
    oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopResidualCircleCoefficient p) *
      oddKTheoryRowLoopFixedOperator p
  let finite : Fin 4 → OddKTheoryMatrixRowOperator B ι := fun i =>
    oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopFiniteCircleCoefficient i) *
      oddKTheoryRowLoopFixedFiniteOperator i
  have hresidual : star (∑ p, residual p) = ∑ p, residual p :=
    oddKTheoryMatrixLoopResidualSum_star (B := B) (ι := ι) u
  have hfinite : star (∑ i, finite i) = ∑ i, finite i :=
    oddKTheoryMatrixLoopFiniteSum_star (B := B) (ι := ι) u
  have hsign : star (oddKTheoryMatrixCircleCoefficient u oddKTheoryLoopSignCircleCoefficient *
      oddKTheoryRowSignOperator) =
      oddKTheoryMatrixCircleCoefficient u oddKTheoryLoopSignCircleCoefficient *
        oddKTheoryRowSignOperator := by
    rw [star_mul, oddKTheoryMatrixCircleCoefficient_star,
      oddKTheoryLoopSignCircleCoefficient_star, oddKTheoryRowSignOperator_star]
    exact (oddKTheoryRowSign_diagonal_commute
      (unitizedModuleMatrixRepresentation (oddKTheoryCircleCFC u oddKTheoryLoopSignCircleCoefficient))).eq
  change star ((∑ p, residual p) +
    oddKTheoryMatrixCircleCoefficient u oddKTheoryLoopSignCircleCoefficient *
      oddKTheoryRowSignOperator + ∑ i, finite i) = _
  rw [star_add, star_add, hresidual, hsign, hfinite]
  rfl

end MatrixPullback
end BC4lean.KKTheory
