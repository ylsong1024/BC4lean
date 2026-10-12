import BC4lean.OddKTheoryMatrixLoopSelfAdjoint

/-! # Finite signed-coordinate identities and actual coefficient transfer

A finite operator formula has genuine row entries in any common continuous
coefficient algebra, including the unit circle and the spectrum of a selfadjoint operator. Equality of those entries transfers through a unital
star algebra action on the actual row module. The argument uses completed
coordinate evaluations and finite sums; it uses no tensor identification and
no compactness assertion for a coordinate projection.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [finiteEntryStarOrderedB : StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [finiteEntryCompleteE : CompleteSpace E]

/-- Actual completed row evaluation in integer coordinates. -/
def oddKTheoryRowIntegerEvaluation (n : ℤ) :
    AdjointableMap B (CountableHilbertModuleSum B E) E :=
  countableModuleEvaluation (B := B) (E := E) (oddKTheoryRowIntegerIndex n)

@[simp] theorem oddKTheoryRowIntegerEvaluation_inclusion (n m : ℤ) (b : E) :
    oddKTheoryRowIntegerEvaluation (B := B) (E := E) n
      (oddKTheoryRowIntegerInclusion (B := B) (E := E) m b) =
      if m = n then b else 0 := by
  simp only [oddKTheoryRowIntegerEvaluation, oddKTheoryRowIntegerInclusion,
    countableModuleEvaluation_inclusion]
  by_cases h : m = n
  · subst m
    simp only [if_true]
  · have hn : oddKTheoryRowIntegerIndex m ≠ oddKTheoryRowIntegerIndex n :=
      fun he => h (Equiv.intEquivNat.injective he)
    simp only [if_neg hn, if_neg h]

/-- Coordinate separation also holds for the genuine integer indexing. -/
theorem oddKTheoryRowVector_ext_integerEvaluations
    (x y : CountableHilbertModuleSum B E)
    (h : ∀ n, oddKTheoryRowIntegerEvaluation n x = oddKTheoryRowIntegerEvaluation n y) : x = y := by
  apply countableModule_ext_eval
  intro k
  obtain ⟨n, rfl⟩ := Equiv.intEquivNat.surjective k
  exact h n

section SumApplication

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E']
  [CStarModule Bᵐᵒᵖ E']

omit finiteEntryStarOrderedB finiteEntryCompleteE in
/-- Application of finite actual adjointable sums is a finite vector sum. -/
theorem oddKTheoryAdjointable_sum_apply [StarOrderedRing B] [CompleteSpace E]
    {κ : Type*} (s : Finset κ)
    (T : κ → AdjointableMap B E E') (x : E) :
    (∑ i ∈ s, T i) x = ∑ i ∈ s, T i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, AdjointableMap.coe_add_apply, ih]

end SumApplication

variable {X : Type*} [TopologicalSpace X]
variable {κ «λ» : Type*} [Fintype κ] [Fintype «λ»]

/-- The common circle entry of a finite signed-coordinate formula. -/
def oddKTheoryFiniteCircleEntry (f : κ → C(X, ℂ))
    (target : κ → ℤ → ℤ) (weight : κ → ℤ → ℂ) (n m : ℤ) : C(X, ℂ) :=
  ∑ i, if target i m = n then weight i m • f i else 0

/-- The genuine bounded completed-module formula obtained from the finite
circle coefficients and actual fixed coordinate operators. -/
def oddKTheoryFiniteRowFormula (φ : C(X, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (f : κ → C(X, ℂ)) (A : κ → OddKTheoryCountableOperator B E) :
    OddKTheoryCountableOperator B E :=
  ∑ i, countableModuleDiagonal (φ (f i)) * A i

/-- Actual evaluation of a finite formula is evaluation of its common
circle entry through the genuine row coefficient action. -/
theorem oddKTheoryFiniteRowFormula_entry
    (φ : C(X, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (f : κ → C(X, ℂ)) (A : κ → OddKTheoryCountableOperator B E)
    (target : κ → ℤ → ℤ) (weight : κ → ℤ → ℂ)
    (hA : ∀ i m (b : E), A i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (target i m) (weight i m • b))
    (n m : ℤ) (b : E) :
    oddKTheoryRowIntegerEvaluation n
      (oddKTheoryFiniteRowFormula φ f A (oddKTheoryRowIntegerInclusion m b)) =
        φ (oddKTheoryFiniteCircleEntry f target weight n m) b := by
  classical
  unfold oddKTheoryFiniteRowFormula oddKTheoryFiniteCircleEntry
  rw [oddKTheoryAdjointable_sum_apply, map_sum (oddKTheoryRowIntegerEvaluation n).toCLM,
    map_sum, oddKTheoryAdjointable_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [AdjointableMap.mul_apply, hA, oddKTheoryRowDiagonal_integerInclusion,
    oddKTheoryRowIntegerEvaluation_inclusion]
  by_cases h : target i m = n
  · rw [if_pos h, if_pos h]
    rw [map_smul φ (weight i m) (f i), AdjointableMap.coe_smul_apply]
    exact (φ (f i)).toCLM.map_smul (weight i m) b
  · simp only [if_neg h, map_zero, AdjointableMap.coe_zero_apply]

/-- Every pointwise scalar entry identity transfers to the actual completed
row module through its genuine circle coefficient action. -/
theorem oddKTheoryFiniteRowFormula_transfer
    (φ : C(X, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (f : κ → C(X, ℂ)) (A : κ → OddKTheoryCountableOperator B E)
    (target : κ → ℤ → ℤ) (weight : κ → ℤ → ℂ)
    (hA : ∀ i m (b : E), A i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (target i m) (weight i m • b))
    (g : «λ» → C(X, ℂ)) (C : «λ» → OddKTheoryCountableOperator B E)
    (target' : «λ» → ℤ → ℤ) (weight' : «λ» → ℤ → ℂ)
    (hC : ∀ i m (b : E), C i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (target' i m) (weight' i m • b))
    (hentries : ∀ n m, oddKTheoryFiniteCircleEntry f target weight n m =
      oddKTheoryFiniteCircleEntry g target' weight' n m) :
    oddKTheoryFiniteRowFormula φ f A = oddKTheoryFiniteRowFormula φ g C := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro m b
  apply oddKTheoryRowVector_ext_integerEvaluations
  intro n
  rw [oddKTheoryFiniteRowFormula_entry φ f A target weight hA,
    oddKTheoryFiniteRowFormula_entry φ g C target' weight' hC, hentries]

/-- Multiplication of two finite signed-coordinate terms has an actual
coordinate rule, including terms whose scalar weight is zero. -/
theorem oddKTheoryRowCoordinateRule_mul
    (A C : OddKTheoryCountableOperator B E) (target target' : ℤ → ℤ)
    (weight weight' : ℤ → ℂ)
    (hA : ∀ m (b : E), A (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (target m) (weight m • b))
    (hC : ∀ m (b : E), C (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (target' m) (weight' m • b))
    (m : ℤ) (b : E) :
    (A * C) (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (target (target' m))
        ((weight (target' m) * weight' m) • b) := by
  rw [AdjointableMap.mul_apply, hC, hA, smul_smul]

/-- The square of a finite formula has a finite product formula when its
actual fixed operators commute with the actual row coefficient action. -/
theorem oddKTheoryFiniteRowFormula_square
    (φ : C(X, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (f : κ → C(X, ℂ)) (A : κ → OddKTheoryCountableOperator B E)
    (hcomm : ∀ i j, Commute (A i) (countableModuleDiagonal (φ (f j)))) :
    oddKTheoryFiniteRowFormula φ f A * oddKTheoryFiniteRowFormula φ f A =
      oddKTheoryFiniteRowFormula φ (fun p : κ × κ => f p.1 * f p.2)
        (fun p => A p.1 * A p.2) := by
  classical
  unfold oddKTheoryFiniteRowFormula
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, oddKTheoryCountableDiagonal_mul]
  calc
    _ = countableModuleDiagonal (φ (f i)) *
        (A i * countableModuleDiagonal (φ (f j))) * A j := by simp only [mul_assoc]
    _ = _ := by rw [(hcomm i j).eq]; simp only [mul_assoc]

/-- Multiplication of two finite formulas is the actual finite product
formula when the left fixed operators commute with the right coefficients. -/
theorem oddKTheoryFiniteRowFormula_mul
    (φ : C(X, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (f : κ → C(X, ℂ)) (A : κ → OddKTheoryCountableOperator B E)
    (g : «λ» → C(X, ℂ)) (C : «λ» → OddKTheoryCountableOperator B E)
    (hcomm : ∀ i j, Commute (A i) (countableModuleDiagonal (φ (g j)))) :
    oddKTheoryFiniteRowFormula φ f A * oddKTheoryFiniteRowFormula φ g C =
      oddKTheoryFiniteRowFormula φ (fun p : κ × «λ» => f p.1 * g p.2)
        (fun p => A p.1 * C p.2) := by
  classical
  unfold oddKTheoryFiniteRowFormula
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, oddKTheoryCountableDiagonal_mul]
  calc
    _ = countableModuleDiagonal (φ (f i)) *
        (A i * countableModuleDiagonal (φ (g j))) * C j := by simp only [mul_assoc]
    _ = _ := by rw [(hcomm i j).eq]; simp only [mul_assoc]

end BC4lean.KKTheory
