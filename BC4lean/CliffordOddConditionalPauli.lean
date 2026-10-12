import BC4lean.CliffordOddSourceCycle
import BC4lean.CliffordExternalEvenBalancedTensor

/-! # The genuine grading-controlled Pauli unitary

On the even spectral range the map is the identity; on the odd spectral
range it is σ_y. It is an actual coefficient-linear selfadjoint unitary
on the Hilbert direct sum. This full map changes the swap grading to the
grading-twisted swap and implements the Koszul half source representation.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddConditionalPauli
open scoped InnerProductSpace
open CliffordExternalEvenBalancedTensor CliffordExternalEvenRepresentation

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]
  [CompleteSpace H]
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) H)

local instance cliffordOddConditionalPauliLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

theorem plus_plus_apply (x : H) : plus J (plus J x) = plus J x :=
  congrArg (fun T : AdjointableMap C H H => T x) (plus_square J)
theorem minus_minus_apply (x : H) : minus J (minus J x) = minus J x :=
  congrArg (fun T : AdjointableMap C H H => T x) (minus_square J)
theorem plus_minus_apply (x : H) : plus J (minus J x) = 0 :=
  congrArg (fun T : AdjointableMap C H H => T x) (plus_mul_minus J)
theorem minus_plus_apply (x : H) : minus J (plus J x) = 0 :=
  congrArg (fun T : AdjointableMap C H H => T x) (minus_mul_plus J)
theorem plus_add_minus_apply (x : H) : plus J x + minus J x = x :=
  congrArg (fun T : AdjointableMap C H H => T x) (plus_add_minus J)

theorem grading_plus : J.toAdjointable * plus J = plus J := by
  calc
    _ = (plus J - minus J) * plus J :=
      congrArg (fun T : AdjointableMap C H H => T * plus J)
        (CliffordOne.plus_sub_minus J.toAdjointable).symm
    _ = _ := by rw [sub_mul, plus_square, minus_mul_plus, sub_zero]

theorem grading_minus : J.toAdjointable * minus J = -minus J := by
  calc
    _ = (plus J - minus J) * minus J :=
      congrArg (fun T : AdjointableMap C H H => T * minus J)
        (CliffordOne.plus_sub_minus J.toAdjointable).symm
    _ = _ := by rw [sub_mul, plus_mul_minus, minus_square, zero_sub]

def operator : AdjointableMap C (HilbertModuleSum C H H) (HilbertModuleSum C H H) :=
  sumMap (plus J) (plus J) + CliffordOddSourceCycle.operator (minus J)

@[simp] theorem operator_apply (x : HilbertModuleSum C H H) :
    operator J x = sumMk (plus J x.fst + (-Complex.I) • minus J x.snd)
      (Complex.I • minus J x.fst + plus J x.snd) := by
  apply Prod.ext <;>
    simp only [operator, AdjointableMap.coe_add_apply, sumMap_apply,
      CliffordOddSourceCycle.operator_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.add_fst, WithCStarModule.add_snd]
  exact add_comm _ _

theorem operator_star : star (operator J) = operator J := by
  have hP : star (plus J) = plus J := plus_adjoint J
  have hQ : star (minus J) = minus J := minus_adjoint J
  unfold operator
  simp only [star_add, ← sumMap_star, CliffordOddSourceCycle.operator_star, hP, hQ]

theorem operator_involutive (x : HilbertModuleSum C H H) : operator J (operator J x) = x := by
  apply Prod.ext <;>
    simp only [operator_apply, sumMk_fst, sumMk_snd, map_add, map_smul,
      plus_plus_apply, minus_minus_apply, plus_minus_apply, minus_plus_apply,
      smul_zero, add_zero, zero_add, smul_smul,
      mul_neg, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  · exact plus_add_minus_apply J x.fst
  · rw [add_comm]
    exact plus_add_minus_apply J x.snd

theorem operator_square : operator J * operator J = 1 := by
  ext x
  change operator J (operator J x) = x
  exact operator_involutive J x

theorem operator_inner (x y : HilbertModuleSum C H H) :
    ⟪operator J x, operator J y⟫_(Cᵐᵒᵖ) = ⟪x, y⟫_(Cᵐᵒᵖ) := by
  rw [(operator J).adjoint_identity]
  change ⟪x, (star (operator J) * operator J) y⟫_(Cᵐᵒᵖ) = _
  rw [operator_star, operator_square, AdjointableMap.one_apply]

def hilbertEquiv : HilbertModuleEquiv C (HilbertModuleSum C H H) (HilbertModuleSum C H H) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := operator J
          invFun := operator J
          left_inv := operator_involutive J
          right_inv := operator_involutive J
          map_add' := (operator J).toCLM.map_add
          map_smul' := (operator J).toCLM.map_smul }
      norm_map' x := by
        change ‖operator J x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), operator_inner,
          ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)] }
  inner_map := operator_inner J

@[simp] theorem hilbertEquiv_apply (x : HilbertModuleSum C H H) :
    hilbertEquiv J x = operator J x := rfl
@[simp] theorem hilbertEquiv_symm_apply (x : HilbertModuleSum C H H) :
    (hilbertEquiv J).symm x = operator J x := rfl

/-- The entire original swap grading becomes the true grading-twisted swap. -/
theorem operator_swap (x : HilbertModuleSum C H H) :
    operator J (sumSwap x) =
      sumMap J.toAdjointable J.toAdjointable (sumSwap (operator J x)) := by
  have hP (z : H) : J.toAdjointable (plus J z) = plus J z :=
    congrArg (fun T : AdjointableMap C H H => T z) (grading_plus J)
  have hQ (z : H) : J.toAdjointable (minus J z) = -minus J z := by
    simpa only [AdjointableMap.mul_apply, AdjointableMap.coe_neg_apply] using
      congrArg (fun T : AdjointableMap C H H => T z) (grading_minus J)
  have hQi (z : H) : J.toAdjointable (Complex.I • minus J z) =
      (-Complex.I) • minus J z := by
    rw [map_smul, hQ, smul_neg, neg_smul]
  have hQni (z : H) : J.toAdjointable ((-Complex.I) • minus J z) =
      Complex.I • minus J z := by
    rw [map_smul, hQ, smul_neg, neg_smul, neg_neg]
  apply Prod.ext <;>
    simp only [operator_apply, sumSwap_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      map_add, hP, hQi, hQni]
  · exact add_comm _ _
  · exact add_comm _ _

/-- An actual odd first operator passes to the correct Pauli first
operator under the full grading-controlled unitary. -/
theorem operator_diagonal_odd (T : AdjointableMap C H H) (hT : J.IsOdd J T)
    (x : HilbertModuleSum C H H) :
    operator J (sumMap T T x) = CliffordOddSourceCycle.operator T (operator J x) := by
  have hP (z : H) : plus J (T z) = T (minus J z) :=
    congrArg (fun S : AdjointableMap C H H => S z) (odd_mul_minus J T hT).symm
  have hQ (z : H) : minus J (T z) = T (plus J z) :=
    congrArg (fun S : AdjointableMap C H H => S z) (odd_mul_plus J T hT).symm
  apply Prod.ext <;>
    simp only [operator_apply, sumMap_apply, CliffordOddSourceCycle.operator_apply,
      sumMk_fst, sumMk_snd, map_add, map_smul, hP, hQ,
      smul_add, smul_smul, neg_mul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

theorem transport_diagonal_odd (T : AdjointableMap C H H) (hT : J.IsOdd J T) :
    (hilbertEquiv J).transport (sumMap T T) = CliffordOddSourceCycle.operator T := by
  ext x
  change operator J (sumMap T T (operator J x)) = CliffordOddSourceCycle.operator T x
  rw [operator_diagonal_odd J T hT, operator_involutive]

variable {A : Type*} [NonUnitalCStarAlgebra A]
  (ρ : A →⋆ₙₐ[ℂ] AdjointableMap C H H)
  (hρ : ∀ a, J.toAdjointable * ρ a = ρ a * J.toAdjointable)

/-- The entire original source representation, including its odd Clifford
coordinate, becomes the genuine Koszul half representation. -/
theorem operator_representation (a : A × A) (x : HilbertModuleSum C H H) :
    operator J (sumMap (ρ a.1) (ρ a.2) x) =
      sumMap (halfRepresentation ρ J hρ a)
        (halfRepresentation ρ J hρ (cliffordCoefficientGrading.automorphism a))
          (operator J x) := by
  have half_apply (b : A × A) (z : H) :
      halfRepresentation ρ J hρ b z = ρ b.1 (plus J z) + ρ b.2 (minus J z) := by
    have h : halfRepresentation ρ J hρ b = ρ b.1 * plus J + ρ b.2 * minus J :=
      halfRepresentation_eq ρ J hρ b
    simpa only [AdjointableMap.coe_add_apply, AdjointableMap.mul_apply] using
      congrArg (fun T : AdjointableMap C H H => T z) h
  have hP (b : A) (z : H) : plus J (ρ b z) = ρ b (plus J z) :=
    congrArg (fun T : AdjointableMap C H H => T z) (plus_commutes ρ J hρ b)
  have hQ (b : A) (z : H) : minus J (ρ b z) = ρ b (minus J z) :=
    congrArg (fun T : AdjointableMap C H H => T z) (minus_commutes ρ J hρ b)
  apply Prod.ext <;>
    simp only [operator_apply, sumMap_apply, half_apply,
      cliffordCoefficientGrading_apply, sumMk_fst, sumMk_snd, map_add, map_smul,
      plus_plus_apply, minus_minus_apply, plus_minus_apply, minus_plus_apply,
      hP, hQ, smul_zero, add_zero, zero_add]
  exact add_comm _ _

theorem transport_representation (a : A × A) :
    (hilbertEquiv J).transport (sumMap (ρ a.1) (ρ a.2)) =
      sumMap (halfRepresentation ρ J hρ a)
        (halfRepresentation ρ J hρ (cliffordCoefficientGrading.automorphism a)) := by
  ext x
  change operator J (sumMap (ρ a.1) (ρ a.2) (operator J x)) = _
  rw [operator_representation, operator_involutive]

end BC4lean.KKTheory.CliffordOddConditionalPauli
