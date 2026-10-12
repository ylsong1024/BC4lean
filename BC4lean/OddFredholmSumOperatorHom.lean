import BC4lean.OddFredholmStandardStabilization

/-! # The actual block operator star homomorphism

The product C-star algebra of adjointable endomorphisms acts block diagonally
on the genuine Hilbert module sum. Its automatic contractivity proves that
augmentation by the identity preserves the bound needed by the row homotopy.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance oddContinuationOddFredholmSumOperatorHomLocalInstance01 : CompleteSpace (HilbertModuleSum B E F) := hilbertModuleSum_complete

def oddFredholmSumOperatorHom :
    (AdjointableMap B E E × AdjointableMap B F F) →⋆ₐ[ℂ]
      AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) where
  toFun p := sumMap p.1 p.2
  map_one' := sumMap_one
  map_zero' := sumMap_zero
  map_add' p q := sumMap_add p.1 q.1 p.2 q.2
  map_mul' p q := sumMap_mul p.1 q.1 p.2 q.2
  map_star' p := sumMap_star p.1 p.2
  commutes' z := by
    change sumMap (algebraMap ℂ (AdjointableMap B E E) z)
      (algebraMap ℂ (AdjointableMap B F F) z) = _
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      sumMap_smul, sumMap_one, Algebra.algebraMap_eq_smul_one]

theorem oddFredholmSumOperator_norm_le (S : AdjointableMap B E E)
    (T : AdjointableMap B F F) : ‖sumMap S T‖ ≤ max ‖S‖ ‖T‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le
    (oddFredholmSumOperatorHom (B := B) (E := E) (F := F)).toNonUnitalStarAlgHom (S, T)
  change ‖sumMap S T‖ ≤ ‖(S, T)‖ at h
  simpa only [Prod.norm_def] using h

theorem oddFredholmExponential_sumMap (S : selfAdjoint (AdjointableMap B E E))
    (T : selfAdjoint (AdjointableMap B F F)) :
    (oddFredholmExponential (⟨sumMap (S : AdjointableMap B E E) (T : AdjointableMap B F F),
      by
        change star (sumMap (S : AdjointableMap B E E) (T : AdjointableMap B F F)) =
          sumMap (S : AdjointableMap B E E) (T : AdjointableMap B F F)
        rw [← sumMap_star, S.property.star_eq, T.property.star_eq]⟩) :
        AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) =
      sumMap (oddFredholmExponential S : AdjointableMap B E E)
        (oddFredholmExponential T : AdjointableMap B F F) := by
  let φ := oddFredholmSumOperatorHom (B := B) (E := E) (F := F)
  let +nondep : NormedAlgebra ℚ (AdjointableMap B E E) :=
    NormedAlgebra.restrictScalars ℚ ℂ (AdjointableMap B E E)
  let +nondep : NormedAlgebra ℚ (AdjointableMap B F F) :=
    NormedAlgebra.restrictScalars ℚ ℂ (AdjointableMap B F F)
  let +nondep : NormedAlgebra ℚ
      (AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) :=
    NormedAlgebra.restrictScalars ℚ ℂ
      (AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F))
  have h := NormedSpace.map_exp φ (map_continuous φ)
    ((Complex.I * (Real.pi : ℂ)) •
      (((S : AdjointableMap B E E), (T : AdjointableMap B F F)) + 1))
  rw [map_smul, map_add, map_one] at h
  change φ (NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) •
      (((S : AdjointableMap B E E), (T : AdjointableMap B F F)) + 1))) =
    NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) •
      (sumMap (S : AdjointableMap B E E) (T : AdjointableMap B F F) + 1)) at h
  have hblock : φ (NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) •
      (((S : AdjointableMap B E E), (T : AdjointableMap B F F)) + 1))) =
      sumMap (NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) •
        ((S : AdjointableMap B E E) + 1)))
        (NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) •
          ((T : AdjointableMap B F F) + 1))) := by
    change sumMap (NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) •
        (((S : AdjointableMap B E E), (T : AdjointableMap B F F)) + 1))).1
      (NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) •
        (((S : AdjointableMap B E E), (T : AdjointableMap B F F)) + 1))).2 = _
    exact congrArg₂ (sumMap (B := B))
      (Prod.fst_exp ((Complex.I * (Real.pi : ℂ)) •
        (((S : AdjointableMap B E E), (T : AdjointableMap B F F)) + 1)))
      (Prod.snd_exp ((Complex.I * (Real.pi : ℂ)) •
        (((S : AdjointableMap B E E), (T : AdjointableMap B F F)) + 1)))
  change NormedSpace.exp (Complex.I • (Real.pi •
    (sumMap (S : AdjointableMap B E E) (T : AdjointableMap B F F) + 1))) =
      sumMap (NormedSpace.exp (Complex.I • (Real.pi • ((S : AdjointableMap B E E) + 1))))
        (NormedSpace.exp (Complex.I • (Real.pi • ((T : AdjointableMap B F F) + 1))))
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul] using!
    h.symm.trans hblock

theorem oddFredholmExponential_one {A : Type*} [CStarAlgebra A] :
    oddFredholmExponential (1 : selfAdjoint A) = 1 := by
  apply Subtype.ext
  have h := oddFredholmExponential_sub_one_factor (1 : selfAdjoint A)
  simp only [selfAdjoint.val_one, one_pow, sub_self, zero_mul] at h
  exact sub_eq_zero.mp h

theorem oddFredholmStandardStabilizedOperator_norm_le_one
    (hE : IsCountablyGeneratedModule B E) (S : selfAdjoint (AdjointableMap B E E))
    (hS : ‖(S : AdjointableMap B E E)‖ ≤ 1) :
    ‖(oddFredholmStandardStabilizedOperator hE S : OddFredholmStandardOperator B)‖ ≤ 1 := by
  change ‖(standardModuleStabilization hE).transport (sumMap (S : AdjointableMap B E E)
    (1 : OddFredholmStandardOperator B))‖ ≤ 1
  rw [HilbertModuleEquiv.transport_norm]
  have hOne : ‖(1 : OddFredholmStandardOperator B)‖ ≤ 1 := by
    change ‖(1 : OddFredholmStandardOperator B).toCLM‖ ≤ 1
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x‖ ≤ 1 * ‖x‖
    exact (one_mul ‖x‖).symm.le
  exact (oddFredholmSumOperator_norm_le _ _).trans (max_le hS hOne)

end BC4lean.KKTheory
