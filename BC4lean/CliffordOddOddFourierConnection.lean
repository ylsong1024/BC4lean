import BC4lean.CliffordOddOddFourier

/-! # All four actual Fourier creator transfers

The adjoint Fourier columns are genuine σ_y eigenvectors. Composing the
original full diagonal creator error with those adjointable embeddings
and the actual whole Fourier unitary proves the compact signed errors.
The opposite coefficient coordinate reverses the eigenvalue, exactly
matching the second Clifford expansion's negative operator.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddOddFourier
open CliffordQuarterPhase

variable {C M F : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]

def plusEmbedding : AdjointableMap C F (HilbertModuleSum C F F) := column ((-Complex.I) • 1) 1
def minusEmbedding : AdjointableMap C F (HilbertModuleSum C F F) := column 1 ((-Complex.I) • 1)

theorem signed_plus (D : AdjointableMap C F F) :
    (CliffordOddSourceCycle.operator D).comp plusEmbedding = plusEmbedding.comp D := by
  have hcolumn (S T : AdjointableMap C F F) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  ext y
  simp only [AdjointableMap.comp_apply, plusEmbedding, hcolumn,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    CliffordOddSourceCycle.operator_apply, sumMk_fst, sumMk_snd]
  apply Prod.ext
  · rfl
  · change Complex.I • D ((-Complex.I) • y) = D y
    rw [map_smul, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

theorem signed_minus (D : AdjointableMap C F F) :
    (CliffordOddSourceCycle.operator D).comp minusEmbedding = -(minusEmbedding.comp D) := by
  have hcolumn (S T : AdjointableMap C F F) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  ext y
  simp only [AdjointableMap.comp_apply, minusEmbedding, hcolumn,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    CliffordOddSourceCycle.operator_apply, sumMk_fst, sumMk_snd,
    AdjointableMap.coe_neg_apply]
  apply Prod.ext
  · change (-Complex.I) • D ((-Complex.I) • y) = -(D y)
    rw [map_smul, smul_smul, neg_mul, mul_neg, Complex.I_mul_I, neg_neg,
      neg_one_smul]
  · change Complex.I • D y = -((-Complex.I) • D y)
    rw [neg_smul, neg_neg]

theorem adjoint_column_even_embedding (T : AdjointableMap C F M) :
    (star operator).comp (column T T) = (sumMap T T).comp plusEmbedding := by
  have hcolumn (S T : AdjointableMap C F M) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  have hcolumnSelf (S T : AdjointableMap C F F) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  rw [adjoint_column_even]
  ext y
  simp only [AdjointableMap.comp_apply, plusEmbedding, hcolumn, hcolumnSelf,
    sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_smul_apply,
    AdjointableMap.one_apply, map_smul]

theorem adjoint_column_odd_embedding (T : AdjointableMap C F M) :
    (star operator).comp (column T (-T)) = (sumMap T T).comp minusEmbedding := by
  have hcolumn (S T : AdjointableMap C F M) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  have hcolumnSelf (S T : AdjointableMap C F F) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  rw [adjoint_column_odd]
  ext y
  simp only [AdjointableMap.comp_apply, minusEmbedding, hcolumn, hcolumnSelf,
    sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_smul_apply,
    AdjointableMap.one_apply, map_smul]

theorem opposite_adjoint_column_even (T : AdjointableMap C F M) :
    oppositeEquiv.symm.toAdjointable.comp (column T T) = (sumMap T T).comp minusEmbedding := by
  have hcolumn (S T : AdjointableMap C F M) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  have hcolumnSelf (S T : AdjointableMap C F F) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  ext y
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    oppositeEquiv_symm_apply]
  have hswap : sumSwap (column T T y) = column T T y := by
    simp only [hcolumn, sumSwap_apply, sumMk_fst, sumMk_snd]
  rw [hswap]
  have h := congrArg (fun Q : AdjointableMap C F (Sum (C := C) (M := M)) => Q y)
    (adjoint_column_even T)
  simp only [AdjointableMap.comp_apply] at h
  rw [h]
  simp only [hcolumn, hcolumnSelf, minusEmbedding, sumMap_apply, sumSwap_apply,
    sumMk_fst, sumMk_snd, AdjointableMap.coe_smul_apply,
    AdjointableMap.one_apply, map_smul]

theorem opposite_adjoint_column_odd (T : AdjointableMap C F M) :
    oppositeEquiv.symm.toAdjointable.comp (column T (-T)) = -((sumMap T T).comp plusEmbedding) := by
  have hcolumn (S T : AdjointableMap C F M) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  have hcolumnSelf (S T : AdjointableMap C F F) (x : F) :
      column S T x = sumMk (S x) (T x) := by
    simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]
  ext y
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    oppositeEquiv_symm_apply, AdjointableMap.coe_neg_apply]
  have hswap : sumSwap (column T (-T) y) = -(column T (-T) y) := by
    apply Prod.ext <;>
      simp only [hcolumn, sumSwap_apply, sumMk_fst, sumMk_snd,
        AdjointableMap.coe_neg_apply, WithCStarModule.neg_fst,
        WithCStarModule.neg_snd, neg_neg]
  rw [hswap, map_neg, map_neg]
  have h := congrArg (fun Q : AdjointableMap C F (Sum (C := C) (M := M)) => Q y)
    (adjoint_column_odd T)
  simp only [AdjointableMap.comp_apply] at h
  rw [h]
  simp only [hcolumn, hcolumnSelf, sumSwap_apply, sumMk_fst, sumMk_snd, plusEmbedding,
    sumMap_apply, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply, map_smul]

variable (R : AdjointableMap C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)))
  (T : AdjointableMap C F M) (D : AdjointableMap C F F)
  (hR : IsModuleCompact (R.comp (sumMap T T) -
    (sumMap T T).comp (CliffordOddSourceCycle.operator D)))

include hR in
private theorem embedded_plus : IsModuleCompact
    (R.comp ((sumMap T T).comp plusEmbedding) -
      ((sumMap T T).comp plusEmbedding).comp D) := by
  have h := hR.comp_right plusEmbedding
  convert h using 1
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply]
  have hy := congrArg (fun Q : AdjointableMap C F (HilbertModuleSum C F F) => Q y) (signed_plus D)
  simp only [AdjointableMap.comp_apply] at hy
  rw [hy]

include hR in
private theorem embedded_minus : IsModuleCompact
    (R.comp ((sumMap T T).comp minusEmbedding) +
      ((sumMap T T).comp minusEmbedding).comp D) := by
  have h := hR.comp_right minusEmbedding
  convert h using 1
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply]
  have hy := congrArg (fun Q : AdjointableMap C F (HilbertModuleSum C F F) => Q y) (signed_minus D)
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_neg_apply] at hy
  rw [hy, map_neg, sub_neg_eq_add]

include hR in
theorem creator_even : IsModuleCompact
    ((hilbertEquiv.transport R).comp (column T T) - (column T T).comp D) := by
  have hinv (z : Sum (C := C) (M := M)) : hilbertEquiv (star operator z) = z := by
    change hilbertEquiv (hilbertEquiv.symm z) = z
    exact HilbertModuleEquiv.apply_symm_apply hilbertEquiv z
  have h := (embedded_plus R T D hR).comp_left hilbertEquiv.toAdjointable
  rw [← adjoint_column_even_embedding T] at h
  convert h using 1
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.transport_apply,
    hilbertEquiv_symm_apply, map_sub, hinv]

include hR in
theorem creator_odd : IsModuleCompact
    ((hilbertEquiv.transport R).comp (column T (-T)) + (column T (-T)).comp D) := by
  have hinv (z : Sum (C := C) (M := M)) : hilbertEquiv (star operator z) = z := by
    change hilbertEquiv (hilbertEquiv.symm z) = z
    exact HilbertModuleEquiv.apply_symm_apply hilbertEquiv z
  have h := (embedded_minus R T D hR).comp_left hilbertEquiv.toAdjointable
  rw [← adjoint_column_odd_embedding T] at h
  convert h using 1
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.transport_apply,
    hilbertEquiv_symm_apply, map_add, hinv]

include hR in
theorem opposite_creator_even : IsModuleCompact
    ((oppositeEquiv.transport R).comp (column T T) + (column T T).comp D) := by
  have h := (embedded_minus R T D hR).comp_left oppositeEquiv.toAdjointable
  rw [← opposite_adjoint_column_even T] at h
  convert h using 1
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.transport_apply,
    map_add, HilbertModuleEquiv.apply_symm_apply]

include hR in
theorem opposite_creator_odd : IsModuleCompact
    ((oppositeEquiv.transport R).comp (column T (-T)) - (column T (-T)).comp D) := by
  have h := ((embedded_plus R T D hR).neg).comp_left oppositeEquiv.toAdjointable
  have heq : -(R.comp ((sumMap T T).comp plusEmbedding) -
        ((sumMap T T).comp plusEmbedding).comp D) =
      R.comp (oppositeEquiv.symm.toAdjointable.comp (column T (-T))) -
        (oppositeEquiv.symm.toAdjointable.comp (column T (-T))).comp D := by
    rw [opposite_adjoint_column_odd T]
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_neg_apply, map_neg]
    abel
  rw [heq] at h
  convert h using 1
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.transport_apply,
    map_sub, HilbertModuleEquiv.apply_symm_apply]

end BC4lean.KKTheory.CliffordOddOddFourier
