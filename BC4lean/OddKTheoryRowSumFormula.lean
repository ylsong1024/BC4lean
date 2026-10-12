import BC4lean.OddKTheoryFiniteCoordinateEquiv
import BC4lean.OddFredholmPullbackNaturality

/-! # The genuine periodic row formula respects direct sums

The completed coefficient-form splitting intertwines the full bounded
formula, including all its fixed row-coordinate operators. No compactness
of either coordinate projection is used.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F]

local instance oddContinuationOddKTheoryRowSumFormulaLocalInstance01 : CompleteSpace (HilbertModuleSum B E F) := hilbertModuleSum_complete
local instance oddContinuationOddKTheoryRowSumFormulaLocalInstance02 : CompleteSpace (HilbertModuleSum B (CountableHilbertModuleSum B E)
    (CountableHilbertModuleSum B F)) := hilbertModuleSum_complete

theorem oddKTheoryRowRectangular_ext (S T : AdjointableMap B (CountableHilbertModuleSum B E) G)
    (h : ∀ n (x : E), S (countableModuleInclusion n x) = T (countableModuleInclusion n x)) : S = T := by
  ext z
  refine countableModuleMk_denseRange.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  have hx : countableModuleMk (B := B) x =
      ∑ n ∈ x.support, countableModuleInclusion n (x n) := by
    calc
      countableModuleMk (B := B) x = countableModuleMk (B := B) (x.sum Finsupp.single) :=
        congrArg (countableModuleMk (B := B)) x.sum_single.symm
      _ = ∑ n ∈ x.support, countableModuleInclusion n (x n) := by
        change countableModuleMk (B := B) (∑ n ∈ x.support, Finsupp.single n (x n)) = _
        rw [map_sum]
        rfl
  rw [hx, map_sum S.toCLM, map_sum T.toCLM]
  exact Finset.sum_congr rfl (fun n _ => h n (x n))

theorem oddKTheoryRowSumSplit_transport_diagonal
    (S : AdjointableMap B E E) (T : AdjointableMap B F F) :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
      (countableModuleDiagonal (sumMap S T)) =
      sumMap (countableModuleDiagonal S) (countableModuleDiagonal T) := by
  have h : (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable.comp (countableModuleDiagonal (sumMap S T)) =
      (sumMap (countableModuleDiagonal S) (countableModuleDiagonal T)).comp
        (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable := by
    apply oddKTheoryRowRectangular_ext
    intro n x
    simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
      oddKTheoryCountableDiagonal_inclusion, oddKTheoryCountableSumEquiv_inclusion,
      sumMap_apply, sumMk_fst, sumMk_snd]
  ext x
  have hh := congrArg (fun U => U ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).symm x)) h
  simpa only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.transport_apply] using hh

theorem oddKTheoryRowSumSplit_transport_reflection (k : ℤ) :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
      (oddKTheoryRowReflectionOperator k) =
      sumMap (oddKTheoryRowReflectionOperator k) (oddKTheoryRowReflectionOperator k) := by
  have h : (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable.comp (oddKTheoryRowReflectionOperator k) =
      (sumMap (oddKTheoryRowReflectionOperator k) (oddKTheoryRowReflectionOperator k)).comp
        (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable := by
    have hinc (w : ℤ) (y : HilbertModuleSum B E F) :
        (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
            (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) w y) =
          sumMk
            (oddKTheoryRowIntegerInclusion (B := B) (E := E) w y.fst)
            (oddKTheoryRowIntegerInclusion (B := B) (E := F) w y.snd) :=
      oddKTheoryCountableSumEquiv_inclusion (B := B) (E := E) (F := F)
        (oddKTheoryRowIntegerIndex w) y
    apply oddKTheoryRowRectangular_ext
    intro n x
    obtain ⟨z, rfl⟩ := Equiv.intEquivNat.surjective n
    change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
        ((oddKTheoryRowReflectionOperator (B := B) (E := HilbertModuleSum B E F) k)
          (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) z x)) =
      (sumMap (oddKTheoryRowReflectionOperator (B := B) (E := E) k)
        (oddKTheoryRowReflectionOperator (B := B) (E := F) k))
        ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
          (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) z x))
    rw [oddKTheoryRowReflectionOperator_inclusion, hinc, hinc, sumMap_apply,
      sumMk_fst, sumMk_snd, oddKTheoryRowReflectionOperator_inclusion,
      oddKTheoryRowReflectionOperator_inclusion]
  ext x
  have hh := congrArg (fun U => U ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).symm x)) h
  simpa only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.transport_apply] using hh

theorem oddKTheoryRowSumSplit_transport_sign :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport oddKTheoryRowSignOperator =
      sumMap oddKTheoryRowSignOperator oddKTheoryRowSignOperator := by
  have h : (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable.comp oddKTheoryRowSignOperator =
      (sumMap oddKTheoryRowSignOperator oddKTheoryRowSignOperator).comp
        (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable := by
    have hinc (w : ℤ) (y : HilbertModuleSum B E F) :
        (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
            (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) w y) =
          sumMk
            (oddKTheoryRowIntegerInclusion (B := B) (E := E) w y.fst)
            (oddKTheoryRowIntegerInclusion (B := B) (E := F) w y.snd) :=
      oddKTheoryCountableSumEquiv_inclusion (B := B) (E := E) (F := F)
        (oddKTheoryRowIntegerIndex w) y
    apply oddKTheoryRowRectangular_ext
    intro n x
    obtain ⟨z, rfl⟩ := Equiv.intEquivNat.surjective n
    change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
        ((oddKTheoryRowSignOperator (B := B) (E := HilbertModuleSum B E F))
          (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) z x)) =
      (sumMap (oddKTheoryRowSignOperator (B := B) (E := E))
        (oddKTheoryRowSignOperator (B := B) (E := F)))
        ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
          (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) z x))
    rw [oddKTheoryRowSignOperator_inclusion, HilbertModuleEquiv.map_smul, hinc,
      sumMap_apply, sumMk_fst, sumMk_snd, oddKTheoryRowSignOperator_inclusion,
      oddKTheoryRowSignOperator_inclusion, sumMk_smul]
  ext x
  have hh := congrArg (fun U => U ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).symm x)) h
  simpa only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.transport_apply] using hh

theorem oddKTheoryRowSumSplit_transport_zeroProjection :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport oddKTheoryRowZeroProjection =
      sumMap oddKTheoryRowZeroProjection oddKTheoryRowZeroProjection := by
  have h : (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable.comp oddKTheoryRowZeroProjection =
      (sumMap oddKTheoryRowZeroProjection oddKTheoryRowZeroProjection).comp
        (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).toAdjointable := by
    have hinc (w : ℤ) (y : HilbertModuleSum B E F) :
        (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
            (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) w y) =
          sumMk
            (oddKTheoryRowIntegerInclusion (B := B) (E := E) w y.fst)
            (oddKTheoryRowIntegerInclusion (B := B) (E := F) w y.snd) :=
      oddKTheoryCountableSumEquiv_inclusion (B := B) (E := E) (F := F)
        (oddKTheoryRowIntegerIndex w) y
    apply oddKTheoryRowRectangular_ext
    intro n x
    obtain ⟨z, rfl⟩ := Equiv.intEquivNat.surjective n
    change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
        ((oddKTheoryRowZeroProjection (B := B) (E := HilbertModuleSum B E F))
          (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) z x)) =
      (sumMap (oddKTheoryRowZeroProjection (B := B) (E := E))
        (oddKTheoryRowZeroProjection (B := B) (E := F)))
        ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
          (oddKTheoryRowIntegerInclusion (B := B) (E := HilbertModuleSum B E F) z x))
    rw [oddKTheoryRowZeroProjection_inclusion, hinc, sumMap_apply,
      sumMk_fst, sumMk_snd, oddKTheoryRowZeroProjection_inclusion,
      oddKTheoryRowZeroProjection_inclusion]
    by_cases hz : z = 0
    · simp only [if_pos hz, hinc]
    · simp only [if_neg hz, HilbertModuleEquiv.map_zero, sumMk_zero]
  ext x
  have hh := congrArg (fun U => U ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).symm x)) h
  simpa only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.transport_apply] using hh

theorem oddKTheoryRowSumSplit_transport_fixedPermutation (i : Fin 4) :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
      (oddKTheoryRowLoopFixedPermutation i) =
      sumMap (oddKTheoryRowLoopFixedPermutation i) (oddKTheoryRowLoopFixedPermutation i) := by
  fin_cases i
  · change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
        (1 : OddKTheoryCountableOperator B (HilbertModuleSum B E F)) =
      sumMap (1 : OddKTheoryCountableOperator B E) (1 : OddKTheoryCountableOperator B F)
    exact ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport_one).trans
      sumMap_one.symm
  · exact oddKTheoryRowSumSplit_transport_reflection (B := B) (E := E) (F := F) 0
  · exact oddKTheoryRowSumSplit_transport_reflection (B := B) (E := E) (F := F) (-1)
  · change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
        (oddKTheoryRowReflectionOperator (B := B) (E := HilbertModuleSum B E F) 0 *
          oddKTheoryRowReflectionOperator (B := B) (E := HilbertModuleSum B E F) (-1)) =
      sumMap
        (oddKTheoryRowReflectionOperator (B := B) (E := E) 0 *
          oddKTheoryRowReflectionOperator (B := B) (E := E) (-1))
        (oddKTheoryRowReflectionOperator (B := B) (E := F) 0 *
          oddKTheoryRowReflectionOperator (B := B) (E := F) (-1))
    rw [HilbertModuleEquiv.transport_mul, oddKTheoryRowSumSplit_transport_reflection,
      oddKTheoryRowSumSplit_transport_reflection, ← sumMap_mul]

theorem oddKTheoryRowSumSplit_transport_fixedOperator (p : Fin 4 × Fin 4) :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
      (oddKTheoryRowLoopFixedOperator p) =
      sumMap (oddKTheoryRowLoopFixedOperator p) (oddKTheoryRowLoopFixedOperator p) := by
  simp only [oddKTheoryRowLoopFixedOperator, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_star, oddKTheoryRowSumSplit_transport_fixedPermutation,
    oddKTheoryRowSumSplit_transport_sign, sumMap_star, sumMap_mul]

theorem oddKTheoryRowSumSplit_transport_fixedFinite (i : Fin 4) :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
      (oddKTheoryRowLoopFixedFiniteOperator i) =
      sumMap (oddKTheoryRowLoopFixedFiniteOperator i) (oddKTheoryRowLoopFixedFiniteOperator i) := by
  fin_cases i
  · exact oddKTheoryRowSumSplit_transport_zeroProjection (B := B) (E := E) (F := F)
  · change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
        (oddKTheoryRowZeroProjection (B := B) (E := HilbertModuleSum B E F) *
          oddKTheoryRowReflectionOperator (B := B) (E := HilbertModuleSum B E F) (-1)) =
      sumMap
        (oddKTheoryRowZeroProjection (B := B) (E := E) *
          oddKTheoryRowReflectionOperator (B := B) (E := E) (-1))
        (oddKTheoryRowZeroProjection (B := B) (E := F) *
          oddKTheoryRowReflectionOperator (B := B) (E := F) (-1))
    rw [HilbertModuleEquiv.transport_mul, oddKTheoryRowSumSplit_transport_zeroProjection,
      oddKTheoryRowSumSplit_transport_reflection, ← sumMap_mul]
  · change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
        (oddKTheoryRowReflectionOperator (B := B) (E := HilbertModuleSum B E F) (-1) *
          oddKTheoryRowZeroProjection (B := B) (E := HilbertModuleSum B E F)) =
      sumMap
        (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1) *
          oddKTheoryRowZeroProjection (B := B) (E := E))
        (oddKTheoryRowReflectionOperator (B := B) (E := F) (-1) *
          oddKTheoryRowZeroProjection (B := B) (E := F))
    rw [HilbertModuleEquiv.transport_mul, oddKTheoryRowSumSplit_transport_reflection,
      oddKTheoryRowSumSplit_transport_zeroProjection, ← sumMap_mul]
  · change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
        (oddKTheoryRowReflectionOperator (B := B) (E := HilbertModuleSum B E F) (-1) *
          oddKTheoryRowZeroProjection (B := B) (E := HilbertModuleSum B E F) *
          oddKTheoryRowReflectionOperator (B := B) (E := HilbertModuleSum B E F) (-1)) =
      sumMap
        (oddKTheoryRowReflectionOperator (B := B) (E := E) (-1) *
          oddKTheoryRowZeroProjection (B := B) (E := E) *
          oddKTheoryRowReflectionOperator (B := B) (E := E) (-1))
        (oddKTheoryRowReflectionOperator (B := B) (E := F) (-1) *
          oddKTheoryRowZeroProjection (B := B) (E := F) *
          oddKTheoryRowReflectionOperator (B := B) (E := F) (-1))
    rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_mul,
      oddKTheoryRowSumSplit_transport_reflection, oddKTheoryRowSumSplit_transport_zeroProjection,
      ← sumMap_mul, ← sumMap_mul]

def oddKTheoryCircleSumHom
    (φ : C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (ψ : C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B F F) :
    C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) where
  toFun f := sumMap (φ f) (ψ f)
  map_one' := by rw [map_one, map_one, sumMap_one]
  map_zero' := by rw [map_zero, map_zero, sumMap_zero]
  map_add' f g := by rw [map_add, map_add, sumMap_add]
  map_mul' f g := by rw [map_mul, map_mul, sumMap_mul]
  map_star' f := by rw [map_star, map_star, sumMap_star]
  commutes' c := by
    have hφ : φ (algebraMap ℂ C(Circle, ℂ) c) =
        algebraMap ℂ (AdjointableMap B E E) c := φ.commutes c
    have hψ : ψ (algebraMap ℂ C(Circle, ℂ) c) =
        algebraMap ℂ (AdjointableMap B F F) c := ψ.commutes c
    change sumMap (φ (algebraMap ℂ C(Circle, ℂ) c))
        (ψ (algebraMap ℂ C(Circle, ℂ) c)) =
      algebraMap ℂ (AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) c
    rw [hφ, hψ]
    simp only [Algebra.algebraMap_eq_smul_one, sumMap_smul, sumMap_one]

theorem oddKTheoryRowSumSplit_transport_formula
    (φ : C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (ψ : C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B F F) :
    (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
      (oddKTheoryFiniteRowFormula (oddKTheoryCircleSumHom φ ψ)
        oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator) =
      sumMap (oddKTheoryFiniteRowFormula φ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator)
        (oddKTheoryFiniteRowFormula ψ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator) := by
  let e := oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)
  have hfixed (i : OddKTheoryLoopTerm) :
      e.transport (oddKTheoryRowLoopTermOperator (B := B) (E := HilbertModuleSum B E F) i) =
        sumMap (oddKTheoryRowLoopTermOperator (B := B) (E := E) i)
          (oddKTheoryRowLoopTermOperator (B := B) (E := F) i) := by
    cases i with
    | inl p => exact oddKTheoryRowSumSplit_transport_fixedOperator p
    | inr i =>
      cases i with
      | inl _ => exact oddKTheoryRowSumSplit_transport_sign
      | inr i => exact oddKTheoryRowSumSplit_transport_fixedFinite i
  have hsum (s : Finset OddKTheoryLoopTerm)
      (S : OddKTheoryLoopTerm → OddKTheoryCountableOperator B E)
      (T : OddKTheoryLoopTerm → OddKTheoryCountableOperator B F) :
      (∑ i ∈ s, sumMap (S i) (T i)) = sumMap (∑ i ∈ s, S i) (∑ i ∈ s, T i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, sumMap_zero]
    | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi,
        Finset.sum_insert hi, ih, sumMap_add]
  change e.transportStarAlgEquiv.toStarAlgHom
      (∑ i : OddKTheoryLoopTerm,
        countableModuleDiagonal ((oddKTheoryCircleSumHom φ ψ) (oddKTheoryLoopTermCoefficient i)) *
          oddKTheoryRowLoopTermOperator (B := B) (E := HilbertModuleSum B E F) i) =
    sumMap
      (∑ i : OddKTheoryLoopTerm, countableModuleDiagonal (φ (oddKTheoryLoopTermCoefficient i)) *
        oddKTheoryRowLoopTermOperator (B := B) (E := E) i)
      (∑ i : OddKTheoryLoopTerm, countableModuleDiagonal (ψ (oddKTheoryLoopTermCoefficient i)) *
        oddKTheoryRowLoopTermOperator (B := B) (E := F) i)
  rw [map_sum]
  calc
    _ = ∑ i : OddKTheoryLoopTerm,
        sumMap
          (countableModuleDiagonal (φ (oddKTheoryLoopTermCoefficient i)) *
            oddKTheoryRowLoopTermOperator (B := B) (E := E) i)
          (countableModuleDiagonal (ψ (oddKTheoryLoopTermCoefficient i)) *
            oddKTheoryRowLoopTermOperator (B := B) (E := F) i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      change e.transport
          (countableModuleDiagonal
            (sumMap (φ (oddKTheoryLoopTermCoefficient i)) (ψ (oddKTheoryLoopTermCoefficient i)))) *
        e.transport (oddKTheoryRowLoopTermOperator (B := B) (E := HilbertModuleSum B E F) i) = _
      rw [oddKTheoryRowSumSplit_transport_diagonal, hfixed, ← sumMap_mul]
    _ = _ := hsum Finset.univ _ _

end BC4lean.KKTheory
