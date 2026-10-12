import BC4lean.OddKTheoryFiniteCircleRecovery
import BC4lean.OddKTheoryFiniteMatrixFlatten

/-! # Genuine finite matrix recovery of a unitary by the universal odd loop

The based scalar circle homotopy is first made an actual matrix of continuous
functions, then evaluated by the genuine unitary functional calculus and
flattened into the sum-indexed finite matrix algebra. This constructs an
actual norm path and equality in the existing stable unitary K1 quotient.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped Matrix CStarAlgebra
open BC4lean.OperatorKTheory

def oddKTheoryRecoveryFunctionMatrix (s : I) :
    CStarMatrix (Fin 2) (Fin 2) C(Circle, ℂ) :=
  CStarMatrix.ofMatrix (fun i j => oddKTheoryRecoveryCircleEntry s i j)

theorem oddKTheoryRecoveryFunctionMatrix_mem_unitary (s : I) :
    oddKTheoryRecoveryFunctionMatrix s ∈
      unitary (CStarMatrix (Fin 2) (Fin 2) C(Circle, ℂ)) := by
  have hentry (i j : Fin 2) :
      oddKTheoryRecoveryFunctionMatrix s i j = oddKTheoryRecoveryCircleEntry s i j := rfl
  apply Unitary.mem_iff.mpr
  constructor
  · apply CStarMatrix.ext
    intro i j
    apply ContinuousMap.ext
    intro z
    simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.one_apply,
      hentry, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.mul_apply, ContinuousMap.star_apply, DFunLike.ite_apply,
      ContinuousMap.one_apply, ContinuousMap.zero_apply]
    change (∑ k : Fin 2,
      star ((oddKTheoryRecoveryCircleFamily z s : OddKTheoryRecoveryMatrix) k i) *
        (oddKTheoryRecoveryCircleFamily z s : OddKTheoryRecoveryMatrix) k j) =
      if i = j then 1 else 0
    have h := congrArg (fun M : OddKTheoryRecoveryMatrix => M i j)
      (Unitary.star_mul_self_of_mem (oddKTheoryRecoveryCircleFamily z s).property)
    simpa only [CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.one_apply] using h
  · apply CStarMatrix.ext
    intro i j
    apply ContinuousMap.ext
    intro z
    simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.one_apply,
      hentry, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.mul_apply, ContinuousMap.star_apply, DFunLike.ite_apply,
      ContinuousMap.one_apply, ContinuousMap.zero_apply]
    change (∑ k : Fin 2,
      (oddKTheoryRecoveryCircleFamily z s : OddKTheoryRecoveryMatrix) i k *
        star ((oddKTheoryRecoveryCircleFamily z s : OddKTheoryRecoveryMatrix) j k)) =
      if i = j then 1 else 0
    have h := congrArg (fun M : OddKTheoryRecoveryMatrix => M i j)
      (Unitary.mul_star_self_of_mem (oddKTheoryRecoveryCircleFamily z s).property)
    simpa only [CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.one_apply] using h

def oddKTheoryRecoveryFunctionUnitary (s : I) :
    unitary (CStarMatrix (Fin 2) (Fin 2) C(Circle, ℂ)) :=
  ⟨oddKTheoryRecoveryFunctionMatrix s, oddKTheoryRecoveryFunctionMatrix_mem_unitary s⟩

theorem continuous_oddKTheoryRecoveryFunctionUnitary :
    Continuous oddKTheoryRecoveryFunctionUnitary := by
  apply Continuous.subtype_mk
  exact CStarMatrix.ofMatrixL.continuous.comp
    (continuous_pi fun i => continuous_pi fun j => continuous_oddKTheoryRecoveryCircleEntry i j)

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι] [DecidableEq ι]

local instance oddKTheoryFiniteMatrixRecoverySpectralOrder : PartialOrder A :=
  CStarAlgebra.spectralOrder A
local instance oddKTheoryFiniteMatrixRecoverySpectralOrderedRing : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

set_option maxHeartbeats 2000000 in
def oddKTheoryRecoveryNestedUnitary (u : unitary (CStarMatrix ι ι A)) (s : I) :
    unitary (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) :=
  ⟨matrixMap (oddKTheoryCircleCFC u) (oddKTheoryRecoveryFunctionUnitary s : _),
    Unitary.map_mem (matrixMap (oddKTheoryCircleCFC u))
      (oddKTheoryRecoveryFunctionUnitary s).property⟩

@[simp] theorem oddKTheoryRecoveryNestedUnitary_apply
    (u : unitary (CStarMatrix ι ι A)) (s : I) (i j : Fin 2) :
    (oddKTheoryRecoveryNestedUnitary u s :
      CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) i j =
      oddKTheoryCircleCFC u (oddKTheoryRecoveryCircleEntry s i j) := rfl

theorem continuous_oddKTheoryRecoveryNestedUnitary (u : unitary (CStarMatrix ι ι A)) :
    Continuous (oddKTheoryRecoveryNestedUnitary u) := by
  apply Continuous.subtype_mk
  change Continuous (fun s : I => CStarMatrix.ofMatrix
    (fun i j : Fin 2 => oddKTheoryCircleCFC u (oddKTheoryRecoveryCircleEntry s i j)))
  exact CStarMatrix.ofMatrixL.continuous.comp
    (continuous_pi fun i => continuous_pi fun j =>
      (continuous_oddKTheoryCircleCFC u).comp (continuous_oddKTheoryRecoveryCircleEntry i j))

def oddKTheoryRecoveryFiniteUnitary (u : unitary (CStarMatrix ι ι A)) (s : I) :
    unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) :=
  oddKTheoryTwoBlockFlattenUnitary (oddKTheoryRecoveryNestedUnitary u s)

theorem continuous_oddKTheoryRecoveryFiniteUnitary (u : unitary (CStarMatrix ι ι A)) :
    Continuous (oddKTheoryRecoveryFiniteUnitary u) :=
  continuous_oddKTheoryTwoBlockFlattenUnitary.comp
    (continuous_oddKTheoryRecoveryNestedUnitary u)

theorem oddKTheoryRecoveryFunctionMatrix_zero :
    oddKTheoryRecoveryFunctionMatrix 0 = CStarMatrix.ofMatrix
      ![![(ContinuousMap.id ℂ).restrict (Metric.sphere 0 1), 0], ![0, 1]] := by
  change oddKTheoryRecoveryFunctionMatrix 0 = CStarMatrix.ofMatrix
    (!![(ContinuousMap.id ℂ).restrict (Metric.sphere 0 1), 0; 0, 1] :
      Matrix (Fin 2) (Fin 2) C(Circle, ℂ))
  apply CStarMatrix.ext
  intro i j
  apply ContinuousMap.ext
  intro z
  have h := oddKTheoryRecoveryCircleFamily_zero z
  change (oddKTheoryRecoveryCircleFamily z 0 : OddKTheoryRecoveryMatrix) =
    CStarMatrix.ofMatrix (!![(z : ℂ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) at h
  change (oddKTheoryRecoveryCircleFamily z 0 : OddKTheoryRecoveryMatrix) i j = _
  rw [h]
  fin_cases i <;> fin_cases j <;> rfl

theorem oddKTheoryRecoveryFiniteUnitary_zero (u : unitary (CStarMatrix ι ι A)) :
    oddKTheoryRecoveryFiniteUnitary u 0 = unitaryBlockSum u 1 := by
  apply Subtype.ext
  change oddKTheoryTwoBlockFlatten
    (matrixMap (oddKTheoryCircleCFC u) (oddKTheoryRecoveryFunctionMatrix 0)) = _
  rw [oddKTheoryRecoveryFunctionMatrix_zero]
  change oddKTheoryTwoBlockFlatten
    (matrixMap (oddKTheoryCircleCFC u) (CStarMatrix.ofMatrix
      !![(ContinuousMap.id ℂ).restrict (Metric.sphere 0 1), 0; 0, 1])) = _
  ext i j
  cases i <;> cases j <;>
    simp [unitaryBlockSum, matrixBlockSum, Matrix.fromBlocks, matrixMap_apply,
      CStarMatrix.ofMatrix_apply, oddKTheoryCircleCFC_coordinate]

/-- The recovered finite unitary is the actual four-entry exponential matrix. -/
def oddKTheoryFiniteExponentialRecovery (u : unitary (CStarMatrix ι ι A)) :
    unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) :=
  oddKTheoryRecoveryFiniteUnitary u 1

theorem oddKTheoryFiniteExponentialRecovery_entryMatrix
    (u : unitary (CStarMatrix ι ι A)) :
    (oddKTheoryFiniteExponentialRecovery u : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) =
      oddKTheoryTwoBlockFlatten (CStarMatrix.ofMatrix
        ![![1 + oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 0),
            oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 1)],
          ![oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 2),
            1 + oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 3)]]) := by
  change oddKTheoryTwoBlockFlatten
    (matrixMap (oddKTheoryCircleCFC u) (oddKTheoryRecoveryFunctionMatrix 1)) =
      oddKTheoryTwoBlockFlatten (CStarMatrix.ofMatrix
        !![1 + oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 0),
            oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 1);
          oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 2),
            1 + oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 3)])
  congr 1
  apply CStarMatrix.ext
  intro i j
  rw [matrixMap_apply]
  change oddKTheoryCircleCFC u (oddKTheoryRecoveryCircleEntry 1 i j) = _
  have h := oddKTheoryRecoveryCircleEntry_target i j
  change oddKTheoryRecoveryCircleEntry 1 i j =
    (CStarMatrix.ofMatrix
      (!![1 + oddKTheoryLoopExponentialCircleEntry 0,
          oddKTheoryLoopExponentialCircleEntry 1;
        oddKTheoryLoopExponentialCircleEntry 2,
          1 + oddKTheoryLoopExponentialCircleEntry 3] :
        Matrix (Fin 2) (Fin 2) C(Circle, ℂ))) i j at h
  rw [h]
  fin_cases i <;> fin_cases j
  · change oddKTheoryCircleCFC u (1 + oddKTheoryLoopExponentialCircleEntry 0) =
      1 + oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 0)
    rw [map_add, map_one]
  · rfl
  · rfl
  · change oddKTheoryCircleCFC u (1 + oddKTheoryLoopExponentialCircleEntry 3) =
      1 + oddKTheoryCircleCFC u (oddKTheoryLoopExponentialCircleEntry 3)
    rw [map_add, map_one]

/-- An actual norm-continuous finite matrix path joins the stabilization of
the given unitary to the four-entry exponential recovery matrix. -/
def oddKTheoryFiniteRecoveryPath (u : unitary (CStarMatrix ι ι A)) :
    Path (unitaryBlockSum u 1) (oddKTheoryFiniteExponentialRecovery u) where
  toFun := oddKTheoryRecoveryFiniteUnitary u
  continuous_toFun := continuous_oddKTheoryRecoveryFiniteUnitary u
  source' := oddKTheoryRecoveryFiniteUnitary_zero u
  target' := rfl

variable [PartialOrder A] [StarOrderedRing A]

theorem oddKTheoryFiniteExponentialRecovery_homotopic
    (u : MatrixUnitary A ι) :
    UnitaryHomotopic (unitaryBlockSum u 1) (oddKTheoryFiniteExponentialRecovery u) :=
  ⟨oddKTheoryFiniteRecoveryPath u⟩

/-- Recovery takes values in the project's existing stable unitary group. -/
theorem oddKTheoryFiniteExponentialRecovery_k1 {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : MatrixUnitary A ι) :
    K1.of (FiniteUnitary.ofUnitary (oddKTheoryFiniteExponentialRecovery u)) =
      K1.of (FiniteUnitary.ofUnitary u) := by
  rw [← K1.of_homotopic (oddKTheoryFiniteExponentialRecovery_homotopic u)]
  exact K1.of_stabilize (FiniteUnitary.ofUnitary u) ι


/-- Actual finite reindexing is available across independent index universes. -/
def oddKTheoryRecoveryReindexUnitary {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (u : MatrixUnitary A ι) : MatrixUnitary A κ :=
  ⟨CStarMatrix.reindexₐ ℂ A e (u : CStarMatrix ι ι A),
    Unitary.map_mem (CStarMatrix.reindexₐ ℂ A e) u.property⟩

/-- Present any finite index universe in the existing Type-0 stable quotient. -/
def oddKTheoryRecoveryFiniteUnitaryOfMatrix (u : MatrixUnitary A ι) : FiniteUnitary A :=
  FiniteUnitary.ofUnitary (oddKTheoryRecoveryReindexUnitary (Fintype.equivFin ι) u)

theorem oddKTheoryRecoveryFiniteUnitaryOfMatrix_homotopic
    {u v : MatrixUnitary A ι} (h : UnitaryHomotopic u v) :
    K1.of (oddKTheoryRecoveryFiniteUnitaryOfMatrix u) =
      K1.of (oddKTheoryRecoveryFiniteUnitaryOfMatrix v) := by
  let e := Fintype.equivFin ι
  change K1.of (FiniteUnitary.ofUnitary (oddKTheoryRecoveryReindexUnitary e u)) =
    K1.of (FiniteUnitary.ofUnitary (oddKTheoryRecoveryReindexUnitary e v))
  apply K1.of_homotopic
  have hc : Continuous (oddKTheoryRecoveryReindexUnitary (A := A) e) := by
    apply Continuous.subtype_mk
    exact (map_continuous (CStarMatrix.reindexₐ ℂ A e).toStarAlgHom).comp continuous_subtype_val
  exact h.map hc

/-- The finite-ordinal bridge agrees with the original constructor on Type-0 inputs. -/
theorem oddKTheoryRecoveryFiniteUnitaryOfMatrix_k1 {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : MatrixUnitary A ι) :
    K1.of (oddKTheoryRecoveryFiniteUnitaryOfMatrix u) =
      K1.of (FiniteUnitary.ofUnitary u) := by
  apply Quotient.sound
  apply FiniteUnitary.equivalent_symm
  exact FiniteUnitary.equivalent_reindex _ _ (Fintype.equivFin ι) rfl

/-- Identity stabilization is preserved by the true arbitrary-universe presentation. -/
theorem oddKTheoryRecoveryFiniteUnitaryOfMatrix_stabilize (u : MatrixUnitary A ι) :
    K1.of (oddKTheoryRecoveryFiniteUnitaryOfMatrix (unitaryBlockSum u (1 : MatrixUnitary A ι))) =
      K1.of (oddKTheoryRecoveryFiniteUnitaryOfMatrix u) := by
  let e := Fintype.equivFin ι
  let f := Fintype.equivFin (ι ⊕ ι)
  let k : Fin (Fintype.card (ι ⊕ ι)) ≃ Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι) :=
    f.symm.trans (e.sumCongr e)
  have hcoord :
      unitaryReindex k (oddKTheoryRecoveryReindexUnitary f (unitaryBlockSum u (1 : MatrixUnitary A ι))) =
        unitaryBlockSum (oddKTheoryRecoveryReindexUnitary e u)
          (1 : MatrixUnitary A (Fin (Fintype.card ι))) := by
    apply Subtype.ext
    apply CStarMatrix.ext
    intro i j
    change
      (unitaryBlockSum u (1 : MatrixUnitary A ι) :
        CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A)
          (f.symm (k.symm i)) (f.symm (k.symm j)) =
      (unitaryBlockSum (oddKTheoryRecoveryReindexUnitary e u)
        (1 : MatrixUnitary A (Fin (Fintype.card ι))) :
        CStarMatrix (Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι))
          (Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)) A) i j
    have hi : f.symm (k.symm i) = (e.sumCongr e).symm i := by
      simp only [k, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    have hj : f.symm (k.symm j) = (e.sumCongr e).symm j := by
      simp only [k, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    rw [hi, hj]
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change (1 : CStarMatrix ι ι A) (e.symm i) (e.symm j) =
          (1 : CStarMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A) i j
        simp only [CStarMatrix.one_apply, e.symm.injective.eq_iff]
  have hclass :
      K1.of (FiniteUnitary.ofUnitary
        (oddKTheoryRecoveryReindexUnitary f (unitaryBlockSum u (1 : MatrixUnitary A ι)))) =
      K1.of (FiniteUnitary.ofUnitary
        (unitaryBlockSum (oddKTheoryRecoveryReindexUnitary e u)
          (1 : MatrixUnitary A (Fin (Fintype.card ι))))) :=
    Quotient.sound (FiniteUnitary.equivalent_reindex
    (FiniteUnitary.ofUnitary (oddKTheoryRecoveryReindexUnitary f (unitaryBlockSum u (1 : MatrixUnitary A ι))))
    (FiniteUnitary.ofUnitary (unitaryBlockSum (oddKTheoryRecoveryReindexUnitary e u)
      (1 : MatrixUnitary A (Fin (Fintype.card ι))))) k hcoord)
  change K1.of (FiniteUnitary.ofUnitary
    (oddKTheoryRecoveryReindexUnitary f (unitaryBlockSum u (1 : MatrixUnitary A ι)))) = _
  exact hclass.trans (K1.of_stabilize
    (FiniteUnitary.ofUnitary (oddKTheoryRecoveryReindexUnitary e u)) (Fin (Fintype.card ι)))

/-- Full recovery in K₁ holds for arbitrary finite index universes through actual reindexing. -/
theorem oddKTheoryFiniteExponentialRecovery_k1_anyIndex (u : MatrixUnitary A ι) :
    K1.of (oddKTheoryRecoveryFiniteUnitaryOfMatrix (oddKTheoryFiniteExponentialRecovery u)) =
      K1.of (oddKTheoryRecoveryFiniteUnitaryOfMatrix u) := by
  exact (oddKTheoryRecoveryFiniteUnitaryOfMatrix_homotopic
    (oddKTheoryFiniteExponentialRecovery_homotopic u)).symm.trans
      (oddKTheoryRecoveryFiniteUnitaryOfMatrix_stabilize u)

end BC4lean.KKTheory
