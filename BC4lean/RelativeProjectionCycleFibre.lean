import BC4lean.RelativeProjectionTransport
import BC4lean.OddFredholmProjectionFibreEquiv
import BC4lean.HilbertModuleFibreSum
import BC4lean.IntervalKasparovFibre

/-! # Actual fibres of a compact-relative projection cycle

This construction applies to any complete countably generated module over
continuous coefficient functions, including the image mapping-cylinder
module. The actual range-fibre unitaries and sum-fibre unitary identify the
whole cycle with the relative cycle of the evaluated projections. No
continuous-section presentation of the module is required.
-/

noncomputable section
namespace BC4lean.KKTheory

universe uΓ
open scoped CStarAlgebra

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

def relativeProjectionPairFibreEquiv
    (P Q : AdjointableMap C(X, B) M M) (hP : IsStarProjection P) (hQ : IsStarProjection Q) (t : X) :
    HilbertModuleEquiv B
      (HilbertModuleFibre B (HilbertModuleSum C(X, B) (ProjectionModule P) (ProjectionModule Q)) t)
      (HilbertModuleSum B (ProjectionModule (hilbertModuleFibreOperator (B := B) t P))
        (ProjectionModule (hilbertModuleFibreOperator (B := B) t Q))) :=
  (hilbertModuleFibreSumEquiv t).trans
    ((oddFredholmProjectionFibreEquiv P hP t).sum (oddFredholmProjectionFibreEquiv Q hQ t))

@[simp] theorem relativeProjectionPairFibreEquiv_mk
    (P Q : AdjointableMap C(X, B) M M) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (t : X) (x : HilbertModuleSum C(X, B) (ProjectionModule P) (ProjectionModule Q)) :
    relativeProjectionPairFibreEquiv P Q hP hQ t (hilbertModuleFibreMk (B := B) t x) =
      sumMk (oddFredholmProjectionFibreEquiv P hP t (hilbertModuleFibreMk (B := B) t x.fst))
        (oddFredholmProjectionFibreEquiv Q hQ t (hilbertModuleFibreMk (B := B) t x.snd)) := by
  simp only [relativeProjectionPairFibreEquiv, HilbertModuleEquiv.trans_apply,
    hilbertModuleFibreSumEquiv_mk, HilbertModuleEquiv.sum_apply, sumMk_fst, sumMk_snd]

omit [T2Space X] in
theorem relativeProjectionFibre_difference_compact
    (P Q : AdjointableMap C(X, B) M M) (hc : IsModuleCompact (P - Q)) (t : X) :
    IsModuleCompact (hilbertModuleFibreOperator (B := B) t P - hilbertModuleFibreOperator t Q) := by
  rw [← hilbertModuleFibreOperator_sub]
  exact hc.fibre t

set_option maxHeartbeats 1200000 in
def relativeProjectionCycleFibreIso
    (P Q : AdjointableMap C(X, B) M M) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) (hM : IsCountablyGeneratedModule C(X, B) M) (t : X) :
    KasparovCycleIso ((relativeProjectionCycle (Γ := PUnit.{uΓ + 1}) P Q hP hQ hc hM).fibre t)
      (relativeProjectionCycle (Γ := PUnit.{uΓ + 1}) (hilbertModuleFibreOperator (B := B) t P)
        (hilbertModuleFibreOperator t Q)
        (hP.map (hilbertModuleFibreOperatorHom t)) (hQ.map (hilbertModuleFibreOperatorHom t))
        (relativeProjectionFibre_difference_compact P Q hc t) (hM.fibre t)) where
  moduleEquiv := relativeProjectionPairFibreEquiv P Q hP hQ t
  grading_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
      (M := HilbertModuleSum C(X, B) (ProjectionModule P) (ProjectionModule Q)) t z
    change relativeProjectionPairFibreEquiv P Q hP hQ t
      (((relativeProjectionCycle (Γ := PUnit.{uΓ + 1}) P Q hP hQ hc hM).grading.fibre t).grading
        (hilbertModuleFibreMk (B := B) t x)) = _
    rw [GradedHilbertModule.fibre_grading_mk]
    change relativeProjectionPairFibreEquiv P Q hP hQ t
      (hilbertModuleFibreMk (B := B) t (sumMk x.fst (-x.snd))) =
        sumMk ((relativeProjectionPairFibreEquiv P Q hP hQ t
          (hilbertModuleFibreMk (B := B) t x)).fst)
          (-((relativeProjectionPairFibreEquiv P Q hP hQ t
            (hilbertModuleFibreMk (B := B) t x)).snd))
    rw [relativeProjectionPairFibreEquiv_mk, relativeProjectionPairFibreEquiv_mk]
    simp only [sumMk_fst, sumMk_snd, map_neg]
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
      (M := HilbertModuleSum C(X, B) (ProjectionModule P) (ProjectionModule Q)) t z
    change relativeProjectionPairFibreEquiv P Q hP hQ t
      (hilbertModuleFibreLinearIsometryEquiv t
        ((relativeProjectionCycle (Γ := PUnit.{uΓ + 1}) P Q hP hQ hc hM).groupAction.action g).toLinearEquiv
        (by
          intro y
          change PositiveModuleForm.formNorm (B := B)
              (evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t y)) =
            PositiveModuleForm.formNorm (B := B) y
          rw [evaluatedModule_of_to])
        (hilbertModuleFibreMk (B := B) t x)) =
      relativeProjectionPairFibreEquiv P Q hP hQ t (hilbertModuleFibreMk (B := B) t x)
    rw [hilbertModuleFibreLinearIsometryEquiv_mk]
    rfl
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
      (M := HilbertModuleSum C(X, B) (ProjectionModule P) (ProjectionModule Q)) t z
    change relativeProjectionPairFibreEquiv P Q hP hQ t
      (hilbertModuleFibreOperator t
        ((relativeProjectionCycle (Γ := PUnit.{uΓ + 1}) P Q hP hQ hc hM).representation a)
        (hilbertModuleFibreMk (B := B) t x)) = _
    rw [hilbertModuleFibreOperator_mk]
    change relativeProjectionPairFibreEquiv P Q hP hQ t
      (hilbertModuleFibreMk (B := B) t (a • x)) =
        a • relativeProjectionPairFibreEquiv P Q hP hQ t (hilbertModuleFibreMk (B := B) t x)
    rw [map_smul, HilbertModuleEquiv.map_smul]
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
      (M := HilbertModuleSum C(X, B) (ProjectionModule P) (ProjectionModule Q)) t z
    change relativeProjectionPairFibreEquiv P Q hP hQ t
      (hilbertModuleFibreOperator t (offDiagonalAdjointable (projectionCrossMap P Q hP hQ))
        (hilbertModuleFibreMk (B := B) t x)) =
      offDiagonalAdjointable (projectionCrossMap
        (hilbertModuleFibreOperator (B := B) t P) (hilbertModuleFibreOperator t Q)
        (hP.map (hilbertModuleFibreOperatorHom t)) (hQ.map (hilbertModuleFibreOperatorHom t)))
        (relativeProjectionPairFibreEquiv P Q hP hQ t (hilbertModuleFibreMk (B := B) t x))
    rw [hilbertModuleFibreOperator_mk, relativeProjectionPairFibreEquiv_mk,
      relativeProjectionPairFibreEquiv_mk]
    apply Prod.ext <;> apply Subtype.ext
    · simp only [offDiagonalAdjointable_apply, projectionCrossMap_adjoint,
        sumMk_fst, sumMk_snd, oddFredholmProjectionFibreEquiv_mk, projectionCrossMap_coe]
      change hilbertModuleFibreMk (B := B) t (P (x.snd : M)) =
        hilbertModuleFibreOperator (B := B) t P
          ((oddFredholmProjectionFibreEquiv Q hQ t
            (hilbertModuleFibreMk (B := B) t x.snd) :
              ProjectionModule (hilbertModuleFibreOperator (B := B) t Q)) : HilbertModuleFibre B M t)
      rw [oddFredholmProjectionFibreEquiv_mk, hilbertModuleFibreOperator_mk]
    · simp only [offDiagonalAdjointable_apply, sumMk_snd, sumMk_fst,
        oddFredholmProjectionFibreEquiv_mk, projectionCrossMap_coe]
      change hilbertModuleFibreMk (B := B) t (Q (x.fst : M)) =
        hilbertModuleFibreOperator (B := B) t Q
          ((oddFredholmProjectionFibreEquiv P hP t
            (hilbertModuleFibreMk (B := B) t x.fst) :
              ProjectionModule (hilbertModuleFibreOperator (B := B) t P)) : HilbertModuleFibre B M t)
      rw [oddFredholmProjectionFibreEquiv_mk, hilbertModuleFibreOperator_mk]

end BC4lean.KKTheory
