import BC4lean.OddFredholmFiniteIndexUnitary
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Genuine compression of compact unitaries with an exact finite identity tail

Actual supported unitaries compress to genuine finite unitization matrices.
The construction retains continuity of actual norm paths, and its represented
operator reconstructs the original whole completed-module unitary.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped CStarAlgebra

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem oddFredholmSupportedUnitary_commutes_cutoff
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    Commute (standardCountableCutoff n) (U : OddFredholmStandardOperator B) := by
  have hl := oddFredholmUnitary_left_tail U (1 - standardCountableCutoff n)
    (by rw [star_sub, star_one, standardCountableCutoff_star]) hU
  rw [mul_sub, mul_one] at hU
  rw [sub_mul, one_mul] at hl
  rw [commute_iff_eq]
  exact sub_right_inj.mp (hl.trans hU.symm)

def oddFredholmSupportedUnitaryCompression
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) :=
  ⟨((oddFredholmStandardFiniteInclusion (B := B) n).adjoint.comp
      (U : OddFredholmStandardOperator B)).comp
      (oddFredholmStandardFiniteInclusion (B := B) n),
    oddFredholmIsometricCompression_mem_unitary _
      (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n) U (by
        rw [oddFredholmStandardFiniteInclusion_comp_adjoint]
        exact oddFredholmSupportedUnitary_commutes_cutoff U n hU)⟩

theorem oddFredholmSupportedUnitaryCompression_sub_one_isModuleCompact
    (U : unitary (OddFredholmStandardOperator B))
    (hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    IsModuleCompact ((oddFredholmSupportedUnitaryCompression U n hU :
      AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) - 1) := by
  have h := (hCompact.comp_left (oddFredholmStandardFiniteInclusion (B := B) n).adjoint).comp_right
    (oddFredholmStandardFiniteInclusion (B := B) n)
  convert h using 1
  apply AdjointableMap.ext
  intro x
  simp only [oddFredholmSupportedUnitaryCompression, AdjointableMap.comp_apply,
    AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    (oddFredholmStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_sub]
  have hi := congrArg (fun T => T x)
    (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
    congrArg (fun z => (oddFredholmStandardFiniteInclusion (B := B) n).adjoint
      ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x)) - z) hi.symm

def oddFredholmSupportedFiniteUnitary
    (U : unitary (OddFredholmStandardOperator B))
    (hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    unitary (CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) :=
  oddFredholmFiniteCompactUnitary (oddFredholmSupportedUnitaryCompression U n hU)
    (oddFredholmSupportedUnitaryCompression_sub_one_isModuleCompact U hCompact n hU)

theorem oddFredholmSupportedFiniteUnitary_scalar
    (U : unitary (OddFredholmStandardOperator B))
    (hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    unitizationScalarMatrix (oddFredholmSupportedFiniteUnitary U hCompact n hU :
      CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) = 1 :=
  oddFredholmFiniteCompactUnitaryMatrix_scalar _ _

theorem oddFredholmSupportedUnitaryCompression_reinclude
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    1 + ((oddFredholmStandardFiniteInclusion (B := B) n).comp
      ((oddFredholmSupportedUnitaryCompression U n hU :
        AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) - 1)).comp
      (oddFredholmStandardFiniteInclusion (B := B) n).adjoint = (U : OddFredholmStandardOperator B) := by
  have hs : (U : OddFredholmStandardOperator B) - 1 =
      standardCountableCutoff n * ((U : OddFredholmStandardOperator B) - 1) *
        standardCountableCutoff n := by
    have hr : ((U : OddFredholmStandardOperator B) - 1) * (1 - standardCountableCutoff n) = 0 := by
      rw [sub_mul, hU, one_mul, sub_self]
    have hl : (1 - standardCountableCutoff n) * ((U : OddFredholmStandardOperator B) - 1) = 0 := by
      rw [mul_sub, oddFredholmUnitary_left_tail U _
        (by rw [star_sub, star_one, standardCountableCutoff_star]) hU, mul_one, sub_self]
    rw [mul_sub, mul_one] at hr
    rw [sub_mul, one_mul] at hl
    rw [← sub_eq_zero.mp hl, ← sub_eq_zero.mp hr]
  have he : ((oddFredholmStandardFiniteInclusion (B := B) n).comp
      ((oddFredholmSupportedUnitaryCompression U n hU :
        AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) - 1)).comp
      (oddFredholmStandardFiniteInclusion (B := B) n).adjoint =
      standardCountableCutoff n * ((U : OddFredholmStandardOperator B) - 1) * standardCountableCutoff n := by
    rw [← oddFredholmStandardFiniteInclusion_comp_adjoint]
    apply AdjointableMap.ext
    intro x
    simp only [oddFredholmSupportedUnitaryCompression, AdjointableMap.comp_apply,
      AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
      (oddFredholmStandardFiniteInclusion (B := B) n).toCLM.map_sub]
    rw [(oddFredholmStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_sub,
      (oddFredholmStandardFiniteInclusion (B := B) n).toCLM.map_sub]
    have hi := congrArg (fun T => T ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint x))
      (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n)
    simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
      congrArg (fun z => oddFredholmStandardFiniteInclusion (B := B) n
        ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint
          ((U : OddFredholmStandardOperator B)
            (oddFredholmStandardFiniteInclusion (B := B) n ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint x)))) -
          oddFredholmStandardFiniteInclusion (B := B) n z) hi.symm
  rw [he, ← hs]
  abel

section Continuity

variable {X : Type*} [TopologicalSpace X]

theorem continuous_oddFredholmFiniteCompactUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : X → unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)))
    (hv : ∀ x, IsModuleCompact ((v x : AdjointableMap B
      (FiniteStandardModule B ι) (FiniteStandardModule B ι)) - 1)) (hc : Continuous v) :
    Continuous (fun x => oddFredholmFiniteCompactUnitary (v x) (hv x)) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (continuous_unitizationCoefficientMatrix.comp
    (continuous_finiteModuleCompactMatrix _ hv ((continuous_subtype_val.comp hc).sub continuous_const)))

theorem continuous_oddFredholmSupportedUnitaryCompression
    (U : X → unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : ∀ x, (U x : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) (hc : Continuous U) :
    Continuous (fun x => oddFredholmSupportedUnitaryCompression (U x) n (hU x)) := by
  apply Continuous.subtype_mk
  exact (AdjointableMap.compRightContinuousLinearMap (oddFredholmStandardFiniteInclusion (B := B) n)).continuous.comp
    ((AdjointableMap.compLeftContinuousLinearMap (oddFredholmStandardFiniteInclusion (B := B) n).adjoint).continuous.comp
      (continuous_subtype_val.comp hc))

theorem continuous_oddFredholmSupportedFiniteUnitary
    (U : X → unitary (OddFredholmStandardOperator B))
    (hCompact : ∀ x, IsModuleCompact ((U x : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : ∀ x, (U x : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) (hc : Continuous U) :
    Continuous (fun x => oddFredholmSupportedFiniteUnitary (U x) (hCompact x) n (hU x)) :=
  continuous_oddFredholmFiniteCompactUnitary _ _
    (continuous_oddFredholmSupportedUnitaryCompression U n hU hc)

end Continuity
end BC4lean.KKTheory
