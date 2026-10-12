import BC4lean.CliffordOddSourceCycle
import BC4lean.GradedKasparovDirectSum
import BC4lean.GradedKasparovCycleIso

/-! # Genuine direct sum compatibility of the signed odd source cycle

The actual complete four-coordinate shuffle preserves the whole
coefficient-valued form and intertwines all cycle data, including σ_y D.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddSourceCycle
open scoped InnerProductSpace

variable {Γ B C H K : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℂ K] [SMul Cᵐᵒᵖ K]
  [CStarModule Cᵐᵒᵖ K] [CompleteSpace K]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

local instance cliffordOddSourceDirectSumIsoLocalInstance1 : CompleteSpace (HilbertModuleSum C H K) := hilbertModuleSum_complete
local instance cliffordOddSourceDirectSumIsoLocalInstance2 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete
local instance cliffordOddSourceDirectSumIsoLocalInstance3 : CompleteSpace (HilbertModuleSum C K K) := hilbertModuleSum_complete

def sourceSumShuffle : HilbertModuleEquiv C
    (HilbertModuleSum C (HilbertModuleSum C H K) (HilbertModuleSum C H K))
    (HilbertModuleSum C (HilbertModuleSum C H H) (HilbertModuleSum C K K)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)
          invFun x := sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      norm_map' x := by
        change ‖sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)
          (sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)),
          CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) x]
        congr 2
        simp only [inner_sum, sumMk_fst, sumMk_snd]
        abel }
  inner_map x y := by
    change ⟪sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd),
      sumMk (sumMk y.fst.fst y.snd.fst) (sumMk y.fst.snd y.snd.snd)⟫_(Cᵐᵒᵖ) =
        ⟪x, y⟫_(Cᵐᵒᵖ)
    simp only [inner_sum, sumMk_fst, sumMk_snd]
    abel

/-- The source construction preserves actual graded direct sum by a full unitary. -/
def directSumIso (c : OddKasparovCycle β γ H) (d : OddKasparovCycle β γ K) :
    GradedKasparovCycleIso (cycle (c.directSum d)) ((cycle c).directSum (cycle d)) where
  moduleEquiv := sourceSumShuffle
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine b x := by
    change sourceSumShuffle
      (sumMap (sumMap (c.representation b.1) (d.representation b.1))
        (sumMap (c.representation b.2) (d.representation b.2)) x) =
      sumMap (sumMap (c.representation b.1) (c.representation b.2))
        (sumMap (d.representation b.1) (d.representation b.2)) (sourceSumShuffle x)
    have hShuffle (z :
        HilbertModuleSum C (HilbertModuleSum C H K) (HilbertModuleSum C H K)) :
        sourceSumShuffle z =
          sumMk (sumMk z.fst.fst z.snd.fst) (sumMk z.fst.snd z.snd.snd) := rfl
    simp only [sumMap_apply, hShuffle, sumMk_fst, sumMk_snd]
  operator_intertwine x := by
    change sourceSumShuffle (operator (sumMap c.operator d.operator) x) =
      sumMap (operator c.operator) (operator d.operator) (sourceSumShuffle x)
    have hShuffle (z :
        HilbertModuleSum C (HilbertModuleSum C H K) (HilbertModuleSum C H K)) :
        sourceSumShuffle z =
          sumMk (sumMk z.fst.fst z.snd.fst) (sumMk z.fst.snd z.snd.snd) := rfl
    simp only [operator_apply, sumMap_apply, hShuffle, sumMk_smul,
      sumMk_fst, sumMk_snd]

end BC4lean.KKTheory.CliffordOddSourceCycle
