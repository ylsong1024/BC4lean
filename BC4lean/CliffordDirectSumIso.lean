import BC4lean.GradedKasparovDirectSum
import BC4lean.CliffordCycleIso
import BC4lean.OddKasparovDirectSumIso

/-! # The actual unitary comparing Clifford pairs and Hilbert direct sums

The permutation ((x₊,x₋),(y₊,y₋)) ↦ ((x₊,y₊),(x₋,y₋))
preserves the B×B-valued inner product. This identifies the genuine
coefficient-Hilbert direct sum of two Clifford expansions with the Clifford
expansion of the genuine B-Hilbert direct sum.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace
variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def cliffordPairSumEquiv :
    HilbertModuleEquiv (B × B)
      (HilbertModuleSum (B × B) (CliffordPairModule B E) (CliffordPairModule B F))
      (CliffordPairModule B (HilbertModuleSum B E F)) := by
  let L : HilbertModuleSum (B × B) (CliffordPairModule B E) (CliffordPairModule B F) →ₗ[ℂ]
      CliffordPairModule B (HilbertModuleSum B E F) :=
    { toFun x := cliffordPairMk (sumMk x.fst.1 x.snd.1) (sumMk x.fst.2 x.snd.2)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hinner (x y : HilbertModuleSum (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) :
      ⟪L x, L y⟫_((B × B)ᵐᵒᵖ) = ⟪x, y⟫_((B × B)ᵐᵒᵖ) := by
    apply MulOpposite.unop_injective
    apply Prod.ext <;> simp only [L, cliffordPair_inner, inner_sum,
      MulOpposite.unop_op, MulOpposite.unop_add] <;> rfl
  exact
    { linearIsometryEquiv :=
        { toFun := L
          invFun y := sumMk (cliffordPairMk y.1.fst y.2.fst) (cliffordPairMk y.1.snd y.2.snd)
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' := L.map_add
          map_smul' := L.map_smul
          norm_map' x := by
            change ‖L x‖ = ‖x‖
            calc
              ‖L x‖ = Real.sqrt ‖⟪L x, L x⟫_((B × B)ᵐᵒᵖ)‖ :=
                CStarModule.norm_eq_sqrt_norm_inner_self
                  (A := (B × B)ᵐᵒᵖ) (E := CliffordPairModule B (HilbertModuleSum B E F)) (L x)
              _ = Real.sqrt ‖⟪x, x⟫_((B × B)ᵐᵒᵖ)‖ :=
                congrArg (fun a : (B × B)ᵐᵒᵖ => Real.sqrt ‖a‖) (hinner x x)
              _ = ‖x‖ :=
                (CStarModule.norm_eq_sqrt_norm_inner_self (A := (B × B)ᵐᵒᵖ)
                  (E := HilbertModuleSum (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) x).symm }
      inner_map := hinner }

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem cliffordPairSumEquiv_apply
    (x : HilbertModuleSum (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) :
    cliffordPairSumEquiv x = cliffordPairMk (sumMk x.fst.1 x.snd.1) (sumMk x.fst.2 x.snd.2) := rfl

def OddKasparovCycle.cliffordExpansionDirectSumIso (c : OddKasparovCycle α β E)
    (d : OddKasparovCycle α β F) :
    GradedKasparovCycleIso (c.cliffordExpansion.directSum d.cliffordExpansion)
      (c.directSum d).cliffordExpansion where
  moduleEquiv := cliffordPairSumEquiv
  grading_intertwine x := rfl
  action_intertwine g x := rfl
  representation_intertwine a x := by
    change cliffordPairSumEquiv
      (sumMap (cliffordPairMap (c.representation a) (c.representation a))
        (cliffordPairMap (d.representation a) (d.representation a)) x) =
      cliffordPairMap (sumMap (c.representation a) (d.representation a))
        (sumMap (c.representation a) (d.representation a)) (cliffordPairSumEquiv x)
    simp only [sumMap_apply, cliffordPairMap_apply, cliffordPairSumEquiv_apply, sumMk_fst, sumMk_snd]
    rfl
  operator_intertwine x := by
    change cliffordPairSumEquiv
      (sumMap (cliffordPairMap c.operator (-c.operator)) (cliffordPairMap d.operator (-d.operator)) x) =
      cliffordPairMap (sumMap c.operator d.operator) (-(sumMap c.operator d.operator))
        (cliffordPairSumEquiv x)
    simp only [sumMap_apply, cliffordPairMap_apply, cliffordPairSumEquiv_apply, sumMk_fst,
      sumMk_snd, AdjointableMap.coe_neg_apply]
    rfl

section ReconstructionSum
variable {M N : Type*}
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (B × B)ᵐᵒᵖ M] [CStarModule (B × B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul (B × B)ᵐᵒᵖ N] [CStarModule (B × B)ᵐᵒᵖ N] [CompleteSpace N]

/-- The raw graded sum is reconstructed by the actual sum of the two
reconstruction unitaries followed by the actual pair-sum permutation. -/
def GradedKasparovCycle.cliffordReconstructionDirectSumIso
    (c : GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading M)
    (d : GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading N) :
    GradedKasparovCycleIso (c.directSum d)
      ((cliffordExtractOddCycle true c).directSum (cliffordExtractOddCycle true d)).cliffordExpansion :=
  (c.cliffordReconstructionIso.directSum d.cliffordReconstructionIso).trans
    ((cliffordExtractOddCycle true c).cliffordExpansionDirectSumIso (cliffordExtractOddCycle true d))

end ReconstructionSum
end BC4lean.KKTheory
