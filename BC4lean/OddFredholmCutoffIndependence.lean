import BC4lean.OddFredholmFiniteCompressionStabilization

/-! # Genuine cutoff independence of the actual odd OperatorK1 index

The concrete polar comparison path lies in a common finite corner. The proved
actual identity-stabilization calculation identifies its endpoints with the
original finite matrices in the existing K1 quotient. Thus every admissible
cutoff gives the same element of the genuine scalar-kernel OperatorK1(B).
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open BC4lean.OperatorKTheory
open scoped CStarAlgebra

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance oddContinuationOddFredholmCutoffIndependenceLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmCutoffIndependenceLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddFredholmCutoffIndependenceLocalInstance03 : PartialOrder (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmCutoffIndependenceLocalInstance04 : StarOrderedRing (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrderedRing _

theorem oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1) :
    IsModuleCompact ((oddFredholmStandardCutoffPolarUnitary U n hn : OddFredholmStandardOperator B) - 1) :=
  oddFredholmPolarElement_sub_one_isModuleCompact _
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U hn)
    (oddFredholmUnitaryCutoff_sub_one_isModuleCompact U hU n)

def oddFredholmCutoffComparisonFinitePath
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) :
    Path (oddFredholmCutoffComparisonFiniteUnitary U hU n m hn hm 0)
      (oddFredholmCutoffComparisonFiniteUnitary U hU n m hn hm 1) where
  toFun := oddFredholmCutoffComparisonFiniteUnitary U hU n m hn hm
  continuous_toFun := continuous_oddFredholmCutoffComparisonFiniteUnitary U hU n m hn hm
  source' := rfl
  target' := rfl

/-- Any two actual radius-one cutoffs give equal classes in the existing
stable finite-unitary K1 group. Both cutoff conditions are concrete analytic
criteria, already eventually proved for every compact standard unitary. -/
theorem oddFredholmStandardFiniteIndexUnitary_k1_independent
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) :
    K1.of (FiniteUnitary.ofUnitary (oddFredholmStandardFiniteIndexUnitary U hU n hn)) =
      K1.of (FiniteUnitary.ofUnitary (oddFredholmStandardFiniteIndexUnitary U hU m hm)) := by
  have h0 := oddFredholmSupportedFiniteUnitary_k1_stabilization
    (oddFredholmStandardCutoffPolarUnitary U n hn)
    (oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact U hU n hn) n m
    (oddFredholmStandardCutoffPolarUnitary_right_tail U n hn)
  have h0' : K1.of (FiniteUnitary.ofUnitary
      (oddFredholmCutoffComparisonFiniteUnitary U hU n m hn hm 0)) =
      K1.of (FiniteUnitary.ofUnitary (oddFredholmStandardFiniteIndexUnitary U hU n hn)) := by
    simpa only [oddFredholmCutoffComparisonFiniteUnitary, oddFredholmCutoffComparisonUnitary_zero,
      oddFredholmSupportedFiniteUnitary, oddFredholmSupportedUnitaryCompression,
      oddFredholmStandardFiniteIndexUnitary, oddFredholmStandardFinitePolarUnitary] using h0
  have h1 := oddFredholmSupportedFiniteUnitary_k1_stabilization
    (oddFredholmStandardCutoffPolarUnitary U m hm)
    (oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact U hU m hm) m n
    (oddFredholmStandardCutoffPolarUnitary_right_tail U m hm)
  have h1' : K1.of (FiniteUnitary.ofUnitary
      (oddFredholmCutoffComparisonFiniteUnitary U hU n m hn hm 1)) =
      K1.of (FiniteUnitary.ofUnitary (oddFredholmStandardFiniteIndexUnitary U hU m hm)) := by
    let V := oddFredholmStandardCutoffPolarUnitary U m hm
    have hCompactV := oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact U hU m hm
    let P : ℕ → Prop := fun N =>
      ∀ hTail : (V : OddFredholmStandardOperator B) * (1 - standardCountableCutoff N) =
          1 - standardCountableCutoff N,
        K1.of (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary V hCompactV N hTail)) =
          K1.of (FiniteUnitary.ofUnitary (oddFredholmStandardFiniteIndexUnitary U hU m hm))
    have h1P : P (m + n) := by
      intro hTail
      simpa only [oddFredholmSupportedFiniteUnitary, oddFredholmSupportedUnitaryCompression,
        oddFredholmStandardFiniteIndexUnitary, oddFredholmStandardFinitePolarUnitary] using h1
    have h1P' : P (n + m) := Eq.mp (congrArg P (Nat.add_comm m n)) h1P
    have hTail : (V : OddFredholmStandardOperator B) * (1 - standardCountableCutoff (n + m)) =
        1 - standardCountableCutoff (n + m) := by
      simpa only [oddFredholmCutoffComparisonUnitary_one] using
        oddFredholmCutoffComparisonUnitary_tail U n m hn hm 1
    simpa only [oddFredholmCutoffComparisonFiniteUnitary,
      oddFredholmCutoffComparisonUnitary_one, oddFredholmSupportedFiniteUnitary,
      oddFredholmSupportedUnitaryCompression] using h1P' hTail
  exact h0'.symm.trans ((K1.of_homotopic ⟨oddFredholmCutoffComparisonFinitePath U hU n m hn hm⟩).trans h1')

theorem oddFredholmStandardFiniteIndexUnitary_operatorK1_independent
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) :
    oddFredholmScalarIdentityUnitaryIndex (oddFredholmStandardFiniteIndexUnitary U hU n hn)
        (oddFredholmStandardFiniteIndexUnitary_scalar U hU n hn) =
      oddFredholmScalarIdentityUnitaryIndex (oddFredholmStandardFiniteIndexUnitary U hU m hm)
        (oddFredholmStandardFiniteIndexUnitary_scalar U hU m hm) := by
  apply Subtype.ext
  exact oddFredholmStandardFiniteIndexUnitary_k1_independent U hU n m hn hm

theorem oddFredholmStandardUnitaryIndex_eq_cutoff
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1) :
    oddFredholmStandardUnitaryIndex U hU =
      oddFredholmScalarIdentityUnitaryIndex (oddFredholmStandardFiniteIndexUnitary U hU n hn)
        (oddFredholmStandardFiniteIndexUnitary_scalar U hU n hn) :=
  oddFredholmStandardFiniteIndexUnitary_operatorK1_independent U hU
    (oddFredholmStandardIndexSize U hU) n (oddFredholmStandardIndexSize_near U hU) hn

end BC4lean.KKTheory
