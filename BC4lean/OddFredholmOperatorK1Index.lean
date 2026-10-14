import BC4lean.OddFredholmFiniteIndexUnitary
import BC4lean.NonunitalOperatorK

/-! # The genuine finite-cutoff odd index takes values in OperatorK1(B)

A genuine scalar-identity finite matrix unitary defines an element of the
project's actual scalar-kernel OperatorK1. Strong compact cutoffs provide
the concrete eventual polar criterion, so every compact standard-module
unitary, and every genuine selfadjoint Fredholm operator, has an actual
finite matrix index value. Homotopy invariance and cutoff independence are
subsequent descent obligations; no odd comparison is asserted here.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance oddContinuationOddFredholmOperatorK1IndexLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmOperatorK1IndexLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddFredholmOperatorK1IndexLocalInstance03 : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmOperatorK1IndexLocalInstance04 : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

/-- A full scalar-identity finite matrix unitary represents an element of
the actual scalar kernel defining the project's OperatorK1(B). -/
def oddFredholmScalarIdentityUnitaryIndex {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hv : unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OperatorKTheory.OperatorK1 B :=
  ⟨OperatorKTheory.K1.of (OperatorKTheory.FiniteUnitary.ofUnitary v), by
    change OperatorKTheory.k1Map (OperatorKTheory.scalarQuotient B)
      (OperatorKTheory.K1.of (OperatorKTheory.FiniteUnitary.ofUnitary v)) = 0
    rw [OperatorKTheory.k1Map_of]
    have hh : OperatorKTheory.matrixUnitaryMap (OperatorKTheory.scalarQuotient B) v =
        (1 : unitary (CStarMatrix ι ι ℂ)) := by
      apply Subtype.ext
      exact hv
    change OperatorKTheory.K1.of (OperatorKTheory.FiniteUnitary.ofUnitary
      (OperatorKTheory.matrixUnitaryMap (OperatorKTheory.scalarQuotient B) v)) = 0
    rw [hh]
    exact OperatorKTheory.K1.of_identity ι⟩

/-- Choose only a size whose concrete radius-one criterion has already
been derived from the actual compact strong cutoffs. -/
def oddFredholmStandardIndexSize (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) : ℕ :=
  Classical.choose (oddFredholmUnitaryCutoff_eventually_near U hU).exists

theorem oddFredholmStandardIndexSize_near (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    ‖oddFredholmUnitaryCutoff U (oddFredholmStandardIndexSize U hU) -
      (U : OddFredholmStandardOperator B)‖ < 1 :=
  Classical.choose_spec (oddFredholmUnitaryCutoff_eventually_near U hU).exists

/-- The concrete finite-cutoff polar index of an actual compact standard
module unitary, with values in the project's actual OperatorK1(B). -/
def oddFredholmStandardUnitaryIndex (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    OperatorKTheory.OperatorK1 B :=
  oddFredholmScalarIdentityUnitaryIndex
    (oddFredholmStandardFiniteIndexUnitary U hU (oddFredholmStandardIndexSize U hU)
      (oddFredholmStandardIndexSize_near U hU))
    (oddFredholmStandardFiniteIndexUnitary_scalar U hU (oddFredholmStandardIndexSize U hU)
      (oddFredholmStandardIndexSize_near U hU))

/-- The actual exponential finite matrix index for a selfadjoint standard
Fredholm operator. The compact exponential defect is proved by full CFC. -/
def oddFredholmStandardIndex (F : selfAdjoint (OddFredholmStandardOperator B))
    (hF : IsModuleCompact ((F : OddFredholmStandardOperator B) ^ 2 - 1)) :
    OperatorKTheory.OperatorK1 B :=
  oddFredholmStandardUnitaryIndex (oddFredholmExponential F)
    (oddFredholmExponential_sub_one_isModuleCompact F hF)

end BC4lean.KKTheory
