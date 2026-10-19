import BC4lean.ReducedCrossedScalarProduct
import BC4lean.KasparovDescentModule
import BC4lean.ScalarKasparovK0ComparisonAddEquiv
import BC4lean.GroupUniverseOddFullComparison
import BC4lean.GroupUniverseParityGroup
import BC4lean.OperatorKUnitalAgreement
import BC4lean.ReducedOperatorK1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual scalar crossed KK to reduced analytic K-theory maps

These maps compose the existing genuine scalar
KK/operator K-theory equivalences, the forward map of the actual scalar
crossed-product equivalence, and the existing unital agreement. Both analytic
targets are exactly the established ReducedK0 and ReducedK1. No unital
structure on the scalar crossed product is postulated.
-/

noncomputable section
universe uΓ uE
namespace BC4lean.Assembly
open KKTheory OperatorKTheory KKTheory.GroupUniverseParityGroup
open scoped KasparovDescent ComplexOrder

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]

/-- The parity family consists of the existing two analytic target groups. -/
def analyticGroup (p : Bool) : Type _ :=
  match p with
  | false => ReducedK0 Γ
  | true => ReducedK1 Γ

instance analyticGroup_addCommGroup (p : Bool) : AddCommGroup (analyticGroup Γ p) := by
  cases p <;> dsimp [analyticGroup] <;> infer_instance

/-- The genuine Julia-index comparison followed by the actual scalar
crossed-to-group-algebra map and canonical unital K0 agreement. -/
def reducedScalarKKToK0Hom :
    KasparovHomotopyClass.{0, 0, uΓ, uE}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))) →+
      ReducedK0 Γ := by
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  exact (operatorK0UnitalEquiv (ReducedGroupCStar Γ)).toAddMonoidHom.comp
    ((operatorK0Map (reducedCrossedScalarProductEquiv (Γ := Γ)).toNonUnitalStarAlgHom).comp
      (scalarKKOperatorK0AddEquiv.{uΓ, uE}).toAddMonoidHom)

/-- The actual odd exponential-index comparison is available in every
module universe and lands in the established stable-unitary reduced K1. -/
def reducedScalarKKToK1Hom :
    OddKK.{0, 0, uΓ, uE}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))) →+
      ReducedK1 Γ := by
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  exact (operatorK1UnitalEquiv (ReducedGroupCStar Γ)).toAddMonoidHom.comp
    ((operatorK1Map (reducedCrossedScalarProductEquiv (Γ := Γ)).toNonUnitalStarAlgHom).comp
      (oddKKOperatorK1AllModuleUniversesAddEquiv.{uΓ, uE}).toAddMonoidHom)

/-- Both degrees use their native comparison, rather than a degree tag on
one even construction. Unit is definitionally PUnit in the scalar APIs. -/
def reducedScalarKKToAnalyticHom (p : Bool) :
    KKParityGroup.{0, 0, uΓ, uE} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))) →+
      analyticGroup Γ p := by
  cases p
  · exact reducedScalarKKToK0Hom Γ
  · exact reducedScalarKKToK1Hom Γ

end BC4lean.Assembly
