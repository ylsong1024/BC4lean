import BC4lean.ReducedGroupCStarTrivial
import BC4lean.ReducedOperatorK0
import BC4lean.ReducedOperatorK1
import BC4lean.OperatorK0Equivalence
import BC4lean.OperatorK1Equivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Analytic targets for a one-element group.
The actual scalar algebra equivalence induces the operator K-group
comparisons. Numerical K-group computations are not asserted here. -/

noncomputable section
open scoped ComplexOrder
universe u
namespace BC4lean.Chapter8Examples
open OperatorKTheory

variable (Γ : Type u) [Group Γ] [Subsingleton Γ]

local instance reducedSpectralOrder : PartialOrder (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrder _
local instance reducedSpectralOrderedRing : StarOrderedRing (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrderedRing _

/-- The actual unital projection K0 target of a one-element group is
canonically the actual projection K0 group of the scalars. -/
def trivialAnalyticK0Equiv : K0 ℂ ≃+ ReducedK0 Γ :=
  k0Equiv (trivialReducedEquiv (Γ := Γ))

/-- The actual stable-unitary K1 target has the same scalar identification. -/
def trivialAnalyticK1Equiv : K1 ℂ ≃+ ReducedK1 Γ :=
  k1Equiv (trivialReducedEquiv (Γ := Γ))

@[simp] theorem trivialAnalyticK0Equiv_apply (x : K0 ℂ) :
    trivialAnalyticK0Equiv Γ x =
      k0Map (trivialReducedEquiv (Γ := Γ)).toStarAlgHom x := rfl

@[simp] theorem trivialAnalyticK1Equiv_apply (x : K1 ℂ) :
    trivialAnalyticK1Equiv Γ x =
      k1Map (trivialReducedEquiv (Γ := Γ)).toStarAlgHom x := rfl

/-- The identification retains the actual entrywise projection-class map. -/
theorem trivialAnalyticK0Equiv_projection (p : FiniteProjection ℂ) :
    trivialAnalyticK0Equiv Γ (k0Projection p) =
      k0Projection (FiniteProjection.map
        (trivialReducedEquiv (Γ := Γ)).toStarAlgHom p) :=
  k0Equiv_projection (trivialReducedEquiv (Γ := Γ)) p

/-- The odd identification retains the actual entrywise unitary-class map. -/
theorem trivialAnalyticK1Equiv_unitary (u : FiniteUnitary ℂ) :
    trivialAnalyticK1Equiv Γ (K1.of u) =
      K1.of (FiniteUnitary.map (trivialReducedEquiv (Γ := Γ)).toStarAlgHom u) :=
  k1Map_of (trivialReducedEquiv (Γ := Γ)).toStarAlgHom u

end BC4lean.Chapter8Examples
