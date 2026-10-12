import BC4lean.OrdinaryOddCoefficientTensor
import BC4lean.OddFredholmRowTensorPullback
import BC4lean.InteriorModuleTensorFirstFactorEquiv

/-! # Whole ordinary coefficient tensor unitaries for compact row inverses

Actual first-factor unitary transport identifies coefficient extensions of
isomorphic cycles. The genuine tensor-row unitary identifies the extension
of a compact-unitary inverse with the inverse of its actual tensor unitary.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B C E N : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N]
  [CompleteSpace E] [CompleteSpace N]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

def OddKasparovCycleIso.coefficientTensor {c : OddKasparovCycle α₁ β₁ E}
    {d : OddKasparovCycle α₁ β₁ N} (e : OddKasparovCycleIso c d) (f : B →⋆ₙₐ[ℂ] C) :
    OddKasparovCycleIso (c.coefficientTensor f) (d.coefficientTensor f) where
  moduleEquiv := InteriorModuleTensorFirstFactorEquiv.hilbertEquiv
    (standardCoefficientImageRepresentation f) e.moduleEquiv
  action_intertwine g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.one_apply, EquivariantHilbertModule.one_apply]
  representation_intertwine a z :=
    InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_operator _ _
      (c.representation a) (d.representation a) (e.representation_intertwine a) z
  operator_intertwine z :=
    InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_operator _ _
      c.operator d.operator e.operator_intertwine z

omit [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] in
theorem oddFredholmTensorOperatorUnitary_compact (f : B →⋆ₙₐ[ℂ] C)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddFredholmTensorOperatorUnitary
      (standardCoefficientImageRepresentation f) U :
        AdjointableMap C
          (InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation f))
          (InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation f))) - 1) := by
  have h := hU.interiorModuleTensorOperator (standardCoefficientImageRepresentation f)
    (fun b => standardLeftMul_mem_moduleCompact (f b))
  change IsModuleCompact (interiorModuleTensorOperatorHom
    (standardCoefficientImageRepresentation f) ((U : AdjointableMap B E E) - 1)) at h
  simpa only [map_sub, map_one, interiorModuleTensorOperatorHom_apply,
    oddFredholmTensorOperatorUnitary] using h

def oddKTheoryCompactUnitaryCoefficientTensorIso (hE : IsCountablyGeneratedModule B E)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) (f : B →⋆ₙₐ[ℂ] C) :
    OddKasparovCycleIso
      ((oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hE U hU).coefficientTensor f)
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
        (hE.interiorTensor standard_module_isCountablyGenerated (standardCoefficientImageRepresentation f))
        (oddFredholmTensorOperatorUnitary (standardCoefficientImageRepresentation f) U)
        (oddFredholmTensorOperatorUnitary_compact f U hU)) where
  moduleEquiv := countableModuleTensorEquiv (standardCoefficientImageRepresentation f)
  action_intertwine g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.one_apply, EquivariantHilbertModule.one_apply]
  representation_intertwine a z := by
    change countableModuleTensorEquiv (standardCoefficientImageRepresentation f)
      (interiorModuleTensorOperatorHom (standardCoefficientImageRepresentation f)
        (scalarModuleRepresentation a) z) =
      a • countableModuleTensorEquiv (standardCoefficientImageRepresentation f) z
    rw [scalarModuleRepresentation_eq_smul_one, map_smul, map_one]
    change countableModuleTensorEquiv (standardCoefficientImageRepresentation f) (a • z) = _
    exact (countableModuleTensorEquiv (standardCoefficientImageRepresentation f)).map_smul a z
  operator_intertwine z :=
    countableModuleTensorEquiv_pullback (standardCoefficientImageRepresentation f) U z

end BC4lean.KKTheory
