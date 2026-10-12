import BC4lean.OddScalarKasparovOperatorK1Index
import BC4lean.OddFredholmStabilizedIndexIso
import BC4lean.OddFredholmNormalizationNaturality

/-! # Actual whole-cycle isomorphism invariance of the scalar odd index

The whole-cycle unitary restricts to the true ranges of the two scalar support
projections. Compression, symmetrization and functional calculus intertwine
through this actual restricted unitary. Absorption independence then compares
the resulting finite OperatorK1 values.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B E N : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N]
  [TopologicalSpace.SeparableSpace B]
  {c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B) E}
  {d : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B) N}

def oddScalarSupportIsoEquiv (e : OddKasparovCycleIso c d) :
    HilbertModuleEquiv B (ProjectionModule c.scalarSupportProjection)
      (ProjectionModule d.scalarSupportProjection) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := ⟨e.moduleEquiv (x : E), by
            change d.representation 1 (e.moduleEquiv (x : E)) = e.moduleEquiv (x : E)
            have hx : c.representation 1 (x : E) = (x : E) := x.property
            calc
              d.representation 1 (e.moduleEquiv (x : E)) =
                  e.moduleEquiv (c.representation 1 (x : E)) :=
                (e.representation_intertwine 1 (x : E)).symm
              _ = e.moduleEquiv (x : E) := congrArg e.moduleEquiv hx⟩
          invFun x := ⟨e.moduleEquiv.symm (x : N), by
            change c.representation 1 (e.moduleEquiv.symm (x : N)) = e.moduleEquiv.symm (x : N)
            apply e.moduleEquiv.injective
            rw [e.representation_intertwine, HilbertModuleEquiv.apply_symm_apply]
            exact x.property⟩
          left_inv x := Subtype.ext (e.moduleEquiv.symm_apply_apply (x : E))
          right_inv x := Subtype.ext (e.moduleEquiv.apply_symm_apply (x : N))
          map_add' x y := Subtype.ext (e.moduleEquiv.map_add (x : E) (y : E))
          map_smul' a x := Subtype.ext (e.moduleEquiv.map_smul a (x : E)) }
      norm_map' x := e.moduleEquiv.norm_map (x : E) }
  inner_map x y := e.moduleEquiv.inner_map (x : E) (y : E)

omit [TopologicalSpace.SeparableSpace B] in
theorem oddScalarSupportIso_block (e : OddKasparovCycleIso c d) (x : E) :
    e.moduleEquiv (c.scalarSupportBlockOperator x) =
      d.scalarSupportBlockOperator (e.moduleEquiv x) := by
  simp only [OddKasparovCycle.scalarSupportBlockOperator, AdjointableMap.coe_add_apply,
    AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    e.moduleEquiv.map_add, e.moduleEquiv.map_sub]
  simp only [OddKasparovCycle.scalarSupportProjection, e.representation_intertwine,
    e.operator_intertwine, e.moduleEquiv.map_sub]

omit [TopologicalSpace.SeparableSpace B] in
theorem oddScalarSupportIso_compression (e : OddKasparovCycleIso c d) :
    (oddScalarSupportIsoEquiv e).transport c.scalarSupportCompression = d.scalarSupportCompression := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  change e.moduleEquiv (c.scalarSupportCompression ((oddScalarSupportIsoEquiv e).symm x) : E) =
    (d.scalarSupportCompression x : N)
  rw [c.scalarSupportCompression_coe, d.scalarSupportCompression_coe, oddScalarSupportIso_block]
  change d.scalarSupportBlockOperator (e.moduleEquiv (e.moduleEquiv.symm (x : N))) =
    d.scalarSupportBlockOperator (x : N)
  rw [HilbertModuleEquiv.apply_symm_apply]

omit [TopologicalSpace.SeparableSpace B] in
theorem oddScalarSupportIso_normalized (e : OddKasparovCycleIso c d) :
    (oddScalarSupportIsoEquiv e).transport c.scalarSupportNormalizedCycle.operator =
      d.scalarSupportNormalizedCycle.operator := by
  change (oddScalarSupportIsoEquiv e).transportStarAlgEquiv.toStarAlgHom
    (oddFredholmNormalizedElement c.scalarSupportCompression) =
      oddFredholmNormalizedElement d.scalarSupportCompression
  rw [oddFredholmNormalizedElement_map]
  change oddFredholmNormalizedElement
      ((oddScalarSupportIsoEquiv e).transport c.scalarSupportCompression) =
    oddFredholmNormalizedElement d.scalarSupportCompression
  rw [oddScalarSupportIso_compression]

omit [TopologicalSpace.SeparableSpace B] in
/-- Actual raw scalar-cycle index values respect every actual whole-cycle
isomorphism, including representations with proper scalar support. -/
theorem oddScalarKasparovOperatorK1Index_iso (e : OddKasparovCycleIso c d) :
    c.operatorK1Index = d.operatorK1Index := by
  apply oddFredholmStabilizedIndex_intertwine (oddScalarSupportIsoEquiv e)
  intro x
  have h := congrArg (fun T => T (oddScalarSupportIsoEquiv e x)) (oddScalarSupportIso_normalized e)
  simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply,
    OddKasparovCycle.scalarSupportFredholmSelfAdjoint] using h

end BC4lean.KKTheory
