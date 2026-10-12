import BC4lean.OddScalarKasparovIndexIso
import BC4lean.OddIntervalKasparovFibre

/-! # Genuine scalar-support index naturality on arbitrary interval fibres

The actual projection-range fibre unitary intertwines support compression.
The actual unital fibre homomorphism and normalization naturality then
intertwine the supported normalized Fredholm operators. Arbitrary-module
interval invariance gives equality of raw scalar-cycle index values.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

variable {B M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(I, B)ᵐᵒᵖ M]
  [CStarModule C(I, B)ᵐᵒᵖ M] [CompleteSpace M]

variable (c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
  ((CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B).continuousSections (X := I)) M)

def oddScalarSupportFibreEquiv (t : I) :
    HilbertModuleEquiv B (HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t)
      (ProjectionModule (c.fibre t).scalarSupportProjection) :=
  oddFredholmProjectionFibreEquiv c.scalarSupportProjection c.scalarSupportProjection_isStarProjection t

omit [TopologicalSpace.SeparableSpace B] in
theorem oddScalarSupportBlock_fibre (t : I) :
    hilbertModuleFibreOperator (B := B) t c.scalarSupportBlockOperator =
      (c.fibre t).scalarSupportBlockOperator := by
  simp only [OddKasparovCycle.scalarSupportBlockOperator, OddKasparovCycle.scalarSupportProjection,
    OddKasparovCycle.fibre, hilbertModuleFibreOperator_add, hilbertModuleFibreOperator_mul,
    hilbertModuleFibreOperator_sub, hilbertModuleFibreOperator_one]
  rfl

omit [TopologicalSpace.SeparableSpace B] in
set_option maxHeartbeats 2000000 in
theorem oddScalarSupportFibreEquiv_compression_intertwine (t : I)
    (z : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t) :
    oddScalarSupportFibreEquiv c t
      (hilbertModuleFibreOperator (B := B) t c.scalarSupportCompression z) =
      (c.fibre t).scalarSupportCompression (oddScalarSupportFibreEquiv c t z) := by
  let U := oddScalarSupportFibreEquiv c t
  have hmk (x : ProjectionModule c.scalarSupportProjection) :
      ((U (hilbertModuleFibreMk (B := B) t x) :
        ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) =
      hilbertModuleFibreMk (B := B) t (x : M) :=
    oddFredholmProjectionFibreEquiv_mk c.scalarSupportProjection
      c.scalarSupportProjection_isStarProjection t x
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := ProjectionModule c.scalarSupportProjection) t z
  apply Subtype.ext
  calc
    ((U (hilbertModuleFibreOperator (B := B) t c.scalarSupportCompression
        (hilbertModuleFibreMk (B := B) t x)) :
      ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) =
        ((U (hilbertModuleFibreMk (B := B) t (c.scalarSupportCompression x)) :
          ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) :=
      congrArg (fun y : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t =>
        ((U y : ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t))
        (hilbertModuleFibreOperator_mk (B := B) t c.scalarSupportCompression x)
    _ = hilbertModuleFibreMk (B := B) t (c.scalarSupportCompression x : M) := hmk _
    _ = hilbertModuleFibreMk (B := B) t (c.scalarSupportBlockOperator (x : M)) :=
      congrArg (fun y : M => hilbertModuleFibreMk (B := B) t y) (c.scalarSupportCompression_coe x)
    _ = hilbertModuleFibreOperator (B := B) t c.scalarSupportBlockOperator
        (hilbertModuleFibreMk (B := B) t (x : M)) :=
      (hilbertModuleFibreOperator_mk (B := B) t c.scalarSupportBlockOperator (x : M)).symm
    _ = (c.fibre t).scalarSupportBlockOperator (hilbertModuleFibreMk (B := B) t (x : M)) :=
      congrArg (fun S : AdjointableMap B (HilbertModuleFibre B M t)
        (HilbertModuleFibre B M t) => S (hilbertModuleFibreMk (B := B) t (x : M)))
        (oddScalarSupportBlock_fibre c t)
    _ = (c.fibre t).scalarSupportBlockOperator
        ((U (hilbertModuleFibreMk (B := B) t x) :
          ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) :=
      congrArg (fun y : HilbertModuleFibre B M t => (c.fibre t).scalarSupportBlockOperator y)
        (hmk x).symm
    _ = ((c.fibre t).scalarSupportCompression (U (hilbertModuleFibreMk (B := B) t x)) :
        HilbertModuleFibre B M t) :=
      ((c.fibre t).scalarSupportCompression_coe (U (hilbertModuleFibreMk (B := B) t x))).symm

def oddScalarSupportFibreOperatorHom (t : I) :
    AdjointableMap C(I, B) (ProjectionModule c.scalarSupportProjection)
      (ProjectionModule c.scalarSupportProjection) →⋆ₐ[ℂ]
    AdjointableMap B (ProjectionModule (c.fibre t).scalarSupportProjection)
      (ProjectionModule (c.fibre t).scalarSupportProjection) :=
  (oddScalarSupportFibreEquiv c t).transportStarAlgEquiv.toStarAlgHom.comp
    (hilbertModuleFibreOperatorHom (B := B) t)

omit [TopologicalSpace.SeparableSpace B] in
set_option maxHeartbeats 2000000 in
theorem oddScalarSupportFibreOperatorHom_compression (t : I) :
    oddScalarSupportFibreOperatorHom c t c.scalarSupportCompression =
      (c.fibre t).scalarSupportCompression := by
  let U := oddScalarSupportFibreEquiv c t
  have hhom : oddScalarSupportFibreOperatorHom c t c.scalarSupportCompression =
      U.transport (hilbertModuleFibreOperator (B := B) t c.scalarSupportCompression) := rfl
  refine hhom.trans ?_
  apply AdjointableMap.ext
  intro x
  exact (HilbertModuleEquiv.transport_apply U
    (hilbertModuleFibreOperator (B := B) t c.scalarSupportCompression) x).trans
    ((oddScalarSupportFibreEquiv_compression_intertwine c t (U.symm x)).trans
      (congrArg (fun y : ProjectionModule (c.fibre t).scalarSupportProjection =>
        (c.fibre t).scalarSupportCompression y) (U.apply_symm_apply x)))

omit [TopologicalSpace.SeparableSpace B] in
theorem oddScalarSupportFibreOperatorHom_normalized (t : I) :
    oddScalarSupportFibreOperatorHom c t c.scalarSupportNormalizedCycle.operator =
      (c.fibre t).scalarSupportNormalizedCycle.operator := by
  change oddScalarSupportFibreOperatorHom c t
    (oddFredholmNormalizedElement c.scalarSupportCompression) =
      oddFredholmNormalizedElement (c.fibre t).scalarSupportCompression
  rw [oddFredholmNormalizedElement_map, oddScalarSupportFibreOperatorHom_compression]

def oddScalarSupportIntervalFredholmSelfAdjoint : selfAdjoint
    (AdjointableMap C(I, B) (ProjectionModule c.scalarSupportProjection)
      (ProjectionModule c.scalarSupportProjection)) :=
  ⟨c.scalarSupportNormalizedCycle.operator, c.scalarSupportNormalizedCycle_selfadjoint⟩

omit [TopologicalSpace.SeparableSpace B] in
set_option maxHeartbeats 2000000 in
/-- The raw fibre-cycle index equals the actual stabilized index of the
fibre of the globally supported normalized Fredholm interval operator. -/
theorem oddScalarKasparovOperatorK1Index_fibre (t : I) :
    (c.fibre t).operatorK1Index =
      oddFredholmStabilizedIndex (c.scalarSupportNormalizedCycle.countablyGenerated.fibre t)
        (oddFredholmFibreSelfAdjoint t (oddScalarSupportIntervalFredholmSelfAdjoint c))
        (oddFredholmFibreSelfAdjoint_square_compact t (oddScalarSupportIntervalFredholmSelfAdjoint c)
          c.scalarSupportNormalizedCycle_square_isModuleCompact) := by
  symm
  apply oddFredholmStabilizedIndex_intertwine (oddScalarSupportFibreEquiv c t)
  intro x
  let U := oddScalarSupportFibreEquiv c t
  let S := hilbertModuleFibreOperator (B := B) t c.scalarSupportNormalizedCycle.operator
  have hhom : oddScalarSupportFibreOperatorHom c t c.scalarSupportNormalizedCycle.operator =
      U.transport S := rfl
  have hop : U.transport S = (c.fibre t).scalarSupportNormalizedCycle.operator :=
    hhom.symm.trans (oddScalarSupportFibreOperatorHom_normalized c t)
  have heval : U.transport S (U x) = U (S x) :=
    (HilbertModuleEquiv.transport_apply U S (U x)).trans
      (congrArg (fun y : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t =>
        U (S y)) (U.symm_apply_apply x))
  exact heval.symm.trans
    (congrArg (fun R : AdjointableMap B (ProjectionModule (c.fibre t).scalarSupportProjection)
      (ProjectionModule (c.fibre t).scalarSupportProjection) => R (U x)) hop)

omit [TopologicalSpace.SeparableSpace B] in
/-- Every actual arbitrary scalar odd interval cycle has equal genuine
OperatorK1 index values at its endpoints; degenerate representations are
handled by the actual support range before normalization and stabilization. -/
theorem oddScalarKasparovOperatorK1Index_fibre_endpoints :
    (c.fibre 0).operatorK1Index = (c.fibre 1).operatorK1Index := by
  rw [oddScalarKasparovOperatorK1Index_fibre, oddScalarKasparovOperatorK1Index_fibre]
  exact oddFredholmFullIntervalIndex_endpoints c.scalarSupportNormalizedCycle.countablyGenerated
    (oddScalarSupportIntervalFredholmSelfAdjoint c) c.scalarSupportNormalizedCycle_square_isModuleCompact

end BC4lean.KKTheory
