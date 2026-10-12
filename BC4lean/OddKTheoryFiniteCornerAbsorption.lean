import BC4lean.OddKTheoryStandardPrefixIndex
import BC4lean.OddFredholmScalarCycleRawIndex
import BC4lean.ModuleIsometricEmbeddingComplement

/-! # Finite corner absorption and its actual odd index

The true orthogonal complement of an adjointable isometric finite embedding
is augmented by H_B and absorbed using the proved stabilization theorem.
The finite corner is placed in the actual standard prefix. The original
compact unitary index therefore equals its actual finite matrix index.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B E : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace B] [Fintype ι] [DecidableEq ι]

local instance oddContinuationOddKTheoryFiniteCornerAbsorptionLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryFiniteCornerAbsorptionLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryFiniteCornerAbsorptionLocalInstance03 {κ : Type} [Fintype κ] [DecidableEq κ] : CompleteSpace (FiniteStandardModule B κ) :=
  finiteStandardModule_complete
local instance oddContinuationOddKTheoryFiniteCornerAbsorptionLocalInstance04 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

def oddKTheoryFiniteCornerComplementCG
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B (ProjectionModule (1 - isometricEmbeddingProjection J)) :=
  projectionModule_isCountablyGenerated _ (isometricEmbeddingProjection_isStarProjection J hJ).one_sub hE

def oddKTheoryFiniteCornerAbsorption
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (hE : IsCountablyGeneratedModule B E) :
    HilbertModuleEquiv B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B) :=
  ((((isometricEmbeddingComplementEquiv J hJ).sum
    (HilbertModuleEquiv.refl (B := B) (E := StandardCountableHilbertModule B))).trans
      HilbertModuleEquiv.sumAssocEquiv).trans
        ((oddKTheoryFiniteReindexEquiv (Fintype.equivFin ι)).sum
          (standardModuleStabilization (oddKTheoryFiniteCornerComplementCG J hJ hE)))).trans
            (oddKTheoryStandardPrefixEquiv (Fintype.card ι))

theorem oddKTheoryFiniteCorner_operator_blocks
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id)
    (U : unitary (AdjointableMap B E E))
    (v : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hCorner : (U : AdjointableMap B E E) - 1 =
      (J.comp (unitizedModuleMatrixRepresentation v - 1)).comp J.adjoint) :
    (isometricEmbeddingComplementEquiv J hJ).transport (U : AdjointableMap B E E) =
      sumMap (unitizedModuleMatrixRepresentation v) 1 := by
  have hx (x : E) : (U : AdjointableMap B E E) x =
      x + J ((unitizedModuleMatrixRepresentation v - 1) (J.adjoint x)) := by
    have hh := congrArg (fun T => T x) hCorner
    change (U : AdjointableMap B E E) x - x = _ at hh
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  apply isometricEmbeddingComplementEquiv_transport J hJ
  · intro x
    rw [hx, ← AdjointableMap.comp_apply J.adjoint J, hJ, AdjointableMap.id_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, J.toCLM.map_sub]
    abel
  · ext x
    rw [AdjointableMap.comp_apply, hx]
    have hz : J.adjoint ((1 - isometricEmbeddingProjection J) x) = 0 := by
      change J.adjoint (x - J (J.adjoint x)) = 0
      rw [J.adjoint.toCLM.map_sub, ← AdjointableMap.comp_apply J.adjoint J,
        hJ, AdjointableMap.id_apply, sub_self]
    rw [hz, map_zero, map_zero, add_zero]

theorem oddKTheoryFiniteCornerAbsorption_unitary
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (hE : IsCountablyGeneratedModule B E)
    (U : unitary (AdjointableMap B E E))
    (v : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hCorner : (U : AdjointableMap B E E) - 1 =
      (J.comp (unitizedModuleMatrixRepresentation v - 1)).comp J.adjoint) :
    oddFredholmTransportUnitary (oddKTheoryFiniteCornerAbsorption J hJ hE)
      (oddKTheorySumOperatorUnitary U 1) =
        oddKTheoryStandardPrefixUnitary (Fintype.card ι)
          (oddKTheoryMatrixOperatorUnitary (unitaryReindex (Fintype.equivFin ι) v)) := by
  have hblock := oddKTheoryFiniteCorner_operator_blocks J hJ U v hCorner
  have hassoc : (HilbertModuleEquiv.sumAssocEquiv (B := B)
      (E := FiniteStandardModule B ι)
      (F := ProjectionModule (1 - isometricEmbeddingProjection J))
      (G := StandardCountableHilbertModule B)).transport
      (sumMap (sumMap (unitizedModuleMatrixRepresentation v) 1) 1) =
        sumMap (unitizedModuleMatrixRepresentation v) 1 := by
    ext x
    change sumMk (unitizedModuleMatrixRepresentation v x.fst)
      (sumMk x.snd.fst x.snd.snd) = sumMap (unitizedModuleMatrixRepresentation v) 1 x
    simp only [sumMap_apply, AdjointableMap.one_apply]
    rfl
  have hreindex : (oddKTheoryFiniteReindexEquiv (Fintype.equivFin ι)).transport
      (unitizedModuleMatrixRepresentation v) =
        unitizedModuleMatrixRepresentation (unitaryReindex (Fintype.equivFin ι) v) := by
    ext x
    rw [HilbertModuleEquiv.transport_apply, oddKTheoryFiniteReindexEquiv_matrix,
      HilbertModuleEquiv.apply_symm_apply]
  apply Subtype.ext
  change (oddKTheoryFiniteCornerAbsorption J hJ hE).transport (sumMap (U : AdjointableMap B E E) 1) = _
  unfold oddKTheoryFiniteCornerAbsorption
  rw [oddFredholmTransport_trans, oddFredholmTransport_trans, oddFredholmTransport_trans,
    oddFredholmTransport_sum, hblock, HilbertModuleEquiv.transport_one, hassoc,
    oddFredholmTransport_sum, hreindex, HilbertModuleEquiv.transport_one]
  rfl

theorem oddKTheoryFiniteCornerAbsorption_unitaryIndex
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (hE : IsCountablyGeneratedModule B E)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1))
    (v : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hv : unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (hCorner : (U : AdjointableMap B E E) - 1 =
      (J.comp (unitizedModuleMatrixRepresentation v - 1)).comp J.adjoint) :
    oddFredholmStandardUnitaryIndex
      (oddFredholmTransportUnitary (oddKTheoryFiniteCornerAbsorption J hJ hE)
        (oddKTheorySumOperatorUnitary U 1))
      (oddFredholmTransportUnitary_sub_one_isModuleCompact _ _
        (oddKTheorySumOperatorUnitary_compact U 1 hU (by simpa only [sub_self] using IsModuleCompact.zero))) =
          oddFredholmScalarIdentityUnitaryIndex v hv := by
  rw [oddKTheoryFiniteCornerAbsorption_unitary J hJ hE U v hCorner,
    oddKTheoryStandardPrefixUnitary_matrixIndex]
  · apply Subtype.ext
    exact (K1.of_eq_iff _ _).mpr
      (FiniteUnitary.equivalent_reindex (FiniteUnitary.ofUnitary v)
        (FiniteUnitary.ofUnitary (unitaryReindex (Fintype.equivFin ι) v))
        (Fintype.equivFin ι) rfl).symm
  · change (CStarMatrix.reindexₐ ℂ ℂ (Fintype.equivFin ι))
      (unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ B))) = 1
    rw [hv, map_one]

theorem oddFredholmStabilizedIndex_finiteExponentialCorner
    (hE : IsCountablyGeneratedModule B E) (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * F - 1))
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id)
    (v : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hv : unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (hCorner : (oddFredholmExponential F : AdjointableMap B E E) - 1 =
      (J.comp (unitizedModuleMatrixRepresentation v - 1)).comp J.adjoint) :
    oddFredholmStabilizedIndex hE F hF = oddFredholmScalarIdentityUnitaryIndex v hv := by
  rw [oddFredholmStabilizedIndex_eq_absorption hE F hF (oddKTheoryFiniteCornerAbsorption J hJ hE)]
  unfold oddFredholmAbsorbedIndex oddFredholmStandardIndex
  rw [← oddFredholmTransport_exponential]
  have he : oddFredholmExponential
      (⟨oddFredholmStandardAugmentedOperator F, oddFredholmStandardAugmentedOperator_isSelfAdjoint F⟩) =
        oddKTheorySumOperatorUnitary (oddFredholmExponential F) 1 := by
    apply Subtype.ext
    rw [oddFredholmExponential_sumMap, oddFredholmExponential_one]
    rfl
  rw [he]
  exact oddKTheoryFiniteCornerAbsorption_unitaryIndex J hJ hE _
    (oddFredholmExponential_sub_one_isModuleCompact F hF) v hv hCorner

end BC4lean.KKTheory
