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
set_option synthInstance.maxSize 512
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

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace B] [DecidableEq ι] in
theorem oddKTheoryFiniteCornerComplementCG
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B (ProjectionModule (1 - isometricEmbeddingProjection J)) :=
  projectionModule_isCountablyGenerated _ (isometricEmbeddingProjection_isStarProjection J hJ).one_sub hE

def oddKTheoryFiniteCornerAbsorption
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (hE : IsCountablyGeneratedModule B E) :
    HilbertModuleEquiv B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B) :=
  HilbertModuleEquiv.trans (B := B)
    (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
    (F := HilbertModuleSum B (FiniteStandardModule B (Fin (Fintype.card ι)))
      (StandardCountableHilbertModule B))
    (G := StandardCountableHilbertModule B)
    (HilbertModuleEquiv.trans (B := B)
      (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
      (F := HilbertModuleSum B (FiniteStandardModule B ι)
        (HilbertModuleSum B (ProjectionModule (1 - isometricEmbeddingProjection J))
          (StandardCountableHilbertModule B)))
      (G := HilbertModuleSum B (FiniteStandardModule B (Fin (Fintype.card ι)))
        (StandardCountableHilbertModule B))
      (HilbertModuleEquiv.trans (B := B)
        (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
        (F := HilbertModuleSum B
          (HilbertModuleSum B (FiniteStandardModule B ι)
            (ProjectionModule (1 - isometricEmbeddingProjection J)))
          (StandardCountableHilbertModule B))
        (G := HilbertModuleSum B (FiniteStandardModule B ι)
          (HilbertModuleSum B (ProjectionModule (1 - isometricEmbeddingProjection J))
            (StandardCountableHilbertModule B)))
        (HilbertModuleEquiv.sum (B := B) (E := E) (F := StandardCountableHilbertModule B)
          (G := HilbertModuleSum B (FiniteStandardModule B ι)
            (ProjectionModule (1 - isometricEmbeddingProjection J)))
          (H := StandardCountableHilbertModule B)
          (isometricEmbeddingComplementEquiv (B := B) (M := FiniteStandardModule B ι)
            (E := E) J hJ)
          (HilbertModuleEquiv.refl (B := B) (E := StandardCountableHilbertModule B)))
        (HilbertModuleEquiv.sumAssocEquiv (B := B) (E := FiniteStandardModule B ι)
          (F := ProjectionModule (1 - isometricEmbeddingProjection J))
          (G := StandardCountableHilbertModule B)))
      (HilbertModuleEquiv.sum (B := B) (E := FiniteStandardModule B ι)
        (F := HilbertModuleSum B (ProjectionModule (1 - isometricEmbeddingProjection J))
          (StandardCountableHilbertModule B))
        (G := FiniteStandardModule B (Fin (Fintype.card ι)))
        (H := StandardCountableHilbertModule B)
        (oddKTheoryFiniteReindexEquiv (B := B) (ι := ι) (κ := Fin (Fintype.card ι))
          (Fintype.equivFin ι))
        (standardModuleStabilization (B := B)
          (E := ProjectionModule (1 - isometricEmbeddingProjection J))
          (oddKTheoryFiniteCornerComplementCG (B := B) (E := E) (ι := ι) J hJ hE))))
    (oddKTheoryStandardPrefixEquiv (B := B) (Fintype.card ι))

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace B] in
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
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
      AdjointableMap.comp_apply] at hh
    have heq : (U : AdjointableMap B E E) x =
        J (unitizedModuleMatrixRepresentation (v : CStarMatrix ι ι (Unitization ℂ B))
          (J.adjoint x) - J.adjoint x) + x := sub_eq_iff_eq_add.mp hh
    simpa only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply] using
      heq.trans (add_comm (J (unitizedModuleMatrixRepresentation
        (v : CStarMatrix ι ι (Unitization ℂ B)) (J.adjoint x) - J.adjoint x)) x)
  apply isometricEmbeddingComplementEquiv_transport J hJ
  · intro x
    rw [hx, ← AdjointableMap.comp_apply J.adjoint J, hJ, AdjointableMap.id_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, J.toCLM.map_sub]
    abel
  · ext x
    rw [AdjointableMap.comp_apply, hx]
    have hz : J.adjoint ((1 - isometricEmbeddingProjection J) x) = 0 := by
      rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
        isometricEmbeddingProjection_apply]
      rw [J.adjoint.toCLM.map_sub, ← AdjointableMap.comp_apply J.adjoint J,
        hJ, AdjointableMap.id_apply, sub_self]
    rw [hz, map_zero, map_zero, add_zero]

omit [TopologicalSpace.SeparableSpace B] in
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
  have hblock := oddKTheoryFiniteCorner_operator_blocks (B := B) (E := E) (ι := ι)
    J hJ U v hCorner
  have hassoc : (HilbertModuleEquiv.sumAssocEquiv (B := B)
      (E := FiniteStandardModule B ι)
      (F := ProjectionModule (1 - isometricEmbeddingProjection J))
      (G := StandardCountableHilbertModule B)).transport
      (sumMap (B := B)
        (E := HilbertModuleSum B (FiniteStandardModule B ι)
          (ProjectionModule (1 - isometricEmbeddingProjection J)))
        (F := StandardCountableHilbertModule B)
        (G := HilbertModuleSum B (FiniteStandardModule B ι)
          (ProjectionModule (1 - isometricEmbeddingProjection J)))
        (H := StandardCountableHilbertModule B)
        (sumMap (B := B) (E := FiniteStandardModule B ι)
          (F := ProjectionModule (1 - isometricEmbeddingProjection J))
          (G := FiniteStandardModule B ι)
          (H := ProjectionModule (1 - isometricEmbeddingProjection J))
          (unitizedModuleMatrixRepresentation
            (v : CStarMatrix ι ι (Unitization ℂ B)))
          (1 : AdjointableMap B (ProjectionModule (1 - isometricEmbeddingProjection J))
            (ProjectionModule (1 - isometricEmbeddingProjection J))))
        (1 : OddFredholmStandardOperator B)) =
      sumMap (B := B) (E := FiniteStandardModule B ι)
        (F := HilbertModuleSum B (ProjectionModule (1 - isometricEmbeddingProjection J))
          (StandardCountableHilbertModule B))
        (G := FiniteStandardModule B ι)
        (H := HilbertModuleSum B (ProjectionModule (1 - isometricEmbeddingProjection J))
          (StandardCountableHilbertModule B))
        (unitizedModuleMatrixRepresentation (v : CStarMatrix ι ι (Unitization ℂ B)))
        (1 : AdjointableMap B
          (HilbertModuleSum B (ProjectionModule (1 - isometricEmbeddingProjection J))
            (StandardCountableHilbertModule B))
          (HilbertModuleSum B (ProjectionModule (1 - isometricEmbeddingProjection J))
            (StandardCountableHilbertModule B))) := by
    apply AdjointableMap.ext
    intro x
    have hsymm : (HilbertModuleEquiv.sumAssocEquiv (B := B)
        (E := FiniteStandardModule B ι)
        (F := ProjectionModule (1 - isometricEmbeddingProjection J))
        (G := StandardCountableHilbertModule B)).symm x =
      sumMk (B := B) (sumMk (B := B) x.fst x.snd.fst) x.snd.snd := by
      apply (HilbertModuleEquiv.sumAssocEquiv (B := B)
        (E := FiniteStandardModule B ι)
        (F := ProjectionModule (1 - isometricEmbeddingProjection J))
        (G := StandardCountableHilbertModule B)).injective
      simp only [HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.sumAssocEquiv_apply,
        sumMk_fst, sumMk_snd, sumMk_eta]
    rw [HilbertModuleEquiv.transport_apply, hsymm]
    simp only [HilbertModuleEquiv.sumAssocEquiv_apply, sumMap_apply,
      AdjointableMap.one_apply, sumMk_fst, sumMk_snd, sumMk_eta]
  have hreindex : (oddKTheoryFiniteReindexEquiv (B := B) (ι := ι)
      (κ := Fin (Fintype.card ι)) (Fintype.equivFin ι)).transport
      (unitizedModuleMatrixRepresentation (v : CStarMatrix ι ι (Unitization ℂ B))) =
        unitizedModuleMatrixRepresentation
          (unitaryReindex (Fintype.equivFin ι) v :
            CStarMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Unitization ℂ B)) := by
    apply AdjointableMap.ext
    intro x
    rw [HilbertModuleEquiv.transport_apply, oddKTheoryFiniteReindexEquiv_matrix,
      HilbertModuleEquiv.apply_symm_apply]
    rfl
  apply Subtype.ext
  change (oddKTheoryFiniteCornerAbsorption (B := B) (E := E) (ι := ι) J hJ hE).transport
    (sumMap (B := B) (E := E) (F := StandardCountableHilbertModule B)
      (G := E) (H := StandardCountableHilbertModule B)
      (U : AdjointableMap B E E) (1 : OddFredholmStandardOperator B)) = _
  unfold oddKTheoryFiniteCornerAbsorption
  rw [oddFredholmTransport_trans, oddFredholmTransport_trans, oddFredholmTransport_trans,
    oddFredholmTransport_sum, hblock, HilbertModuleEquiv.transport_one, hassoc,
    oddFredholmTransport_sum, hreindex, HilbertModuleEquiv.transport_one]
  rfl

omit [TopologicalSpace.SeparableSpace B] in
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
      (oddFredholmTransportUnitary_sub_one_isModuleCompact
        (B := B) (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
        (oddKTheoryFiniteCornerAbsorption (B := B) (E := E) (ι := ι) J hJ hE)
        (oddKTheorySumOperatorUnitary U (1 : unitary (OddFredholmStandardOperator B)))
        (oddKTheorySumOperatorUnitary_compact U (1 : unitary (OddFredholmStandardOperator B)) hU
          (by
            change IsModuleCompact ((1 : OddFredholmStandardOperator B) - 1)
            simpa only [sub_self] using
              (IsModuleCompact.zero (B := B) (E := StandardCountableHilbertModule B)
                (F := StandardCountableHilbertModule B))))) =
          oddFredholmScalarIdentityUnitaryIndex v hv := by
  let vr : unitary (CStarMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι))
      (Unitization ℂ B)) := unitaryReindex (Fintype.equivFin ι) v
  have hvr : unitizationScalarMatrix (vr : CStarMatrix (Fin (Fintype.card ι))
      (Fin (Fintype.card ι)) (Unitization ℂ B)) = 1 := by
    change (CStarMatrix.reindexₐ ℂ ℂ (Fintype.equivFin ι))
      (unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ B))) = 1
    rw [hv, map_one]
  have hunitary := oddKTheoryFiniteCornerAbsorption_unitary (B := B) (E := E) (ι := ι)
    J hJ hE U v hCorner
  have hprefixIndex := oddKTheoryStandardPrefixUnitary_matrixIndex (B := B)
    (Fintype.card ι) vr hvr
  have htransportIndex : oddFredholmStandardUnitaryIndex
      (oddFredholmTransportUnitary
        (oddKTheoryFiniteCornerAbsorption (B := B) (E := E) (ι := ι) J hJ hE)
        (oddKTheorySumOperatorUnitary U (1 : unitary (OddFredholmStandardOperator B))))
      (oddFredholmTransportUnitary_sub_one_isModuleCompact
        (B := B) (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
        (oddKTheoryFiniteCornerAbsorption (B := B) (E := E) (ι := ι) J hJ hE)
        (oddKTheorySumOperatorUnitary U (1 : unitary (OddFredholmStandardOperator B)))
        (oddKTheorySumOperatorUnitary_compact U (1 : unitary (OddFredholmStandardOperator B)) hU
          (by
            change IsModuleCompact ((1 : OddFredholmStandardOperator B) - 1)
            simpa only [sub_self] using
              (IsModuleCompact.zero (B := B) (E := StandardCountableHilbertModule B)
                (F := StandardCountableHilbertModule B))))) =
      oddFredholmScalarIdentityUnitaryIndex vr hvr := by
    simpa only [hunitary, vr] using hprefixIndex
  refine htransportIndex.trans ?_
  apply Subtype.ext
  exact (K1.of_eq_iff _ _).mpr
    (FiniteUnitary.equivalent_reindex (FiniteUnitary.ofUnitary v)
      (FiniteUnitary.ofUnitary vr) (Fintype.equivFin ι) rfl).symm

set_option maxHeartbeats 4000000 in
omit [TopologicalSpace.SeparableSpace B] in
theorem oddFredholmStabilizedIndex_finiteExponentialCorner
    (hE : IsCountablyGeneratedModule B E) (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1))
    (J : AdjointableMap B (FiniteStandardModule B ι) E)
    (hJ : J.adjoint.comp J = AdjointableMap.id)
    (v : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hv : unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (hCorner : (oddFredholmExponential F : AdjointableMap B E E) - 1 =
      (J.comp (unitizedModuleMatrixRepresentation v - 1)).comp J.adjoint) :
    oddFredholmStabilizedIndex hE F hF = oddFredholmScalarIdentityUnitaryIndex v hv := by
  let u : HilbertModuleEquiv B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B) := oddKTheoryFiniteCornerAbsorption J hJ hE
  let Faug : selfAdjoint (AdjointableMap B
      (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (HilbertModuleSum B E (StandardCountableHilbertModule B))) :=
    ⟨oddFredholmStandardAugmentedOperator F, oddFredholmStandardAugmentedOperator_isSelfAdjoint F⟩
  have hFaug : IsModuleCompact ((Faug : AdjointableMap B
      (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (HilbertModuleSum B E (StandardCountableHilbertModule B))) ^ 2 - 1) := by
    simpa only [Faug, pow_two] using
      oddFredholmStandardAugmentedOperator_square_compact (B := B) (E := E) F hF
  have hAbs : oddFredholmStabilizedIndex hE F hF = oddFredholmAbsorbedIndex u Faug hFaug := by
    simpa only [u, Faug] using
      oddFredholmStabilizedIndex_eq_absorption (B := B) (E := E) hE F hF u
  have he : oddFredholmExponential Faug =
      oddKTheorySumOperatorUnitary (oddFredholmExponential F)
        (1 : unitary (OddFredholmStandardOperator B)) := by
    have hsum := oddFredholmExponential_sumMap (B := B) (E := E)
      (F := StandardCountableHilbertModule B) F (1 : selfAdjoint (OddFredholmStandardOperator B))
    apply Subtype.ext
    dsimp only [Faug, oddFredholmStandardAugmentedOperator]
    simpa only [selfAdjoint.val_one, oddFredholmExponential_one,
      oddKTheorySumOperatorUnitary, OneMemClass.coe_one] using hsum
  have htransport : oddFredholmExponential (oddFredholmTransportSelfAdjoint u Faug) =
      oddFredholmTransportUnitary u
        (oddKTheorySumOperatorUnitary (oddFredholmExponential F)
          (1 : unitary (OddFredholmStandardOperator B))) := by
    rw [← oddFredholmTransport_exponential, he]
  have hindex := oddKTheoryFiniteCornerAbsorption_unitaryIndex (B := B) (E := E) (ι := ι)
    J hJ hE (oddFredholmExponential F)
    (oddFredholmExponential_sub_one_isModuleCompact F hF) v hv hCorner
  exact hAbs.trans (by
    simpa only [oddFredholmAbsorbedIndex, oddFredholmStandardIndex, htransport, u] using hindex)

end BC4lean.KKTheory
