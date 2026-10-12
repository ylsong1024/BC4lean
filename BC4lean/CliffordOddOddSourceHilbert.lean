import BC4lean.CliffordOddOddCoordinateCycle
import BC4lean.CliffordCycleIso
import BC4lean.CliffordPairSecondTensorCompatibility
import BC4lean.GradedMatrixMoritaTensorDirectSumCycle
import BC4lean.GradedKasparovTensorCycleTransport

/-! # The genuine completed tensor for the final three-odd coherence

The actual second Clifford pair is distributed over the whole first
Hilbert sum. A coefficient-form unitary then applies the explicit Pauli
Fourier unitary in the positive coordinate and X V X in the negative
coordinate. It intertwines the entire external even coordinate cycle with
the canonical signed-odd by Clifford-odd tensor data.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddOddSource

variable {Γ A B C H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : OddKasparovCycle α β H) (d : OddKasparovCycle β γ F)

abbrev Base := InteriorModuleTensor (E := H) d.representation
abbrev Sum := HilbertModuleSum C (Base (H := H) d) (Base (H := H) d)
abbrev Target := CliffordPairModule C (Sum (H := H) d)
abbrev Source := InteriorModuleTensor (E := HilbertModuleSum B H H) d.cliffordExpansion.representation

local instance sourceSumComplete : CompleteSpace (HilbertModuleSum B H H) := hilbertModuleSum_complete
local instance targetSumComplete : CompleteSpace (Sum (H := H) d) := hilbertModuleSum_complete

def distribution : HilbertModuleEquiv C (InteriorModuleTensor (E := HilbertModuleSum B H H) d.representation) (Sum (H := H) d) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv (E := H) (G := H) d.representation

def pairDistribution : HilbertModuleEquiv (C × C) (Source (H := H) d) (Target (H := H) d) :=
  (CliffordPairSecondTensor.hilbertEquiv (E := HilbertModuleSum B H H) d.representation).trans (distribution (H := H) d).cliffordPair

def wholeEquiv : HilbertModuleEquiv (C × C) (Target (H := H) d) (Source (H := H) d) :=
  (CliffordOddOddFourier.pairEquiv (C := C) (M := Base (H := H) d)).trans (pairDistribution (H := H) d).symm

@[simp] theorem wholeEquiv_apply (z : Target (H := H) d) :
    wholeEquiv (H := H) d z = (pairDistribution (H := H) d).symm (CliffordOddOddFourier.pairEquiv (C := C) (M := Base (H := H) d) z) := rfl
@[simp] theorem wholeEquiv_symm_apply (z : Source (H := H) d) :
    (wholeEquiv (H := H) d).symm z = (CliffordOddOddFourier.pairEquiv (C := C) (M := Base (H := H) d)).symm (pairDistribution (H := H) d z) := rfl

@[simp] theorem pairDistribution_mk (x : HilbertModuleSum B H H) (y : CliffordPairModule C F) :
    pairDistribution (H := H) d (interiorModuleTensorMk d.cliffordExpansion.representation x y) =
      cliffordPairMk (B := C) (sumMk (B := C) (interiorModuleTensorMk d.representation x.fst y.1)
        (interiorModuleTensorMk d.representation x.snd y.1))
        (sumMk (B := C) (interiorModuleTensorMk d.representation x.fst y.2)
          (interiorModuleTensorMk d.representation x.snd y.2)) := by
  change (distribution (H := H) d).cliffordPair
      (CliffordPairSecondTensor.hilbertEquiv (E := HilbertModuleSum B H H)
        d.representation (interiorModuleTensorMk
          (CliffordPairSecondTensor.representation d.representation) x y)) = _
  rw [CliffordPairSecondTensor.hilbertEquiv_mk
    (E := HilbertModuleSum B H H) d.representation x y]
  change cliffordPairMk (B := C)
      (GradedMatrixMoritaTensorDirectSum.hilbertEquiv (E := H) (G := H)
        d.representation (interiorModuleTensorMk d.representation x y.1))
      (GradedMatrixMoritaTensorDirectSum.hilbertEquiv (E := H) (G := H)
        d.representation (interiorModuleTensorMk d.representation x y.2)) = _
  apply Prod.ext
  · exact GradedMatrixMoritaTensorDirectSum.hilbertEquiv_mk d.representation x y.1
  · exact GradedMatrixMoritaTensorDirectSum.hilbertEquiv_mk d.representation x y.2

theorem pairDistribution_grading (z : Source (H := H) d) :
    pairDistribution (H := H) d ((gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c) d.cliffordExpansion).grading z) =
      (cliffordExternalEvenGrading (CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d))).grading (pairDistribution (H := H) d z) := by
  let W := (pairDistribution (H := H) d).toAdjointable.toCLM
  let J := (gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c) d.cliffordExpansion).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (cliffordExternalEvenGrading (CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d))).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp J = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change pairDistribution (H := H) d
        ((gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c)
          d.cliffordExpansion).grading
            (interiorModuleTensorMk d.cliffordExpansion.representation x y)) =
      (cliffordExternalEvenGrading
        (CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d))).grading
          (pairDistribution (H := H) d
            (interiorModuleTensorMk d.cliffordExpansion.representation x y))
    have hφ : ModuleTensorRepresentationGraded
        (δB := (CStarGrading.trivial : CStarGrading B))
        d.cliffordExpansion.representation d.cliffordExpansion.grading := by
      intro b v
      exact d.cliffordExpansion.representation_graded b v
    have hfirst (v : HilbertModuleSum B H H) :
        (CliffordOddSourceCycle.cycle c).grading.grading v = sumSwap v := rfl
    have hsecond (v : CliffordPairModule C F) :
        d.cliffordExpansion.grading.grading v = cliffordPairMk (B := C) v.2 v.1 := rfl
    have htarget (v : Target (H := H) d) :
        (cliffordExternalEvenGrading
          (CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d))).grading v =
          cliffordPairMk (B := C) (sumSwap v.2) (sumSwap v.1) := rfl
    change pairDistribution (H := H) d
        (((CliffordOddSourceCycle.cycle c).grading.interiorTensor
          (φ := d.cliffordExpansion.representation) d.cliffordExpansion.grading hφ).grading
            (interiorModuleTensorMk d.cliffordExpansion.representation x y)) = _
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := d.cliffordExpansion.representation)
      (CliffordOddSourceCycle.cycle c).grading d.cliffordExpansion.grading hφ x y,
      hfirst, hsecond, pairDistribution_mk, pairDistribution_mk, htarget]
    simp only [cliffordPairMk, sumSwap_apply, sumMk_fst, sumMk_snd]
    rfl
  exact DFunLike.congr_fun h z

theorem pairDistribution_representation (a : A × A) (z : Source (H := H) d) :
    pairDistribution (H := H) d (gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d.cliffordExpansion a z) =
      cliffordPairMap
        (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1) (CliffordOddOddCoordinate.baseRepresentation c d a.2))
        (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1) (CliffordOddOddCoordinate.baseRepresentation c d a.2))
        (pairDistribution (H := H) d z) := by
  let W := (pairDistribution (H := H) d).toAdjointable.toCLM
  have h : W.comp (gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d.cliffordExpansion a).toCLM =
      (cliffordPairMap
        (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1) (CliffordOddOddCoordinate.baseRepresentation c d a.2))
        (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1) (CliffordOddOddCoordinate.baseRepresentation c d a.2))).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change pairDistribution (H := H) d
        (gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c)
          d.cliffordExpansion a
            (interiorModuleTensorMk d.cliffordExpansion.representation x y)) =
      cliffordPairMap
        (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1)
          (CliffordOddOddCoordinate.baseRepresentation c d a.2))
        (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1)
          (CliffordOddOddCoordinate.baseRepresentation c d a.2))
        (pairDistribution (H := H) d
          (interiorModuleTensorMk d.cliffordExpansion.representation x y))
    have hsource (v : HilbertModuleSum B H H) :
        (CliffordOddSourceCycle.cycle c).representation a v =
          sumMk (B := B) (c.representation a.1 v.fst) (c.representation a.2 v.snd) :=
      sumMap_apply (c.representation a.1) (c.representation a.2) v
    have hbase (b : A) : CliffordOddOddCoordinate.baseRepresentation c d b =
        interiorModuleTensorOperator d.representation (c.representation b) := rfl
    have hsumMap
        (S T : AdjointableMap C (Base (H := H) d) (Base (H := H) d))
        (v : Sum (H := H) d) :
        (sumMap S T).toCLM v =
          sumMk (B := C) (S.toCLM v.fst) (T.toCLM v.snd) := by
      change sumMap S T v = sumMk (B := C) (S v.fst) (T v.snd)
      exact sumMap_apply S T v
    rw [gradedKasparovTensorRepresentation_apply, interiorModuleTensorOperator_mk,
      hsource, pairDistribution_mk, pairDistribution_mk]
    simp only [hbase]
    dsimp only [cliffordPairMap]
    erw [ContinuousLinearMap.coe_prodMap']
    dsimp only [Prod.map, cliffordPairMk]
    erw [hsumMap, hsumMap]
    simp only [sumMk_fst, sumMk_snd]
    apply Prod.ext
    · apply Prod.ext
      · change interiorModuleTensorMk d.representation (c.representation a.1 x.fst) y.1 =
          interiorModuleTensorOperator d.representation (c.representation a.1)
            (interiorModuleTensorMk d.representation x.fst y.1)
        exact (interiorModuleTensorOperator_mk d.representation
          (c.representation a.1) x.fst y.1).symm
      · change interiorModuleTensorMk d.representation (c.representation a.2 x.snd) y.1 =
          interiorModuleTensorOperator d.representation (c.representation a.2)
            (interiorModuleTensorMk d.representation x.snd y.1)
        exact (interiorModuleTensorOperator_mk d.representation
          (c.representation a.2) x.snd y.1).symm
    · apply Prod.ext
      · change interiorModuleTensorMk d.representation (c.representation a.1 x.fst) y.2 =
          interiorModuleTensorOperator d.representation (c.representation a.1)
            (interiorModuleTensorMk d.representation x.fst y.2)
        exact (interiorModuleTensorOperator_mk d.representation
          (c.representation a.1) x.fst y.2).symm
      · change interiorModuleTensorMk d.representation (c.representation a.2 x.snd) y.2 =
          interiorModuleTensorOperator d.representation (c.representation a.2)
            (interiorModuleTensorMk d.representation x.snd y.2)
        exact (interiorModuleTensorOperator_mk d.representation
          (c.representation a.2) x.snd y.2).symm
  exact DFunLike.congr_fun h z

theorem pairDistribution_firstOperator (z : Source (H := H) d) :
    pairDistribution (H := H) d (interiorModuleTensorOperator d.cliffordExpansion.representation
      (CliffordOddSourceCycle.cycle c).operator z) =
      cliffordPairMap (CliffordOddSourceCycle.operator (interiorModuleTensorOperator d.representation c.operator))
        (CliffordOddSourceCycle.operator (interiorModuleTensorOperator d.representation c.operator))
        (pairDistribution (H := H) d z) := by
  let W := (pairDistribution (H := H) d).toAdjointable.toCLM
  have h : W.comp (interiorModuleTensorOperator d.cliffordExpansion.representation
      (CliffordOddSourceCycle.cycle c).operator).toCLM =
      (cliffordPairMap (CliffordOddSourceCycle.operator (interiorModuleTensorOperator d.representation c.operator))
        (CliffordOddSourceCycle.operator (interiorModuleTensorOperator d.representation c.operator))).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change pairDistribution (H := H) d
        (interiorModuleTensorOperator d.cliffordExpansion.representation
          (CliffordOddSourceCycle.cycle c).operator
            (interiorModuleTensorMk d.cliffordExpansion.representation x y)) =
      cliffordPairMap
        (CliffordOddSourceCycle.operator
          (interiorModuleTensorOperator d.representation c.operator))
        (CliffordOddSourceCycle.operator
          (interiorModuleTensorOperator d.representation c.operator))
        (pairDistribution (H := H) d
          (interiorModuleTensorMk d.cliffordExpansion.representation x y))
    have hsource (v : HilbertModuleSum B H H) :
        (CliffordOddSourceCycle.cycle c).operator v =
          sumMk (B := B) ((-Complex.I) • c.operator v.snd)
            (Complex.I • c.operator v.fst) :=
      CliffordOddSourceCycle.operator_apply c.operator v
    have hoperatorApply
        (T : AdjointableMap C (Base (H := H) d) (Base (H := H) d))
        (v : Sum (H := H) d) :
        (CliffordOddSourceCycle.operator T).toCLM v =
          sumMk (B := C) ((-Complex.I) • T.toCLM v.snd)
            (Complex.I • T.toCLM v.fst) := by
      change CliffordOddSourceCycle.operator T v =
        sumMk (B := C) ((-Complex.I) • T v.snd) (Complex.I • T v.fst)
      exact CliffordOddSourceCycle.operator_apply T v
    rw [interiorModuleTensorOperator_mk, hsource,
      pairDistribution_mk, pairDistribution_mk]
    dsimp only [cliffordPairMap]
    erw [ContinuousLinearMap.coe_prodMap']
    dsimp only [Prod.map, cliffordPairMk]
    erw [hoperatorApply, hoperatorApply]
    simp only [sumMk_fst, sumMk_snd]
    apply Prod.ext
    · apply Prod.ext
      · change interiorModuleTensorMk d.representation ((-Complex.I) • c.operator x.snd) y.1 =
          (-Complex.I) • interiorModuleTensorOperator d.representation c.operator
            (interiorModuleTensorMk d.representation x.snd y.1)
        rw [interiorModuleTensorOperator_mk, map_smul, LinearMap.smul_apply]
      · change interiorModuleTensorMk d.representation (Complex.I • c.operator x.fst) y.1 =
          Complex.I • interiorModuleTensorOperator d.representation c.operator
            (interiorModuleTensorMk d.representation x.fst y.1)
        rw [interiorModuleTensorOperator_mk, map_smul, LinearMap.smul_apply]
    · apply Prod.ext
      · change interiorModuleTensorMk d.representation ((-Complex.I) • c.operator x.snd) y.2 =
          (-Complex.I) • interiorModuleTensorOperator d.representation c.operator
            (interiorModuleTensorMk d.representation x.snd y.2)
        rw [interiorModuleTensorOperator_mk, map_smul, LinearMap.smul_apply]
      · change interiorModuleTensorMk d.representation (Complex.I • c.operator x.fst) y.2 =
          Complex.I • interiorModuleTensorOperator d.representation c.operator
            (interiorModuleTensorMk d.representation x.fst y.2)
        rw [interiorModuleTensorOperator_mk, map_smul, LinearMap.smul_apply]
  exact DFunLike.congr_fun h z

theorem pairDistribution_action (g : Γ) (z : Source (H := H) d) :
    pairDistribution (H := H) d ((gradedKasparovTensorAction (CliffordOddSourceCycle.cycle c) d.cliffordExpansion).action g z) =
      (cliffordPairAction ((CliffordOddOddCoordinate.baseAction c d).sum
        (CliffordOddOddCoordinate.baseAction c d))).action g (pairDistribution (H := H) d z) := by
  let W := (pairDistribution (H := H) d).toAdjointable.toCLM
  let U := (gradedKasparovTensorAction (CliffordOddSourceCycle.cycle c) d.cliffordExpansion).action g
  let V := (cliffordPairAction ((CliffordOddOddCoordinate.baseAction c d).sum
    (CliffordOddOddCoordinate.baseAction c d))).action g
  have h : W.comp U.toContinuousLinearEquiv.toContinuousLinearMap =
      V.toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change pairDistribution (H := H) d
        ((gradedKasparovTensorAction (CliffordOddSourceCycle.cycle c)
          d.cliffordExpansion).action g
            (interiorModuleTensorMk d.cliffordExpansion.representation x y)) =
      (cliffordPairAction ((CliffordOddOddCoordinate.baseAction c d).sum
        (CliffordOddOddCoordinate.baseAction c d))).action g
          (pairDistribution (H := H) d
            (interiorModuleTensorMk d.cliffordExpansion.representation x y))
    simp only [gradedKasparovTensorAction]
    rw [EquivariantHilbertModule.interiorTensor_action_mk,
      pairDistribution_mk, pairDistribution_mk]
    apply Prod.ext
    · apply Prod.ext
      · change interiorModuleTensorMk d.representation (c.groupAction.action g x.fst)
            (d.groupAction.action g y.1) =
          (CliffordOddOddCoordinate.baseAction c d).action g
            (interiorModuleTensorMk d.representation x.fst y.1)
        exact (EquivariantHilbertModule.interiorTensor_action_mk c.groupAction d.groupAction
          (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
          g x.fst y.1).symm
      · change interiorModuleTensorMk d.representation (c.groupAction.action g x.snd)
            (d.groupAction.action g y.1) =
          (CliffordOddOddCoordinate.baseAction c d).action g
            (interiorModuleTensorMk d.representation x.snd y.1)
        exact (EquivariantHilbertModule.interiorTensor_action_mk c.groupAction d.groupAction
          (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
          g x.snd y.1).symm
    · apply Prod.ext
      · change interiorModuleTensorMk d.representation (c.groupAction.action g x.fst)
            (d.groupAction.action g y.2) =
          (CliffordOddOddCoordinate.baseAction c d).action g
            (interiorModuleTensorMk d.representation x.fst y.2)
        exact (EquivariantHilbertModule.interiorTensor_action_mk c.groupAction d.groupAction
          (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
          g x.fst y.2).symm
      · change interiorModuleTensorMk d.representation (c.groupAction.action g x.snd)
            (d.groupAction.action g y.2) =
          (CliffordOddOddCoordinate.baseAction c d).action g
            (interiorModuleTensorMk d.representation x.snd y.2)
        exact (EquivariantHilbertModule.interiorTensor_action_mk c.groupAction d.groupAction
          (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
          g x.snd y.2).symm
  exact DFunLike.congr_fun h z

variable (R : AdjointableMap C (CliffordOddOddCoordinate.Source (H := H) d) (CliffordOddOddCoordinate.Source (H := H) d))
  (hR : GradedKasparovTensorOperatorConditions c.cliffordExpansion (CliffordOddSourceCycle.cycle d) R)

abbrev externalCycle := CliffordExternalEvenCycle.cycle (CliffordOddOddCoordinate.cycle c d R hR)

theorem whole_grading (z : Target (H := H) d) :
    wholeEquiv (H := H) d ((externalCycle c d R hR).grading.grading z) =
      (gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c) d.cliffordExpansion).grading (wholeEquiv (H := H) d z) := by
  apply (pairDistribution (H := H) d).injective
  rw [pairDistribution_grading c d]
  simp only [wholeEquiv_apply, HilbertModuleEquiv.apply_symm_apply, externalCycle,
    CliffordExternalEvenCycle.cycle, cliffordExternalEvenGrading,
    CliffordOddOddCoordinate.cycle_grading]
  exact CliffordOddOddFourier.pairEquiv_grading z

theorem whole_action (g : Γ) (z : Target (H := H) d) :
    wholeEquiv (H := H) d ((externalCycle c d R hR).groupAction.action g z) =
      (gradedKasparovTensorAction (CliffordOddSourceCycle.cycle c) d.cliffordExpansion).action g (wholeEquiv (H := H) d z) := by
  apply (pairDistribution (H := H) d).injective
  rw [pairDistribution_action c d]
  simp only [wholeEquiv_apply, HilbertModuleEquiv.apply_symm_apply,
    externalCycle, CliffordExternalEvenCycle.cycle,
    CliffordExternalEvenBalancedTensor.pairAction_apply, CliffordOddOddCoordinate.cycle_action]
  exact CliffordOddOddFourier.pairEquiv_action (CliffordOddOddCoordinate.baseAction c d) g z

set_option maxHeartbeats 1200000 in
theorem whole_representation (a : A × A) (z : Target (H := H) d) :
    wholeEquiv (H := H) d ((externalCycle c d R hR).representation a z) =
      gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d.cliffordExpansion a (wholeEquiv (H := H) d z) := by
  apply (pairDistribution (H := H) d).injective
  rw [pairDistribution_representation c d]
  simp only [wholeEquiv_apply, HilbertModuleEquiv.apply_symm_apply]
  change CliffordOddOddFourier.pairEquiv
      ((externalCycle c d R hR).representation a z) =
    cliffordPairMap
      (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1)
        (CliffordOddOddCoordinate.baseRepresentation c d a.2))
      (sumMap (CliffordOddOddCoordinate.baseRepresentation c d a.1)
        (CliffordOddOddCoordinate.baseRepresentation c d a.2))
      (CliffordOddOddFourier.pairEquiv z)
  have hgrade : (CliffordOddOddCoordinate.cycle c d R hR).grading.toAdjointable =
      (CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d)).toAdjointable := by
    ext x
    change (CliffordOddOddCoordinate.cycle c d R hR).grading.grading x = sumSwap x
    exact CliffordOddOddCoordinate.cycle_grading c d R hR x
  have hhalf (b : A × A) :
      CliffordExternalEvenCycle.half (CliffordOddOddCoordinate.cycle c d R hR) b =
        CliffordExternalEvenRepresentation.halfRepresentation
          (CliffordOddOddFourier.diagonalRepresentation
            (CliffordOddOddCoordinate.baseRepresentation c d))
          (CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d))
          (CliffordOddOddFourier.diagonalRepresentation_commutes
            (CliffordOddOddCoordinate.baseRepresentation c d)) b := by
    rw [CliffordExternalEvenCycle.half,
      CliffordExternalEvenRepresentation.halfRepresentation_eq,
      CliffordExternalEvenRepresentation.halfRepresentation_eq]
    simp only [CliffordOddOddCoordinate.cycle_representation, hgrade,
      CliffordOddOddFourier.diagonalRepresentation, sumRepresentation_apply]
  have hrepresentation (b : A × A) : (externalCycle c d R hR).representation b =
      CliffordExternalEvenRepresentation.representation
        (CliffordOddOddFourier.diagonalRepresentation
          (CliffordOddOddCoordinate.baseRepresentation c d))
        (CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d))
        (CliffordOddOddFourier.diagonalRepresentation_commutes
          (CliffordOddOddCoordinate.baseRepresentation c d)) b := by
    change cliffordPairMap
        (CliffordExternalEvenCycle.half (CliffordOddOddCoordinate.cycle c d R hR) b)
        (CliffordExternalEvenCycle.half (CliffordOddOddCoordinate.cycle c d R hR)
          (cliffordCoefficientGrading.automorphism b)) = _
    simp only [hhalf]
    all_goals rfl
  rw [hrepresentation]
  exact CliffordOddOddFourier.pairEquiv_representation
    (C := C) (M := Base (H := H) d)
    (CliffordOddOddCoordinate.baseRepresentation c d) a z

def productOperator : AdjointableMap (C × C) (Source (H := H) d) (Source (H := H) d) :=
  (wholeEquiv (H := H) d).transport (externalCycle c d R hR).operator

theorem productConditions : GradedKasparovTensorOperatorConditions (CliffordOddSourceCycle.cycle c) d.cliffordExpansion
    (productOperator c d R hR) :=
  transportedCycle_tensorConditions (CliffordOddSourceCycle.cycle c) d.cliffordExpansion
    (externalCycle c d R hR) (wholeEquiv (H := H) d)
    (whole_grading c d R hR) (whole_action c d R hR) (whole_representation c d R hR)

def cycleIso : GradedKasparovCycleIso (externalCycle c d R hR)
    (gradedKasparovTensorCycleOfConditions (CliffordOddSourceCycle.cycle c) d.cliffordExpansion
      (productOperator c d R hR) (productConditions c d R hR)) :=
  transportedCycle_tensorIso (CliffordOddSourceCycle.cycle c) d.cliffordExpansion
    (externalCycle c d R hR) (wholeEquiv (H := H) d)
    (whole_grading c d R hR) (whole_action c d R hR) (whole_representation c d R hR)

@[simp] theorem pairDistribution_productOperator :
    (pairDistribution (H := H) d).transport (productOperator c d R hR) =
      cliffordPairMap ((CliffordOddOddFourier.hilbertEquiv (C := C) (M := Base (H := H) d)).transport (CliffordOddOddCoordinate.cycle c d R hR).operator)
        ((CliffordOddOddFourier.oppositeEquiv (C := C) (M := Base (H := H) d)).transport (CliffordOddOddCoordinate.cycle c d R hR).operator) := by
  have hwhole (T : AdjointableMap (C × C) (Target (H := H) d) (Target (H := H) d)) :
      (wholeEquiv (H := H) d).transport T =
        (pairDistribution (H := H) d).symm.transport
          ((CliffordOddOddFourier.pairEquiv (C := C) (M := Base (H := H) d)).transport T) := by
    ext x
    simp only [HilbertModuleEquiv.transport_apply, wholeEquiv_apply,
      wholeEquiv_symm_apply, HilbertModuleEquiv.symm_symm]
  have hpairMap
      (S T : AdjointableMap C (Sum (H := H) d) (Sum (H := H) d))
      (v : Target (H := H) d) :
      (cliffordPairMap S T).toCLM v =
        cliffordPairMk (B := C) (S.toCLM v.1) (T.toCLM v.2) := rfl
  have hpair (T : AdjointableMap C (Sum (H := H) d) (Sum (H := H) d)) :
      (CliffordOddOddFourier.pairEquiv (C := C) (M := Base (H := H) d)).transport
        (cliffordPairMap T T) =
      cliffordPairMap
        ((CliffordOddOddFourier.hilbertEquiv (C := C) (M := Base (H := H) d)).transport T)
        ((CliffordOddOddFourier.oppositeEquiv (C := C) (M := Base (H := H) d)).transport T) := by
    ext x
    simp only [HilbertModuleEquiv.transport_apply, CliffordOddOddFourier.pairEquiv_apply,
      CliffordOddOddFourier.pairEquiv_symm_apply, hpairMap, cliffordPairMk,
      CliffordOddOddFourier.hilbertEquiv_apply, CliffordOddOddFourier.hilbertEquiv_symm_apply]
    rfl
  have hoperator : (externalCycle c d R hR).operator =
      cliffordPairMap (CliffordOddOddCoordinate.cycle c d R hR).operator
        (CliffordOddOddCoordinate.cycle c d R hR).operator := rfl
  rw [productOperator, hwhole, HilbertModuleEquiv.transport_symm_symm, hoperator]
  exact hpair (CliffordOddOddCoordinate.cycle c d R hR).operator

end BC4lean.KKTheory.CliffordOddOddSource
