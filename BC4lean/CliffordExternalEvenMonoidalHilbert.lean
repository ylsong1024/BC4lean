import BC4lean.CliffordExternalEvenBalancedCompatibility
import BC4lean.GradedKasparovTensorCycleTransport
import Mathlib.Tactic.Module

/-! # The whole balanced tensor for two actual external even cycles

The first module grading is arbitrary. The same completed coefficient-form
unitary intertwines its Koszul grading, source representation and action
with the genuine external extension of the original interior tensor.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenMonoidal
open CliffordExternalEvenRepresentation CliffordExternalEvenBalancedTensor

variable {Γ A B C H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial H)
  (d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F)

abbrev Source := InteriorModuleTensor (E := CliffordPairModule B H)
  (CliffordExternalEvenCycle.cycle d).representation
abbrev Target := CliffordPairModule C (InteriorModuleTensor (E := H) d.representation)

def hilbertEquiv : HilbertModuleEquiv (C × C) (Source (H := H) d) (Target (H := H) d) :=
  CliffordExternalEvenBalancedTensor.hilbertEquiv (H := H) d.representation d.grading
    (CliffordExternalEvenCycle.representation_commutes_grading d)

@[simp] theorem hilbertEquiv_mk (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    hilbertEquiv (H := H) d (interiorModuleTensorMk (CliffordExternalEvenCycle.cycle d).representation x y) =
      bilinear d.representation d.grading x y :=
  CliffordExternalEvenBalancedTensor.hilbertEquiv_mk _ _ _ x y

theorem bilinear_grading (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    bilinear d.representation d.grading
      ((CliffordExternalEvenCycle.cycle c).grading.grading x)
      ((CliffordExternalEvenCycle.cycle d).grading.grading y) =
    (cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading
      (bilinear d.representation d.grading x y) := by
  change bilinear d.representation d.grading
      (cliffordPairMk (c.grading.grading x.2) (c.grading.grading x.1))
      (cliffordPairMk (d.grading.grading y.2) (d.grading.grading y.1)) =
    cliffordPairMk
      ((gradedKasparovTensorGrading c d).grading (bilinear d.representation d.grading x y).2)
      ((gradedKasparovTensorGrading c d).grading (bilinear d.representation d.grading x y).1)
  have hmk (u : H) (v : F) :
      (gradedKasparovTensorGrading c d).grading (interiorModuleTensorMk d.representation u v) =
        interiorModuleTensorMk d.representation (c.grading.grading u) (d.grading.grading v) :=
    GradedHilbertModule.interiorTensor_grading_mk c.grading d.grading d.representation_graded u v
  apply Prod.ext
  · change interiorModuleTensorMk d.representation (c.grading.grading x.2)
        (plus d.grading (d.grading.grading y.2)) +
      interiorModuleTensorMk d.representation (c.grading.grading x.1)
        (minus d.grading (d.grading.grading y.2)) =
      (gradedKasparovTensorGrading c d).grading
        (interiorModuleTensorMk d.representation x.1 (minus d.grading y.2) +
          interiorModuleTensorMk d.representation x.2 (plus d.grading y.2))
    rw [plus_grading_apply, minus_grading_apply, map_add, hmk, hmk,
      grading_minus_apply, grading_plus_apply]
    simp only [map_neg]
    abel
  · change interiorModuleTensorMk d.representation (c.grading.grading x.2)
        (minus d.grading (d.grading.grading y.1)) +
      interiorModuleTensorMk d.representation (c.grading.grading x.1)
        (plus d.grading (d.grading.grading y.1)) =
      (gradedKasparovTensorGrading c d).grading
        (interiorModuleTensorMk d.representation x.1 (plus d.grading y.1) +
          interiorModuleTensorMk d.representation x.2 (minus d.grading y.1))
    rw [minus_grading_apply, plus_grading_apply, map_add, hmk, hmk,
      grading_plus_apply, grading_minus_apply]
    simp only [map_neg]
    abel

theorem hilbertEquiv_grading (z : Source (H := H) d) :
    hilbertEquiv (H := H) d
      ((gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
        (CliffordExternalEvenCycle.cycle d)).grading z) =
    (cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading
      (hilbertEquiv (H := H) d z) := by
  let W := (hilbertEquiv (H := H) d).toAdjointable.toCLM
  let L := (gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
    (CliffordExternalEvenCycle.cycle d)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp L = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv (H := H) d
      ((gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
        (CliffordExternalEvenCycle.cycle d)).grading
        (interiorModuleTensorMk (CliffordExternalEvenCycle.cycle d).representation x y)) =
      (cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading
        (hilbertEquiv (H := H) d (interiorModuleTensorMk (CliffordExternalEvenCycle.cycle d).representation x y))
    have hφ : ModuleTensorRepresentationGraded (δB := cliffordCoefficientGrading)
        (CliffordExternalEvenCycle.cycle d).representation
        (CliffordExternalEvenCycle.cycle d).grading :=
      (CliffordExternalEvenCycle.cycle d).representation_graded
    change hilbertEquiv (H := H) d
      (((CliffordExternalEvenCycle.cycle c).grading.interiorTensor
        (CliffordExternalEvenCycle.cycle d).grading hφ).grading
        (interiorModuleTensorMk (CliffordExternalEvenCycle.cycle d).representation x y)) = _
    rw [GradedHilbertModule.interiorTensor_grading_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    exact bilinear_grading c d x y
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_action (g : Γ) (z : Source (H := H) d) :
    hilbertEquiv (H := H) d ((gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
        (CliffordExternalEvenCycle.cycle d)).action g z) =
      (cliffordPairAction (gradedKasparovTensorAction c d)).action g (hilbertEquiv (H := H) d z) :=
  CliffordExternalEvenBalancedTensor.hilbertEquiv_action _ _ _ c.groupAction d.groupAction
    d.grading_preserved
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    ((CliffordExternalEvenCycle.cycle d).groupAction.representationEquivariant_of_conjugate
      (CliffordExternalEvenCycle.cycle d).representation_equivariant) g z

variable
  (R : AdjointableMap C (InteriorModuleTensor (E := H) d.representation)
    (InteriorModuleTensor (E := H) d.representation))
  (hR : GradedKasparovTensorOperatorConditions c d R)

def externalTensorCycle := CliffordExternalEvenCycle.cycle (gradedKasparovTensorCycleOfConditions c d R hR)

theorem bilinear_representation (a : A × A) (x : CliffordPairModule B H)
    (y : CliffordPairModule C F) :
    bilinear d.representation d.grading ((CliffordExternalEvenCycle.cycle c).representation a x) y =
      (externalTensorCycle c d R hR).representation a (bilinear d.representation d.grading x y) := by
  let T := gradedKasparovTensorCycleOfConditions c d R hR
  let J := gradedKasparovTensorGrading c d
  have hmk (u : H) (v : F) : J.grading (interiorModuleTensorMk d.representation u v) =
      interiorModuleTensorMk d.representation (c.grading.grading u) (d.grading.grading v) :=
    GradedHilbertModule.interiorTensor_grading_mk c.grading d.grading d.representation_graded u v
  have hρ (b : A) (u : H) (v : F) :
      T.representation b (interiorModuleTensorMk d.representation u v) =
        interiorModuleTensorMk d.representation (c.representation b u) v :=
    by
      change interiorModuleTensorOperator d.representation (c.representation b)
        (interiorModuleTensorMk d.representation u v) = _
      rw [interiorModuleTensorOperator_mk]
  have hPp (u : H) (v : F) : plus J (interiorModuleTensorMk d.representation u (plus d.grading v)) =
      interiorModuleTensorMk d.representation (plus c.grading u) (plus d.grading v) := by
    rw [show plus J (interiorModuleTensorMk d.representation u (plus d.grading v)) =
      (2 : ℂ)⁻¹ • (interiorModuleTensorMk d.representation u (plus d.grading v) +
      J.grading (interiorModuleTensorMk d.representation u (plus d.grading v))) from rfl,
      show plus c.grading u = (2 : ℂ)⁻¹ • (u + c.grading.grading u) from rfl]
    rw [hmk, grading_plus_apply, LinearMap.map_smul₂, LinearMap.map_add₂]
  have hMp (u : H) (v : F) : minus J (interiorModuleTensorMk d.representation u (plus d.grading v)) =
      interiorModuleTensorMk d.representation (minus c.grading u) (plus d.grading v) := by
    rw [show minus J (interiorModuleTensorMk d.representation u (plus d.grading v)) =
      (2 : ℂ)⁻¹ • (interiorModuleTensorMk d.representation u (plus d.grading v) -
      J.grading (interiorModuleTensorMk d.representation u (plus d.grading v))) from by
        simp only [minus, CliffordOne.minusProjection, AdjointableMap.coe_smul_apply,
          AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
          GradedHilbertModule.toAdjointable_apply],
      show minus c.grading u = (2 : ℂ)⁻¹ • (u - c.grading.grading u) from by
        simp only [minus, CliffordOne.minusProjection, AdjointableMap.coe_smul_apply,
          AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
          GradedHilbertModule.toAdjointable_apply]]
    rw [hmk, grading_plus_apply, LinearMap.map_smul₂, LinearMap.map_sub₂]
  have hPm (u : H) (v : F) : plus J (interiorModuleTensorMk d.representation u (minus d.grading v)) =
      interiorModuleTensorMk d.representation (minus c.grading u) (minus d.grading v) := by
    rw [show plus J (interiorModuleTensorMk d.representation u (minus d.grading v)) =
      (2 : ℂ)⁻¹ • (interiorModuleTensorMk d.representation u (minus d.grading v) +
      J.grading (interiorModuleTensorMk d.representation u (minus d.grading v))) from rfl,
      show minus c.grading u = (2 : ℂ)⁻¹ • (u - c.grading.grading u) from by
        simp only [minus, CliffordOne.minusProjection, AdjointableMap.coe_smul_apply,
          AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
          GradedHilbertModule.toAdjointable_apply]]
    rw [hmk, grading_minus_apply, LinearMap.map_smul₂, LinearMap.map_sub₂]
    simp only [map_neg, sub_eq_add_neg]
  have hMm (u : H) (v : F) : minus J (interiorModuleTensorMk d.representation u (minus d.grading v)) =
      interiorModuleTensorMk d.representation (plus c.grading u) (minus d.grading v) := by
    rw [show minus J (interiorModuleTensorMk d.representation u (minus d.grading v)) =
      (2 : ℂ)⁻¹ • (interiorModuleTensorMk d.representation u (minus d.grading v) -
      J.grading (interiorModuleTensorMk d.representation u (minus d.grading v))) from by
        simp only [minus, CliffordOne.minusProjection, AdjointableMap.coe_smul_apply,
          AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
          GradedHilbertModule.toAdjointable_apply],
      show plus c.grading u = (2 : ℂ)⁻¹ • (u + c.grading.grading u) from rfl]
    rw [hmk, grading_minus_apply, LinearMap.map_smul₂, LinearMap.map_add₂]
    simp only [map_neg, sub_neg_eq_add]
  have hc (b : A × A) (u : H) : CliffordExternalEvenCycle.half c b u =
      c.representation b.1 (plus c.grading u) + c.representation b.2 (minus c.grading u) := by
    change halfRepresentation c.representation c.grading
      (CliffordExternalEvenCycle.representation_commutes_grading c) b u = _
    rw [halfRepresentation_eq]
    rfl
  have hT (b : A × A) (u : InteriorModuleTensor (E := H) d.representation) :
      CliffordExternalEvenCycle.half T b u =
        T.representation b.1 (plus J u) + T.representation b.2 (minus J u) := by
    change halfRepresentation T.representation T.grading
      (CliffordExternalEvenCycle.representation_commutes_grading T) b u = _
    rw [halfRepresentation_eq]
    rfl
  apply Prod.ext
  · change interiorModuleTensorMk d.representation (CliffordExternalEvenCycle.half c a x.1)
        (plus d.grading y.1) +
      interiorModuleTensorMk d.representation
        (CliffordExternalEvenCycle.half c (cliffordCoefficientGrading.automorphism a) x.2)
        (minus d.grading y.1) =
      CliffordExternalEvenCycle.half T a
        (interiorModuleTensorMk d.representation x.1 (plus d.grading y.1) +
          interiorModuleTensorMk d.representation x.2 (minus d.grading y.1))
    simp only [hc, hT, cliffordCoefficientGrading_apply, map_add, LinearMap.add_apply,
      hPp, hMp, hPm, hMm, hρ]
    abel
  · change interiorModuleTensorMk d.representation (CliffordExternalEvenCycle.half c a x.1)
        (minus d.grading y.2) +
      interiorModuleTensorMk d.representation
        (CliffordExternalEvenCycle.half c (cliffordCoefficientGrading.automorphism a) x.2)
        (plus d.grading y.2) =
      CliffordExternalEvenCycle.half T (cliffordCoefficientGrading.automorphism a)
        (interiorModuleTensorMk d.representation x.1 (minus d.grading y.2) +
          interiorModuleTensorMk d.representation x.2 (plus d.grading y.2))
    simp only [hc, hT, cliffordCoefficientGrading_apply, map_add, LinearMap.add_apply,
      hPp, hMp, hPm, hMm, hρ]
    abel

theorem hilbertEquiv_representation (a : A × A) (z : Source (H := H) d) :
    hilbertEquiv (H := H) d (gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
      (CliffordExternalEvenCycle.cycle d) a z) =
    (externalTensorCycle c d R hR).representation a (hilbertEquiv (H := H) d z) := by
  let W := (hilbertEquiv (H := H) d).toAdjointable.toCLM
  have h : W.comp (gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
      (CliffordExternalEvenCycle.cycle d) a).toCLM =
      ((externalTensorCycle c d R hR).representation a).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [ContinuousLinearMap.comp_apply, W, HilbertModuleEquiv.toAdjointable_apply,
      gradedKasparovTensorRepresentation_apply, interiorModuleTensorOperator_mk,
      hilbertEquiv_mk]
    exact bilinear_representation c d R hR a x y
  exact DFunLike.congr_fun h z

theorem transport_firstOperator :
    (hilbertEquiv (H := H) d).transport
      (interiorModuleTensorOperator (CliffordExternalEvenCycle.cycle d).representation
        (CliffordExternalEvenCycle.cycle c).operator) =
    cliffordPairMap (interiorModuleTensorOperator d.representation c.operator)
      (interiorModuleTensorOperator d.representation c.operator) :=
  CliffordExternalEvenBalancedTensor.transport_diagonal_operator _ _ _ c.operator

theorem transport_representation (a : A × A) :
    (hilbertEquiv (H := H) d).transport
      (gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
        (CliffordExternalEvenCycle.cycle d) a) = (externalTensorCycle c d R hR).representation a := by
  ext z
  rw [HilbertModuleEquiv.transport_apply, hilbertEquiv_representation,
    HilbertModuleEquiv.apply_symm_apply]

def productOperator : AdjointableMap (C × C) (Source (H := H) d) (Source (H := H) d) :=
  (hilbertEquiv (H := H) d).symm.transport (cliffordPairMap R R)

include hR in
theorem productConditions : GradedKasparovTensorOperatorConditions
    (CliffordExternalEvenCycle.cycle c) (CliffordExternalEvenCycle.cycle d)
    (productOperator d R) :=
  transportedCycle_tensorConditions _ _ (externalTensorCycle c d R hR)
    (hilbertEquiv (H := H) d).symm
    (fun z => by
      let U := hilbertEquiv (H := H) d
      have hinv (y : Target (H := H) d) : U (U.symm y) = y :=
        U.apply_symm_apply y
      have h := hilbertEquiv_grading c d (U.symm z)
      change U (((gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
            (CliffordExternalEvenCycle.cycle d)).grading) (U.symm z)) =
        ((cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading) (U (U.symm z)) at h
      rw [hinv] at h
      apply U.injective
      change U (U.symm (((cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading) z)) =
        U (((gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
            (CliffordExternalEvenCycle.cycle d)).grading) (U.symm z))
      rw [hinv]
      exact h.symm)
    (fun g z => by
      let U := hilbertEquiv (H := H) d
      have hinv (y : Target (H := H) d) : U (U.symm y) = y :=
        U.apply_symm_apply y
      have h := hilbertEquiv_action c d g (U.symm z)
      change U (((gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
            (CliffordExternalEvenCycle.cycle d)).action g) (U.symm z)) =
        ((cliffordPairAction (gradedKasparovTensorAction c d)).action g) (U (U.symm z)) at h
      rw [hinv] at h
      apply U.injective
      change U (U.symm (((cliffordPairAction (gradedKasparovTensorAction c d)).action g) z)) =
        U (((gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
            (CliffordExternalEvenCycle.cycle d)).action g) (U.symm z))
      rw [hinv]
      exact h.symm)
    (fun a z => by
      let U := hilbertEquiv (H := H) d
      have hinv (y : Target (H := H) d) : U (U.symm y) = y :=
        U.apply_symm_apply y
      have h := hilbertEquiv_representation c d R hR a (U.symm z)
      change U ((gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
            (CliffordExternalEvenCycle.cycle d) a) (U.symm z)) =
        ((externalTensorCycle c d R hR).representation a) (U (U.symm z)) at h
      rw [hinv] at h
      apply U.injective
      change U (U.symm (((externalTensorCycle c d R hR).representation a) z)) =
        U ((gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
            (CliffordExternalEvenCycle.cycle d) a) (U.symm z))
      rw [hinv]
      exact h.symm)

def cycleIso : GradedKasparovCycleIso (externalTensorCycle c d R hR)
    (gradedKasparovTensorCycleOfConditions (CliffordExternalEvenCycle.cycle c)
      (CliffordExternalEvenCycle.cycle d) (productOperator d R) (productConditions c d R hR)) where
  moduleEquiv := (hilbertEquiv (H := H) d).symm
  grading_intertwine z := by
    let U := hilbertEquiv (H := H) d
    have hinv (y : Target (H := H) d) : U (U.symm y) = y :=
      U.apply_symm_apply y
    have h := hilbertEquiv_grading c d (U.symm z)
    change U (((gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
          (CliffordExternalEvenCycle.cycle d)).grading) (U.symm z)) =
      ((cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading) (U (U.symm z)) at h
    rw [hinv] at h
    apply U.injective
    change U (U.symm (((cliffordExternalEvenGrading (gradedKasparovTensorGrading c d)).grading) z)) =
      U (((gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
          (CliffordExternalEvenCycle.cycle d)).grading) (U.symm z))
    rw [hinv]
    exact h.symm
  action_intertwine g z := by
    let U := hilbertEquiv (H := H) d
    have hinv (y : Target (H := H) d) : U (U.symm y) = y :=
      U.apply_symm_apply y
    have h := hilbertEquiv_action c d g (U.symm z)
    change U (((gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
          (CliffordExternalEvenCycle.cycle d)).action g) (U.symm z)) =
      ((cliffordPairAction (gradedKasparovTensorAction c d)).action g) (U (U.symm z)) at h
    rw [hinv] at h
    apply U.injective
    change U (U.symm (((cliffordPairAction (gradedKasparovTensorAction c d)).action g) z)) =
      U (((gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
          (CliffordExternalEvenCycle.cycle d)).action g) (U.symm z))
    rw [hinv]
    exact h.symm
  representation_intertwine a z := by
    let U := hilbertEquiv (H := H) d
    have hinv (y : Target (H := H) d) : U (U.symm y) = y :=
      U.apply_symm_apply y
    have h := hilbertEquiv_representation c d R hR a (U.symm z)
    change U ((gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
          (CliffordExternalEvenCycle.cycle d) a) (U.symm z)) =
      ((externalTensorCycle c d R hR).representation a) (U (U.symm z)) at h
    rw [hinv] at h
    apply U.injective
    change U (U.symm (((externalTensorCycle c d R hR).representation a) z)) =
      U ((gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
          (CliffordExternalEvenCycle.cycle d) a) (U.symm z))
    rw [hinv]
    exact h.symm
  operator_intertwine z := by
    dsimp only [externalTensorCycle, CliffordExternalEvenCycle.cycle,
      gradedKasparovTensorCycleOfConditions]
    change (hilbertEquiv (H := H) d).symm (cliffordPairMap R R z) =
      productOperator d R ((hilbertEquiv (H := H) d).symm z)
    simp only [productOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_symm, HilbertModuleEquiv.apply_symm_apply]

end BC4lean.KKTheory.CliffordExternalEvenMonoidal
