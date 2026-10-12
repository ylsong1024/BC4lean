import BC4lean.GroupUniverseCoefficientPushforward
import BC4lean.GroupUniverseEvenBridge
import BC4lean.OrdinaryScalarCoefficientTensor

/-! # Actual ordinary even coefficient pushforward across universes

The genuine homomorphism-cycle product is transported through the actual
even full-witness bridge. Its compact-second representative has exactly the
original scalar coefficient tensor's module, full form, representation and
operator. Whole grading equality is proved on dense pure tensors; the
PUnit action equality uses its actual action identity law.
-/

noncomputable section
universe uB uC uE
namespace BC4lean.KKTheory.GroupUniverseOrdinaryEven
variable {B : Type uB} {C : Type uC}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction (PUnit : Type) ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction (PUnit : Type) B)
local notation "γ₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction (PUnit : Type) C)

def coefficientPushforward (f : B →⋆ₙₐ[ℂ] C)
    (x : KasparovHomotopyClass.{0,0,uB,uE} α₁ β₁) :
    KasparovHomotopyClass.{0,0,uC,max uE uC} α₁ γ₁ :=
  GroupUniverseEvenBridge.evenClass (GroupUniverseCoefficientPushforward.coefficientPushforward
    (CStarAlgebraAction.preservesGrading_trivial β₁) (CStarAlgebraAction.preservesGrading_trivial γ₁) f
    (fun _ _ => rfl) (fun _ => rfl) (GroupUniverseEvenBridge.gradedClass x))

set_option maxHeartbeats 2000000 in
theorem coefficientPushforward_add (f : B →⋆ₙₐ[ℂ] C)
    (x y : KasparovHomotopyClass.{0,0,uB,uE} α₁ β₁) :
    coefficientPushforward f (x + y) = coefficientPushforward f x + coefficientPushforward f y := by
  let p : GradedKasparovHomotopyClass.{0,0,uB,uE} α₁ β₁
      CStarGrading.trivial CStarGrading.trivial →
      GradedKasparovHomotopyClass.{0,0,uC,max uE uC} α₁ γ₁
        CStarGrading.trivial CStarGrading.trivial :=
    GroupUniverseCoefficientPushforward.coefficientPushforward
      (CStarAlgebraAction.preservesGrading_trivial β₁)
      (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl)
  have hp := GroupUniverseCoefficientPushforward.coefficientPushforward_add
    (CStarAlgebraAction.preservesGrading_trivial β₁)
    (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl)
    (GroupUniverseEvenBridge.gradedClass x) (GroupUniverseEvenBridge.gradedClass y)
  exact (congrArg GroupUniverseEvenBridge.evenClass
    ((congrArg p (GroupUniverseEvenBridge.gradedClass_add x y)).trans hp)).trans
      (GroupUniverseEvenBridge.evenClass_add _ _)

def coefficientPushforwardHom (f : B →⋆ₙₐ[ℂ] C) :
    KasparovHomotopyClass.{0,0,uB,uE} α₁ β₁ →+
    KasparovHomotopyClass.{0,0,uC,max uE uC} α₁ γ₁ :=
  AddMonoidHom.mk' (coefficientPushforward f) (coefficientPushforward_add f)

set_option maxHeartbeats 2000000 in
def compactSecondTensorIso {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : KasparovCycle α₁ β₁ E) (f : B →⋆ₙₐ[ℂ] C) : GradedKasparovCycleIso
      (gradedKasparovCompactSecondProduct (GradedKasparovCycle.ofKasparovCycle c)
        (gradedStandardModuleHomCycle β₁ γ₁ CStarGrading.trivial CStarGrading.trivial
          (CStarAlgebraAction.preservesGrading_trivial β₁) (CStarAlgebraAction.preservesGrading_trivial γ₁) f
          (fun _ _ => rfl) (fun _ => rfl))
        (gradedStandardModuleHomCycle_representation_compact β₁ γ₁
          CStarGrading.trivial CStarGrading.trivial (CStarAlgebraAction.preservesGrading_trivial β₁)
          (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl)))
      (GradedKasparovCycle.ofKasparovCycle (c.scalarCoefficientTensor f)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine z := by
    let φ := standardCoefficientImageRepresentation f
    have h :
        ((GradedKasparovCycle.ofKasparovCycle c).grading.interiorTensor
          (GradedHilbertModule.standard (CStarGrading.trivial : CStarGrading C))
          (φ := φ) (fun _ _ => rfl)).grading.toContinuousLinearEquiv.toContinuousLinearMap =
        (c.grading.interiorTensor GradedHilbertModule.trivial
          (φ := φ) (fun _ _ => rfl)).grading.toContinuousLinearEquiv.toContinuousLinearMap := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change
        (((GradedKasparovCycle.ofKasparovCycle c).grading.interiorTensor
          (GradedHilbertModule.standard (CStarGrading.trivial : CStarGrading C))
          (φ := φ) (fun _ _ => rfl)).grading (interiorModuleTensorMk φ x y)) =
        (c.grading.interiorTensor GradedHilbertModule.trivial
          (φ := φ) (fun _ _ => rfl)).grading (interiorModuleTensorMk φ x y)
      have hleft := GradedHilbertModule.interiorTensor_grading_mk (φ := φ)
        (GradedKasparovCycle.ofKasparovCycle c).grading
        (GradedHilbertModule.standard (CStarGrading.trivial : CStarGrading C))
        (fun _ _ => rfl) x y
      have hright := GradedHilbertModule.interiorTensor_grading_mk (φ := φ)
        c.grading GradedHilbertModule.trivial (fun _ _ => rfl) x y
      exact hleft.trans hright.symm
    exact DFunLike.congr_fun h z
  action_intertwine g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    let s := gradedKasparovCompactSecondProduct (GradedKasparovCycle.ofKasparovCycle c)
      (gradedStandardModuleHomCycle β₁ γ₁ CStarGrading.trivial CStarGrading.trivial
        (CStarAlgebraAction.preservesGrading_trivial β₁)
        (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl))
      (gradedStandardModuleHomCycle_representation_compact β₁ γ₁
        CStarGrading.trivial CStarGrading.trivial
        (CStarAlgebraAction.preservesGrading_trivial β₁)
        (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl))
    change s.groupAction.action 1 z = z
    exact EquivariantHilbertModule.one_apply s.groupAction z
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

set_option maxHeartbeats 2000000 in
theorem coefficientPushforward_mk_scalarCoefficientTensor {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : KasparovCycle α₁ β₁ E) (f : B →⋆ₙₐ[ℂ] C) :
    coefficientPushforward f (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (c.scalarCoefficientTensor f)) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  let p : GradedKasparovHomotopyClass.{0,0,uB,uE} α₁ β₁
      CStarGrading.trivial CStarGrading.trivial →
      GradedKasparovHomotopyClass.{0,0,uC,max uE uC} α₁ γ₁
        CStarGrading.trivial CStarGrading.trivial :=
    GroupUniverseCoefficientPushforward.coefficientPushforward
      (CStarAlgebraAction.preservesGrading_trivial β₁)
      (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl)
  have hp := GroupUniverseCoefficientPushforward.coefficientPushforward_mk_tensor
    (CStarAlgebraAction.preservesGrading_trivial β₁)
    (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl)
    (GroupUniverseEvenBase.ofEven (BundledKasparovCycle.of c))
  have hi := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of
      (gradedKasparovCompactSecondProduct (GradedKasparovCycle.ofKasparovCycle c)
        (gradedStandardModuleHomCycle β₁ γ₁ CStarGrading.trivial CStarGrading.trivial
          (CStarAlgebraAction.preservesGrading_trivial β₁)
          (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl))
        (gradedStandardModuleHomCycle_representation_compact β₁ γ₁
          CStarGrading.trivial CStarGrading.trivial
          (CStarAlgebraAction.preservesGrading_trivial β₁)
          (CStarAlgebraAction.preservesGrading_trivial γ₁) f (fun _ _ => rfl) (fun _ => rfl))))
    (d := GroupUniverseEvenBase.ofEven (BundledKasparovCycle.of (c.scalarCoefficientTensor f)))
    (compactSecondTensorIso c f)
  exact (GroupUniverseEvenBridge.gradedClass_evenClass _).trans
    ((congrArg p (GroupUniverseEvenBridge.gradedClass_mk (BundledKasparovCycle.of c))).trans
      (hp.trans (hi.trans
        (GroupUniverseEvenBridge.gradedClass_mk
          (BundledKasparovCycle.of (c.scalarCoefficientTensor f))).symm)))

end BC4lean.KKTheory.GroupUniverseOrdinaryEven
