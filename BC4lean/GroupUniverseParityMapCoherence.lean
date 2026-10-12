import BC4lean.GroupUniverseParityFunctoriality

/-! # Actual cycle computation of the full parity algebra maps

The first-algebra homomorphism product is the genuine representation
precomposition, by actual source naturality and the real standard unit.
The external even homomorphism cycle is identified with the coordinate
Clifford homomorphism cycle by the whole standard pair unitary. Thus both
coefficient maps are exactly the independently constructed genuine graded
coefficient products, rather than maps defined through K-theory comparison.
-/

noncomputable section
universe uΓ uA uB uC u v
namespace BC4lean.KKTheory.GroupUniverseParityMapCoherence
variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

theorem coordinateHom_action (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (k : Γ) (b : B × B) :
    cliffordCoordinateHom f ((cliffordCoefficientAction β).automorphism k b) =
      (cliffordCoefficientAction γ).automorphism k (cliffordCoordinateHom f b) :=
  Prod.ext (hact k b.1) (hact k b.2)

theorem half_homCycle (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b)) (b : B × B) :
    CliffordExternalEvenCycle.half
      (gradedStandardModuleHomCycle β γ CStarGrading.trivial CStarGrading.trivial
        β.preservesGrading_trivial γ.preservesGrading_trivial f hact (fun _ => rfl)) b =
    standardLeftMul (f b.1) := by
  let c := gradedStandardModuleHomCycle β γ CStarGrading.trivial CStarGrading.trivial
    β.preservesGrading_trivial γ.preservesGrading_trivial f hact (fun _ => rfl)
  have hJ : c.grading.toAdjointable = (1 : AdjointableMap C Cᵐᵒᵖ Cᵐᵒᵖ) := by ext x; rfl
  have hp : CliffordOne.plusProjection (1 : AdjointableMap C Cᵐᵒᵖ Cᵐᵒᵖ) = 1 := by
    rw [CliffordOne.plusProjection, smul_add, ← add_smul]
    norm_num
  have hm : CliffordOne.minusProjection (1 : AdjointableMap C Cᵐᵒᵖ Cᵐᵒᵖ) = 0 := by
    simp only [CliffordOne.minusProjection, sub_self, smul_zero]
  change CliffordExternalEvenCycle.half c b = _
  rw [CliffordExternalEvenCycle.half, CliffordExternalEvenRepresentation.halfRepresentation_eq,
    hJ, hp, hm, mul_one, mul_zero, add_zero]
  rfl

/-- The genuine full pair coefficient form is preserved by the actual
standard pair unitary; both coordinate actions are the original `f`. -/
def externalEvenHomIso (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b)) :
    GradedKasparovCycleIso
      (CliffordExternalEvenCycle.cycle
        (gradedStandardModuleHomCycle β γ CStarGrading.trivial CStarGrading.trivial
          β.preservesGrading_trivial γ.preservesGrading_trivial f hact (fun _ => rfl)))
      (gradedStandardModuleHomCycle (cliffordCoefficientAction β) (cliffordCoefficientAction γ)
        cliffordCoefficientGrading cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading β) (cliffordCoefficientAction_preservesGrading γ)
        (cliffordCoordinateHom f) (coordinateHom_action f hact) (fun _ => rfl)) where
  moduleEquiv := cliffordPairStandardEquiv.symm
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine b x := by
    change cliffordPairStandardEquiv.symm
      (cliffordPairMap (CliffordExternalEvenCycle.half _ b)
        (CliffordExternalEvenCycle.half _ (cliffordCoefficientGrading.automorphism b)) x) = _
    rw [half_homCycle, half_homCycle]
    rfl
  operator_intertwine _ := rfl

theorem externalClass_homClass (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b)) :
    GroupUniverseExternalEvenClass.externalClass
      (GroupUniverseParityHomCycle.homClass.{uΓ,uB,uC,v} f hact) =
    GradedKasparovHomotopyClass.ulift.{uΓ,uB,uC,uC,v}
      (GroupUniverseCoefficientPushforward.homClass
        (cliffordCoefficientAction_preservesGrading β) (cliffordCoefficientAction_preservesGrading γ)
        (cliffordCoordinateHom f) (coordinateHom_action f hact) (fun _ => rfl)) := by
  unfold GroupUniverseParityHomCycle.homClass
  rw [GroupUniverseParityUnits.externalClass_evenClass_ulift]
  apply congrArg (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uC,uC,v})
  simp only [GroupUniverseCoefficientPushforward.homClass,
    GroupUniverseEvenBridge.evenClass_mk, GroupUniverseExternalEvenClass.externalClass_mk,
    GroupUniverseEvenBase.toEven, GradedKasparovCycle.ofKasparovCycle_toKasparovCycle]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (externalEvenHomIso f hact)

end BC4lean.KKTheory.GroupUniverseParityMapCoherence

namespace BC4lean.KKTheory.GroupUniverseParityFunctoriality
open GroupUniverseParityGroup GroupUniverseParityMapCoherence
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

/-- The actual standard homomorphism product is representation
precomposition, using the genuine source naturality and standard unit. -/
theorem homClass_leftProduct_eq_sourcePullback
    {δC : CStarGrading C} (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x : GradedKasparovHomotopyClass.{uΓ,uB,uC,max u (max uA (max uB uC))}
      β γ CStarGrading.trivial δC) :
    GroupUniverseProduct.product
      (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uB,max u (max uA (max uB uC))}
        (GroupUniverseCoefficientPushforward.homClass
          α.preservesGrading_trivial β.preservesGrading_trivial f hact (fun _ => rfl))) x =
    GradedKasparovHomotopyClass.sourcePullback α CStarGrading.trivial
      α.preservesGrading_trivial f hact (fun _ => rfl) x := by
  rw [GroupUniverseCoefficientPushforward.homClass_sourcePullback_identity,
    GradedKasparovHomotopyClass.ulift_sourcePullback,
    ← GroupUniverseProduct.sourcePullback_product,
    ← GroupUniverseProduct.product_ulift_first, GroupUniverseProduct.product_left_identity,
    ← GradedKasparovHomotopyClass.ulift_sourcePullback]
  exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uC,0,max u (max uA (max uB uC))} _

theorem sourcePullback_graded_even (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x : KasparovHomotopyClass.{uΓ,uB,uC,max u (max uA (max uB uC))} β γ) :
    GroupUniverseEvenBridge.gradedClass (sourcePullback false f hact x) =
    GradedKasparovHomotopyClass.sourcePullback α CStarGrading.trivial
      α.preservesGrading_trivial f hact (fun _ => rfl)
      (GroupUniverseEvenBridge.gradedClass x) := by
  rw [sourcePullback, GroupUniverseParityUnits.leftEvenProduct,
    GroupUniverseParityProduct.gradedClass_evenProduct,
    GroupUniverseParityHomCycle.gradedClass_homClass]
  exact homClass_leftProduct_eq_sourcePullback f hact _

theorem sourcePullback_graded_odd (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x : OddKK.{uΓ,uB,uC,max u (max uA (max uB uC))} β γ) :
    GroupUniverseCliffordCoordinateBridge.gradedOddClass (sourcePullback true f hact x) =
    GradedKasparovHomotopyClass.sourcePullback α CStarGrading.trivial
      α.preservesGrading_trivial f hact (fun _ => rfl)
      (GroupUniverseCliffordCoordinateBridge.gradedOddClass x) := by
  rw [sourcePullback, GroupUniverseParityUnits.leftEvenProduct,
    GroupUniverseOddFirstParityProduct.coordinateClass_evenOddProduct,
    GroupUniverseParityHomCycle.gradedClass_homClass]
  exact homClass_leftProduct_eq_sourcePullback f hact _

theorem coefficientPushforward_graded_even (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (x : KasparovHomotopyClass.{uΓ,uA,uB,max u (max uA (max uB uC))} α β) :
    GroupUniverseEvenBridge.gradedClass (coefficientPushforward false f hact x) =
    GroupUniverseCoefficientPushforward.coefficientPushforward
      β.preservesGrading_trivial γ.preservesGrading_trivial f hact (fun _ => rfl)
      (GroupUniverseEvenBridge.gradedClass x) := by
  rw [coefficientPushforward, GroupUniverseParityUnits.rightEvenProduct,
    GroupUniverseParityProduct.gradedClass_evenProduct, GroupUniverseParityHomCycle.gradedClass_homClass,
    ← GroupUniverseProduct.product_ulift_second, GradedKasparovHomotopyClass.ulift_eq_self]
  rfl

theorem coefficientPushforward_graded_odd (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (x : OddKK.{uΓ,uA,uB,max u (max uA (max uB uC))} α β) :
    GroupUniverseCliffordCoordinateBridge.gradedOddClass (coefficientPushforward true f hact x) =
    GroupUniverseCoefficientPushforward.coefficientPushforward
      (cliffordCoefficientAction_preservesGrading β) (cliffordCoefficientAction_preservesGrading γ)
      (cliffordCoordinateHom f) (coordinateHom_action f hact) (fun _ => rfl)
      (GroupUniverseCliffordCoordinateBridge.gradedOddClass x) := by
  rw [coefficientPushforward, GroupUniverseParityUnits.rightEvenProduct,
    GroupUniverseOddFirstParityProduct.gradedOddClass_oddEvenProduct, externalClass_homClass,
    ← GroupUniverseProduct.product_ulift_second, GradedKasparovHomotopyClass.ulift_eq_self]
  rfl

end BC4lean.KKTheory.GroupUniverseParityFunctoriality
