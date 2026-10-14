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

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] in
theorem coordinateHom_action (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (k : Γ) (b : B × B) :
    cliffordCoordinateHom f ((cliffordCoefficientAction β).automorphism k b) =
      (cliffordCoefficientAction γ).automorphism k (cliffordCoordinateHom f b) :=
  Prod.ext (hact k b.1) (hact k b.2)

omit [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] in
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

omit [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] in
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
    GroupUniverseEvenBase.toEven]
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

omit [PartialOrder A] [StarOrderedRing A] in
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
  let hgrade : ∀ a : A, f (CStarGrading.trivial.automorphism a) =
      CStarGrading.trivial.automorphism (f a) := fun _ => rfl
  let e : GradedKasparovHomotopyClass.{uΓ,uB,uB,uB}
      β β CStarGrading.trivial CStarGrading.trivial :=
    GroupUniverseProduct.identity β CStarGrading.trivial β.preservesGrading_trivial
  let h : GradedKasparovHomotopyClass.{uΓ,uA,uB,uB}
      α β CStarGrading.trivial CStarGrading.trivial :=
    GroupUniverseCoefficientPushforward.homClass
      α.preservesGrading_trivial β.preservesGrading_trivial f hact hgrade
  have hhom : h = GradedKasparovHomotopyClass.sourcePullback
      α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade e :=
    GroupUniverseCoefficientPushforward.homClass_sourcePullback_identity.{uΓ,uA,uB}
      α.preservesGrading_trivial β.preservesGrading_trivial f hact hgrade
  have hlift : GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uB,max u (max uA (max uB uC))}
      (GradedKasparovHomotopyClass.sourcePullback
        α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade e) =
      GradedKasparovHomotopyClass.sourcePullback
        α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade
        (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uB,uB,max u (max uA (max uB uC))} e) :=
    GradedKasparovHomotopyClass.ulift_sourcePullback.{uΓ,uB,uB,uB,max u (max uA (max uB uC)),uA}
      α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade e
  have hunit : GroupUniverseProduct.product
      (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uB,uB,max u (max uA (max uB uC))} e) x = x := by
    calc
      _ = GradedKasparovHomotopyClass.ulift.{uΓ,uB,uC,max u (max uA (max uB uC)),max u (max uA (max uB uC))}
          (GroupUniverseProduct.product e x) :=
        (GroupUniverseProduct.product_ulift_first.{uΓ,uB,uB,uC,uB,max u (max uA (max uB uC)),max u (max uA (max uB uC))} e x).symm
      _ = GradedKasparovHomotopyClass.ulift.{uΓ,uB,uC,max u (max uA (max uB uC)),max u (max uA (max uB uC))} x :=
        congrArg (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uC,max u (max uA (max uB uC)),max u (max uA (max uB uC))})
          (GroupUniverseProduct.product_left_identity.{uΓ,uB,uC,max u (max uA (max uB uC))}
            β.preservesGrading_trivial x)
      _ = x := GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uB,uC,0,max u (max uA (max uB uC))} x
  change GroupUniverseProduct.product
    (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uB,max u (max uA (max uB uC))} h) x =
    GradedKasparovHomotopyClass.sourcePullback
      α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade x
  calc
    _ = GroupUniverseProduct.product
        (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uB,max u (max uA (max uB uC))}
          (GradedKasparovHomotopyClass.sourcePullback
            α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade e)) x :=
      congrArg (fun y : GradedKasparovHomotopyClass.{uΓ,uA,uB,uB}
        α β CStarGrading.trivial CStarGrading.trivial =>
          GroupUniverseProduct.product
            (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uB,max u (max uA (max uB uC))} y) x) hhom
    _ = GroupUniverseProduct.product
        (GradedKasparovHomotopyClass.sourcePullback
          α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade
          (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uB,uB,max u (max uA (max uB uC))} e)) x :=
      congrArg (fun y : GradedKasparovHomotopyClass.{uΓ,uA,uB,max u (max uA (max uB uC))}
        α β CStarGrading.trivial CStarGrading.trivial => GroupUniverseProduct.product y x) hlift
    _ = GradedKasparovHomotopyClass.sourcePullback
        α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade
        (GroupUniverseProduct.product
          (GradedKasparovHomotopyClass.ulift.{uΓ,uB,uB,uB,max u (max uA (max uB uC))} e) x) :=
      (GroupUniverseProduct.sourcePullback_product.{uΓ,uB,uA,uB,uC,max u (max uA (max uB uC)),max u (max uA (max uB uC))}
        α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade _ x).symm
    _ = _ := congrArg (GradedKasparovHomotopyClass.sourcePullback
      α CStarGrading.trivial α.preservesGrading_trivial f hact hgrade) hunit

omit [PartialOrder A] [StarOrderedRing A] in
theorem sourcePullback_graded_even (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x : KasparovHomotopyClass.{uΓ,uB,uC,max u (max uA (max uB uC))} β γ) :
    GroupUniverseEvenBridge.gradedClass (sourcePullback.{uΓ,uA,uB,uC,u} false f hact x) =
    GradedKasparovHomotopyClass.sourcePullback α CStarGrading.trivial
      α.preservesGrading_trivial f hact (fun _ => rfl)
      (GroupUniverseEvenBridge.gradedClass x) := by
  change GroupUniverseEvenBridge.gradedClass
    (GroupUniverseParityProduct.evenProduct
      (GroupUniverseParityHomCycle.homClass.{uΓ,uA,uB,max u (max uA (max uB uC))} f hact) x) = _
  rw [GroupUniverseParityProduct.gradedClass_evenProduct,
    GroupUniverseParityHomCycle.gradedClass_homClass.{uΓ,uA,uB,max u (max uA (max uB uC))}]
  exact homClass_leftProduct_eq_sourcePullback.{uΓ,uA,uB,uC,u} f hact _

omit [PartialOrder A] [StarOrderedRing A] in
theorem sourcePullback_graded_odd (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x : OddKK.{uΓ,uB,uC,max u (max uA (max uB uC))} β γ) :
    GroupUniverseCliffordCoordinateBridge.gradedOddClass (sourcePullback.{uΓ,uA,uB,uC,u} true f hact x) =
    GradedKasparovHomotopyClass.sourcePullback α CStarGrading.trivial
      α.preservesGrading_trivial f hact (fun _ => rfl)
      (GroupUniverseCliffordCoordinateBridge.gradedOddClass x) := by
  change GroupUniverseCliffordCoordinateBridge.gradedOddClass
    (GroupUniverseParityProduct.evenOddProduct
      (GroupUniverseParityHomCycle.homClass.{uΓ,uA,uB,max u (max uA (max uB uC))} f hact) x) = _
  rw [GroupUniverseOddFirstParityProduct.coordinateClass_evenOddProduct,
    GroupUniverseParityHomCycle.gradedClass_homClass.{uΓ,uA,uB,max u (max uA (max uB uC))}]
  exact homClass_leftProduct_eq_sourcePullback.{uΓ,uA,uB,uC,u} f hact _

omit [PartialOrder A] [StarOrderedRing A] in
theorem coefficientPushforward_graded_even (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (x : KasparovHomotopyClass.{uΓ,uA,uB,max u (max uA (max uB uC))} α β) :
    GroupUniverseEvenBridge.gradedClass (coefficientPushforward.{uΓ,uA,uB,uC,u} false f hact x) =
    GroupUniverseCoefficientPushforward.coefficientPushforward
      β.preservesGrading_trivial γ.preservesGrading_trivial f hact (fun _ => rfl)
      (GroupUniverseEvenBridge.gradedClass x) := by
  change GroupUniverseEvenBridge.gradedClass
    (GroupUniverseParityProduct.evenProduct x
      (GroupUniverseParityHomCycle.homClass.{uΓ,uB,uC,max u (max uA (max uB uC))} f hact)) = _
  rw [GroupUniverseParityProduct.gradedClass_evenProduct,
    GroupUniverseParityHomCycle.gradedClass_homClass.{uΓ,uB,uC,max u (max uA (max uB uC))},
    ← GroupUniverseProduct.product_ulift_second.{uΓ,uA,uB,uC,max u (max uA (max uB uC)),uC,max u (max uA (max uB uC))}]
  exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uC,0,max u (max uA (max uB uC))} _

omit [PartialOrder A] [StarOrderedRing A] in
theorem coefficientPushforward_graded_odd (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (x : OddKK.{uΓ,uA,uB,max u (max uA (max uB uC))} α β) :
    GroupUniverseCliffordCoordinateBridge.gradedOddClass (coefficientPushforward.{uΓ,uA,uB,uC,u} true f hact x) =
    GroupUniverseCoefficientPushforward.coefficientPushforward
      (cliffordCoefficientAction_preservesGrading β) (cliffordCoefficientAction_preservesGrading γ)
      (cliffordCoordinateHom f) (coordinateHom_action f hact) (fun _ => rfl)
      (GroupUniverseCliffordCoordinateBridge.gradedOddClass x) := by
  change GroupUniverseCliffordCoordinateBridge.gradedOddClass
    (GroupUniverseOddFirstParityProduct.oddEvenProduct x
      (GroupUniverseParityHomCycle.homClass.{uΓ,uB,uC,max u (max uA (max uB uC))} f hact)) = _
  rw [GroupUniverseOddFirstParityProduct.gradedOddClass_oddEvenProduct,
    externalClass_homClass.{uΓ,uB,uC,max u (max uA (max uB uC))},
    ← GroupUniverseProduct.product_ulift_second.{uΓ,uA,uB,uC,max u (max uA (max uB uC)),uC,max u (max uA (max uB uC))}]
  exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uC,0,max u (max uA (max uB uC))} _

end BC4lean.KKTheory.GroupUniverseParityFunctoriality
