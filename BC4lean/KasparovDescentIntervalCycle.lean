import BC4lean.KasparovDescentIntervalDefects
import BC4lean.KasparovDescentRawCycle
import BC4lean.FullCliffordParityHomotopy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual even and odd interval cycles for reduced descent

The imported interval norm proof uses the concrete ordinary reduced
representation. This construction
allows every actual complete countably generated C(X,B)-module. It does not
replace full homotopy by an operator path on a fixed module.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

variable {Γ A B X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]

variable (β : CStarAlgebraAction Γ B) (M : Type*)
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- The actual tensor grading, with identity grading on the section factor. -/
def intervalModuleGrading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M) :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, ReducedCrossedProduct β))
      (IntervalModule (X := X) β M) :=
  J.interiorTensor
    (GradedHilbertModule.trivial (B := C(X, ReducedCrossedProduct β))
      (E := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))) (fun _ _ => rfl)

omit [T2Space X] in
@[simp] theorem intervalModuleGrading_mk
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (x : M) (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
    (intervalModuleGrading β M J).grading (intervalMk β M x s) =
      intervalMk β M (J.grading x) s :=
  J.interiorTensor_grading_mk
    (GradedHilbertModule.trivial (B := C(X, ReducedCrossedProduct β))
      (E := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))) (fun _ _ => rfl) x s

omit [T2Space X] in
theorem intervalOperatorHom_odd
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    {T : AdjointableMap C(X, B) M M} (hT : J.IsOdd J T) :
    (intervalModuleGrading β M J).IsOdd (intervalModuleGrading β M J)
      (intervalOperatorHom β M T) :=
  hT.interiorModuleTensorOperator
    (GradedHilbertModule.trivial (B := C(X, ReducedCrossedProduct β))
      (E := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))) (fun _ _ => rfl)

omit [T2Space X] in
theorem intervalOperatorHom_even
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    {T : AdjointableMap C(X, B) M M} (hT : J.IsEven J T) :
    (intervalModuleGrading β M J).IsEven (intervalModuleGrading β M J)
      (intervalOperatorHom β M T) :=
  hT.interiorModuleTensorOperator
    (GradedHilbertModule.trivial (B := C(X, ReducedCrossedProduct β))
      (E := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))) (fun _ _ => rfl)

omit [T2Space X] in
theorem intervalGroupOperator_even
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (hU : U.PreservesGrading J) (g : Γ) :
    (intervalModuleGrading β M J).IsEven (intervalModuleGrading β M J)
      (intervalGroupOperator β M U g) := by
  have h := U.interiorTensor_preservesGrading (intervalLeftRegularAction β) J
    (GradedHilbertModule.trivial (B := C(X, ReducedCrossedProduct β))
      (E := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))) hU (fun _ _ => rfl)
    (intervalCoefficientRepresentation_equivariant β) (fun _ _ => rfl)
  intro u
  exact (h g u).symm

variable (α : CStarAlgebraAction Γ A)

private theorem intervalReducedSourceRepresentation_single_even_aux
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (hU : U.PreservesGrading J) (hπJ : ∀ a, J.IsEven J (π a)) (g : Γ) (a : A) :
    (intervalModuleGrading (X := X) β M J).IsEven (intervalModuleGrading (X := X) β M J)
      (intervalReducedSourceRepresentation (X := X) β M α U π hπ
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))) := by
  have hcomp :
      (intervalOperatorHom (X := X) β M (π a)).comp (intervalGroupOperator (X := X) β M U g) =
        intervalOperatorHom (X := X) β M (π a) * intervalGroupOperator (X := X) β M U g := by
    apply AdjointableMap.ext
    intro u
    simp only [AdjointableMap.comp_apply, AdjointableMap.mul_apply]
  simpa only [intervalReducedSourceRepresentation_single, intervalSourceRepresentation,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom, hcomp] using
    (intervalOperatorHom_even (X := X) β M J (hπJ a)).comp
      (intervalGroupOperator_even (X := X) β M U J hU g)

theorem intervalReducedSourceRepresentation_even
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (hU : U.PreservesGrading J) (hπJ : ∀ a, J.IsEven J (π a))
    (z : ReducedCrossedProduct α) :
    (intervalModuleGrading β M J).IsEven (intervalModuleGrading β M J)
      (intervalReducedSourceRepresentation β M α U π hπ z) := by
  have hfinite : ∀ f : AlgebraicCrossedProduct α,
      (intervalModuleGrading β M J).IsEven (intervalModuleGrading β M J)
        (intervalReducedSourceRepresentation β M α U π hπ (algebraicToReducedCrossed α f)) := by
    intro f
    induction f using AlgebraicCrossedProduct.induction_on α with
    | zero => simp only [map_zero]; exact GradedHilbertModule.isEven_zero
    | single g a =>
      exact intervalReducedSourceRepresentation_single_even_aux (X := X)
        β M α U π hπ J hU hπJ g a
    | add f h ihf ihh =>
      have hadd :
          (intervalReducedSourceRepresentation (X := X) β M α U π hπ
              (algebraicToReducedCrossed α f)).add
              (intervalReducedSourceRepresentation (X := X) β M α U π hπ
                (algebraicToReducedCrossed α h)) =
            intervalReducedSourceRepresentation (X := X) β M α U π hπ
                (algebraicToReducedCrossed α f) +
              intervalReducedSourceRepresentation (X := X) β M α U π hπ
                (algebraicToReducedCrossed α h) := by
        apply AdjointableMap.ext
        intro u
        simp only [AdjointableMap.add_apply, AdjointableMap.coe_add_apply]
      simpa only [map_add, hadd] using ihf.add ihh
  exact (algebraicToReducedCrossed_denseRange α).induction_on z
    ((intervalModuleGrading β M J).evenOperatorSubalgebra_isClosed.preimage
      (map_continuous (intervalReducedSourceRepresentation β M α U π hπ))) hfinite

/-- Ordinary interval KK has the actual continuous-sections Unit action. -/
def intervalTargetAction :
    EquivariantHilbertModule
      ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)).continuousSections
        (X := X)) (IntervalModule (X := X) β M) where
  action := 1
  inner_action _ _ _ := rfl

omit [T2Space X] in
@[simp] theorem intervalTargetAction_conjugate (g : Unit)
    (T : AdjointableMap C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) (IntervalModule (X := X) β M)) :
    (intervalTargetAction β M).conjugateOperator g T = T := by ext u; rfl

omit [T2Space X] in
private theorem intervalTargetAction_defect_compact (g : Unit)
    (T S : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M)) :
    IsModuleCompact (((intervalTargetAction (X := X) β M).conjugateOperator g T - T) * S) := by
  have hz : ((intervalTargetAction (X := X) β M).conjugateOperator g T - T) * S = 0 :=
    (congrArg
      (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => (Q - T) * S)
      (intervalTargetAction_conjugate (X := X) β M g T)).trans
        ((congrArg
          (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => Q * S)
          (sub_self T)).trans (zero_mul S))
  exact Eq.mpr
    (congrArg
      (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => IsModuleCompact Q) hz)
    (IsModuleCompact.zero (B := C(X, ReducedCrossedProduct β))
      (E := IntervalModule (X := X) β M) (F := IntervalModule (X := X) β M))

variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

theorem interval_countablyGenerated (hM : IsCountablyGeneratedModule C(X, B) M) :
    IsCountablyGeneratedModule C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) :=
  hM.interiorTensor (continuousSection_isCountablyGenerated standard_module_isCountablyGenerated)
    (intervalCoefficientRepresentation β)

/-- Genuine even cycle over C(X,B crossed_r Gamma), on the actual extended module. -/
def intervalEvenCycle (c : KasparovCycle α (β.continuousSections (X := X)) M) :
    KasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)).continuousSections
        (X := X)) (IntervalModule (X := X) β M) where
  countablyGenerated := interval_countablyGenerated β M c.countablyGenerated
  grading := intervalModuleGrading β M c.grading
  groupAction := intervalTargetAction β M
  grading_preserved := by intro g u; rfl
  representation := intervalReducedSourceRepresentation β M α c.groupAction c.representation
    c.representation_equivariant
  representation_even := intervalReducedSourceRepresentation_even β M α c.groupAction c.representation
    c.representation_equivariant c.grading c.grading_preserved c.representation_even
  representation_equivariant := by intro g z; exact intervalTargetAction_conjugate β M g _
  operator := intervalOperatorHom β M c.operator
  operator_odd := intervalOperatorHom_odd β M c.grading c.operator_odd
  selfadjoint_mod_compact z := (interval_reduced_source_defects β M α c.groupAction c.representation
    c.representation_equivariant c.operator c.selfadjoint_mod_compact c.square_mod_compact
    c.commutator_compact c.equivariance_mod_compact z).1
  square_mod_compact z := (interval_reduced_source_defects β M α c.groupAction c.representation
    c.representation_equivariant c.operator c.selfadjoint_mod_compact c.square_mod_compact
    c.commutator_compact c.equivariance_mod_compact z).2.1
  commutator_compact z := (interval_reduced_source_defects β M α c.groupAction c.representation
    c.representation_equivariant c.operator c.selfadjoint_mod_compact c.square_mod_compact
    c.commutator_compact c.equivariance_mod_compact z).2.2
  equivariance_mod_compact g z :=
    intervalTargetAction_defect_compact (X := X) β M g
      (intervalOperatorHom (X := X) β M c.operator)
      (intervalReducedSourceRepresentation (X := X) β M α c.groupAction c.representation
        c.representation_equivariant z)

/-- The genuine odd picture uses the same actual arbitrary interval extension. -/
def intervalOddCycle (c : OddKasparovCycle α (β.continuousSections (X := X)) M) :
    OddKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)).continuousSections
        (X := X)) (IntervalModule (X := X) β M) where
  countablyGenerated := interval_countablyGenerated β M c.countablyGenerated
  groupAction := intervalTargetAction β M
  representation := intervalReducedSourceRepresentation β M α c.groupAction c.representation
    c.representation_equivariant
  representation_equivariant := by intro g z; exact intervalTargetAction_conjugate β M g _
  operator := intervalOperatorHom β M c.operator
  selfadjoint_mod_compact z := (interval_reduced_source_defects β M α c.groupAction c.representation
    c.representation_equivariant c.operator c.selfadjoint_mod_compact c.square_mod_compact
    c.commutator_compact c.equivariance_mod_compact z).1
  square_mod_compact z := (interval_reduced_source_defects β M α c.groupAction c.representation
    c.representation_equivariant c.operator c.selfadjoint_mod_compact c.square_mod_compact
    c.commutator_compact c.equivariance_mod_compact z).2.1
  commutator_compact z := (interval_reduced_source_defects β M α c.groupAction c.representation
    c.representation_equivariant c.operator c.selfadjoint_mod_compact c.square_mod_compact
    c.commutator_compact c.equivariance_mod_compact z).2.2
  equivariance_mod_compact g z :=
    intervalTargetAction_defect_compact (X := X) β M g
      (intervalOperatorHom (X := X) β M c.operator)
      (intervalReducedSourceRepresentation (X := X) β M α c.groupAction c.representation
        c.representation_equivariant z)

end BC4lean.KKTheory.KasparovDescent
