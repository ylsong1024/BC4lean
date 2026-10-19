import BC4lean.KasparovDescentReducedRepresentation
import BC4lean.KasparovDescentGrading
import BC4lean.KasparovDescentGeneratorDefects
import BC4lean.GradedKasparovNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual raw even and odd reduced descent cycles

The construction uses KasparovDescentReducedRepresentation, built from
the actual finite integration and a proved reduced-norm bound. It uses that
specific concrete endpoint, never an arbitrary
representation supplied as a field or hypothesis.



The target acting group is Unit. The original Gamma group operators occur in
the crossed source representation, not as a target equivariant-cycle action.
This file does not define a map on any homotopy quotient or assert product
compatibility.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

variable (β : CStarAlgebraAction Γ B)

/-- The actual trivial-coefficient specialization of the tensor grading.
Using the identity standard-module grading avoids a transport in its index. -/
def ordinaryModuleGrading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct β))
      (Module β E) :=
  J.interiorTensor
    (GradedHilbertModule.trivial (B := ReducedCrossedProduct β)
      (E := (ReducedCrossedProduct β)ᵐᵒᵖ)) (fun _ _ => rfl)

@[simp] theorem ordinaryModuleGrading_mk
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    (ordinaryModuleGrading β J).grading (mk β E x c) = mk β E (J.grading x) c :=
  J.interiorTensor_grading_mk
    (GradedHilbertModule.trivial (B := ReducedCrossedProduct β)
      (E := (ReducedCrossedProduct β)ᵐᵒᵖ)) (fun _ _ => rfl) x c

theorem operatorHom_ordinary_odd
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    {T : AdjointableMap B E E} (hT : J.IsOdd J T) :
    (ordinaryModuleGrading β J).IsOdd (ordinaryModuleGrading β J) (operatorHom β E T) :=
  hT.interiorModuleTensorOperator
    (GradedHilbertModule.trivial (B := ReducedCrossedProduct β)
      (E := (ReducedCrossedProduct β)ᵐᵒᵖ)) (fun _ _ => rfl)

theorem operatorHom_ordinary_even
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    {T : AdjointableMap B E E} (hT : J.IsEven J T) :
    (ordinaryModuleGrading β J).IsEven (ordinaryModuleGrading β J) (operatorHom β E T) :=
  hT.interiorModuleTensorOperator
    (GradedHilbertModule.trivial (B := ReducedCrossedProduct β)
      (E := (ReducedCrossedProduct β)ᵐᵒᵖ)) (fun _ _ => rfl)

theorem groupAction_preserves_ordinaryGrading (U : EquivariantHilbertModule β E)
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (hU : U.PreservesGrading J) :
    (groupAction β E U).PreservesGrading (ordinaryModuleGrading β J) :=
  U.interiorTensor_preservesGrading (leftRegularAction β) J
    (GradedHilbertModule.trivial (B := ReducedCrossedProduct β)
      (E := (ReducedCrossedProduct β)ᵐᵒᵖ)) hU (fun _ _ => rfl)
    (coefficientRepresentation_equivariant β) (fun _ _ => rfl)

theorem groupOperator_ordinary_even (U : EquivariantHilbertModule β E)
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (hU : U.PreservesGrading J) (g : Γ) :
    (ordinaryModuleGrading β J).IsEven (ordinaryModuleGrading β J) (groupOperator β E U g) := by
  intro x
  exact (groupAction_preserves_ordinaryGrading β U J hU g x).symm

omit [PartialOrder A] [StarOrderedRing A] in
theorem sourceGenerator_ordinary_even (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (hU : U.PreservesGrading J) (hπ : ∀ a, J.IsEven J (π a)) (a : A) (g : Γ) :
    (ordinaryModuleGrading β J).IsEven (ordinaryModuleGrading β J)
      (sourceGenerator β E U π a g) :=
  (operatorHom_ordinary_even β J (hπ a)).comp (groupOperator_ordinary_even β U J hU g)

variable (α : CStarAlgebraAction Γ A)

/-- Source evenness is proved first on the concrete generators and then by
the actual reduced-norm dense range and the existing closed even subalgebra. -/
theorem reducedSourceRepresentation_ordinary_even
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (hU : U.PreservesGrading J) (hπJ : ∀ a, J.IsEven J (π a))
    (z : ReducedCrossedProduct α) :
    (ordinaryModuleGrading β J).IsEven (ordinaryModuleGrading β J)
      (reducedSourceRepresentation β E α U π hπ z) := by
  have hfinite : ∀ f : AlgebraicCrossedProduct α,
      (ordinaryModuleGrading β J).IsEven (ordinaryModuleGrading β J)
        (reducedSourceRepresentation β E α U π hπ (algebraicToReducedCrossed α f)) := by
    intro f
    induction f using AlgebraicCrossedProduct.induction_on α with
    | zero =>
      simp only [map_zero]
      exact GradedHilbertModule.isEven_zero
    | single g a =>
      simpa only [reducedSourceRepresentation_single] using
        sourceGenerator_ordinary_even β U π J hU hπJ a g
    | add f h ihf ihh =>
      have hadd :
          (reducedSourceRepresentation β E α U π hπ (algebraicToReducedCrossed α f)).add
              (reducedSourceRepresentation β E α U π hπ (algebraicToReducedCrossed α h)) =
            reducedSourceRepresentation β E α U π hπ (algebraicToReducedCrossed α f) +
              reducedSourceRepresentation β E α U π hπ (algebraicToReducedCrossed α h) := by
        apply AdjointableMap.ext
        intro x
        simp only [AdjointableMap.add_apply, AdjointableMap.coe_add_apply]
      simpa only [map_add, hadd] using ihf.add ihh
  exact (algebraicToReducedCrossed_denseRange α).induction_on z
    ((ordinaryModuleGrading β J).evenOperatorSubalgebra_isClosed.preimage
      (map_continuous (reducedSourceRepresentation β E α U π hπ))) hfinite

theorem even_reduced_source_defects (c : KasparovCycle α β E) (z : ReducedCrossedProduct α) :
    IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
        reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) ∧
    IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
        reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) ∧
    IsModuleCompact (operatorHom β E c.operator *
        reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z -
      reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z *
        operatorHom β E c.operator) := by
  constructor
  · apply integrated_selfadjoint_compact_of_generators β α _ _ _ z
    intro g a
    simpa only [reducedSourceRepresentation_single] using
      even_sourceGenerator_selfadjoint_compact β E c a g
  constructor
  · apply integrated_square_compact_of_generators β α _ _ _ z
    intro g a
    simpa only [reducedSourceRepresentation_single] using
      even_sourceGenerator_square_compact β E c a g
  · apply integrated_commutator_compact_of_generators β α _ _ _ z
    intro g a
    simpa only [reducedSourceRepresentation_single] using
      even_sourceGenerator_commutator_compact β E c a g

theorem odd_reduced_source_defects (c : OddKasparovCycle α β E) (z : ReducedCrossedProduct α) :
    IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
        reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) ∧
    IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
        reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) ∧
    IsModuleCompact (operatorHom β E c.operator *
        reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z -
      reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z *
        operatorHom β E c.operator) := by
  constructor
  · apply integrated_selfadjoint_compact_of_generators β α _ _ _ z
    intro g a
    simpa only [reducedSourceRepresentation_single] using
      odd_sourceGenerator_selfadjoint_compact β E c a g
  constructor
  · apply integrated_square_compact_of_generators β α _ _ _ z
    intro g a
    simpa only [reducedSourceRepresentation_single] using
      odd_sourceGenerator_square_compact β E c a g
  · apply integrated_commutator_compact_of_generators β α _ _ _ z
    intro g a
    simpa only [reducedSourceRepresentation_single] using
      odd_sourceGenerator_commutator_compact β E c a g


/-- Ordinary KK uses the actual trivial Unit action on the descended module. -/
def ordinaryTargetAction :
    EquivariantHilbertModule
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (Module β E) := EquivariantHilbertModule.trivial

@[simp] theorem ordinaryTargetAction_conjugate (g : Unit)
    (T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E)) :
    (ordinaryTargetAction (E := E) β).conjugateOperator g T = T := by
  ext x
  rfl

private theorem ordinaryTargetAction_defect_compact (g : Unit)
    (T S : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E)) :
    IsModuleCompact (((ordinaryTargetAction (E := E) β).conjugateOperator g T - T) * S) := by
  have hz : ((ordinaryTargetAction (E := E) β).conjugateOperator g T - T) * S = 0 :=
    (congrArg
      (fun Q : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
        (Q - T) * S)
      (ordinaryTargetAction_conjugate (E := E) β g T)).trans
        ((congrArg
          (fun Q : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
            Q * S)
          (sub_self T)).trans (zero_mul S))
  exact Eq.mpr
    (congrArg
      (fun Q : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
        IsModuleCompact Q) hz)
    (IsModuleCompact.zero
      (B := ReducedCrossedProduct β) (E := Module β E) (F := Module β E))

variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- The raw even cycle from the concrete completed source representation.
-/
def evenCycle (c : KasparovCycle α β E) :
    KasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (Module β E) where
  countablyGenerated := KasparovDescent.countablyGenerated β E c.countablyGenerated
  grading := ordinaryModuleGrading β c.grading
  groupAction := ordinaryTargetAction (E := E) β
  grading_preserved := by intro g x; rfl
  representation := reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant
  representation_even := reducedSourceRepresentation_ordinary_even β α
    c.groupAction c.representation c.representation_equivariant
    c.grading c.grading_preserved c.representation_even
  representation_equivariant := by
    intro g z
    exact ordinaryTargetAction_conjugate (E := E) β g _
  operator := operatorHom β E c.operator
  operator_odd := operatorHom_ordinary_odd β c.grading c.operator_odd
  selfadjoint_mod_compact z := (even_reduced_source_defects β α c z).1
  square_mod_compact z := (even_reduced_source_defects β α c z).2.1
  commutator_compact z := (even_reduced_source_defects β α c z).2.2
  equivariance_mod_compact g z :=
    ordinaryTargetAction_defect_compact (E := E) β g
      (operatorHom β E c.operator)
      (reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z)

/-- The raw odd picture keeps its genuine ungraded module and Fredholm operator. -/
def oddCycle (c : OddKasparovCycle α β E) :
    OddKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (Module β E) where
  countablyGenerated := KasparovDescent.countablyGenerated β E c.countablyGenerated
  groupAction := ordinaryTargetAction (E := E) β
  representation := reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant
  representation_equivariant := by
    intro g z
    exact ordinaryTargetAction_conjugate (E := E) β g _
  operator := operatorHom β E c.operator
  selfadjoint_mod_compact z := (odd_reduced_source_defects β α c z).1
  square_mod_compact z := (odd_reduced_source_defects β α c z).2.1
  commutator_compact z := (odd_reduced_source_defects β α c z).2.2
  equivariance_mod_compact g z :=
    ordinaryTargetAction_defect_compact (E := E) β g
      (operatorHom β E c.operator)
      (reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z)

@[simp] theorem evenCycle_operator (c : KasparovCycle α β E) :
    (evenCycle β α c).operator = operatorHom β E c.operator := rfl

@[simp] theorem oddCycle_operator (c : OddKasparovCycle α β E) :
    (oddCycle β α c).operator = operatorHom β E c.operator := rfl

end BC4lean.KKTheory.KasparovDescent
