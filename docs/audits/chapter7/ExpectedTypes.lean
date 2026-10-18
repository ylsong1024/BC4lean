import BC4lean.ReducedCutoffProjection
import BC4lean.ReducedCrossedNorm
import BC4lean.ReducedCrossedScalarProduct
import BC4lean.KasparovDescentCompactAction
import BC4lean.CocompactPieceCutoff
import BC4lean.KasparovDescentModule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Independent mathematical signatures for the Chapter 7 milestone.
These signatures retain the actual completed C*-algebra, real compactly
supported cutoff formula, finite-support coefficient algebra and scalar-kernel
operator K₀. No assembly or Kasparov-descent endpoint is assumed.
-/

noncomputable section
open scoped CompactlySupported ZeroAtInfty ComplexOrder
open BC4lean BC4lean.KKTheory BC4lean.ProperActions

section Algebra
variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

example (α : CStarAlgebraAction Γ B) :
    NonUnitalCStarAlgebra (ReducedCrossedProduct α) := inferInstance

example [Countable Γ] [TopologicalSpace.SeparableSpace B] (α : CStarAlgebraAction Γ B) :
    TopologicalSpace.SeparableSpace (ReducedCrossedProduct α) := reducedCrossedProduct_separableSpace α

example (α : CStarAlgebraAction Γ B) :
    Function.Injective (algebraicToReducedCrossed α) := algebraicToReducedCrossed_injective α

example (α : CStarAlgebraAction Γ B) : DenseRange (algebraicToReducedCrossed α) :=
  algebraicToReducedCrossed_denseRange α

example (α : CStarAlgebraAction Γ B) (f : AlgebraicCrossedProduct α) :
    algebraicCrossedReducedNorm α f = 0 ↔ f = 0 := algebraicCrossedReducedNorm_eq_zero α f

example (α : CStarAlgebraAction Γ B) (f : AlgebraicCrossedProduct α) :
    algebraicCrossedReducedNorm α (star f * f) = algebraicCrossedReducedNorm α f ^ 2 :=
  algebraicCrossedReducedNorm_cstar α f

example : ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) ≃⋆ₐ[ℂ]
    ReducedGroupCStar Γ := reducedCrossedScalarProductEquiv
end Algebra

section Cutoff
variable {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  [TopologicalSpace X] [MulAction Γ X] [ProperSMul Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]

example (S : CocompactPiece Γ X) :
    Nonempty (Cutoff.CutoffFunction Γ S.toInvariantSubset) := CocompactPiece.exists_cutoffFunction S

example [CompactSpace (Quotient (MulAction.orbitRel Γ X))] :
    Nonempty (Cutoff.CutoffFunction Γ X) := Cutoff.exists_cutoffFunction

example (c : Cutoff.CutoffFunction Γ X) (x : X) :
    (∑' g : Γ, c (g⁻¹ • x) ^ 2) = 1 := Cutoff.normalized_tsum c x

example (c : Cutoff.CutoffFunction Γ X) (g : Γ) (x : X) :
    AlgebraicCrossedProduct.coeff (CZero.action Γ) (Cutoff.algebraicProjection c) g x =
      ((c x * c (g⁻¹ • x) : ℝ) : ℂ) := rfl

example (c : Cutoff.CutoffFunction Γ X) :
    IsStarProjection (Cutoff.reducedCutoffProjection c) :=
  Cutoff.reducedCutoffProjection_isStarProjection c

example (c d : Cutoff.CutoffFunction Γ X) :
    ∃ v : ReducedCrossedProduct (CZero.action Γ (X := X)),
      star v * v = Cutoff.reducedCutoffProjection c ∧
      v * star v = Cutoff.reducedCutoffProjection d :=
  Cutoff.reducedCutoffProjection_partialIsometry c d

example (c : Cutoff.CutoffFunction Γ X) :
    OperatorKTheory.OperatorK0 (ReducedCrossedProduct (CZero.action Γ (X := X))) := Cutoff.cutoffK0 c

example (c d : Cutoff.CutoffFunction Γ X) : Cutoff.cutoffK0 c = Cutoff.cutoffK0 d :=
  Cutoff.cutoffK0_independent c d
end Cutoff

section CompactConjugation
variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {β : CStarAlgebraAction Γ B}

example (U : EquivariantHilbertModule β E) :
    CStarAlgebraAction Γ (CompactModuleOperator B E) := U.compactOperatorAction

example (U : EquivariantHilbertModule β E) (g : Γ)
    (T : CompactModuleOperator B E) (x : E) :
    (U.compactOperatorAction.automorphism g T : AdjointableMap B E E) x =
      U.action g ((T : AdjointableMap B E E) (U.action g⁻¹ x)) := rfl

example (U : EquivariantHilbertModule β E) (g : Γ) (x y : E) :
    (U.compactOperatorAction.automorphism g
      ⟨moduleRankOne x y, moduleRankOne_mem_moduleCompact x y⟩ : AdjointableMap B E E) =
      moduleRankOne (U.action g x) (U.action g y) := by
  exact congrArg Subtype.val (U.compactOperatorAction_rankOne g x y)
end CompactConjugation

section ActualDescentModule
open scoped KasparovDescent
variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

-- The carrier is the actual completed interior tensor using the concrete
-- crossed-product coefficient inclusion; no descended cycle is an input.
example (β : CStarAlgebraAction Γ B) :
    KasparovDescent.Module β E =
      InteriorModuleTensor (E := E)
        (standardLeftMul.comp (coefficientToReducedCrossed β)) := rfl

example (β : CStarAlgebraAction Γ B) :
    CompleteSpace (InteriorModuleTensor (E := E)
      (standardLeftMul.comp (coefficientToReducedCrossed β))) := inferInstance

example [Countable Γ] [TopologicalSpace.SeparableSpace B]
    (β : CStarAlgebraAction Γ B) (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule (ReducedCrossedProduct β)
      (InteriorModuleTensor (E := E)
        (standardLeftMul.comp (coefficientToReducedCrossed β))) :=
  KasparovDescent.countablyGenerated β E hE

example (β : CStarAlgebraAction Γ B) :
    AdjointableMap B E E →⋆ₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β)
        (InteriorModuleTensor (E := E)
          (standardLeftMul.comp (coefficientToReducedCrossed β)))
        (InteriorModuleTensor (E := E)
          (standardLeftMul.comp (coefficientToReducedCrossed β))) :=
  KasparovDescent.operatorHom β E

example (β : CStarAlgebraAction Γ B) (T : AdjointableMap B E E)
    (hT : IsModuleCompact T) :
    IsModuleCompact (interiorModuleTensorOperator
      (standardLeftMul.comp (coefficientToReducedCrossed β)) T) :=
  KasparovDescent.operatorHom_compact β E hT
end ActualDescentModule
