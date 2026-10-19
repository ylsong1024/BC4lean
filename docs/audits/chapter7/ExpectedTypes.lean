import BC4lean.ReducedCutoffProjection
import BC4lean.ReducedCrossedNorm
import BC4lean.ReducedCrossedScalarProduct
import BC4lean.KasparovDescentCompactAction
import BC4lean.CocompactPieceCutoff
import BC4lean.KasparovDescentModule
import BC4lean.AssemblyModelNaturality
import BC4lean.AssemblyCofinalIndex
import BC4lean.KasparovDescentClass
import BC4lean.KasparovDescentNativeParityProduct
import BC4lean.KasparovDescentGradedClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Independent mathematical signatures for the Chapter 7 construction.
The examples check the concrete completed coefficients, normalized cutoff,
reduced representation, full homotopies, existing native products and actual
assembly homomorphisms. Desired conclusions are checked against definitions
and proved endpoints; they are not extra inputs to those constructions.
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

noncomputable section
universe uΓ uA uB uE
open BC4lean BC4lean.KKTheory BC4lean.ProperActions
open scoped KasparovDescent

section ActualReducedRepresentation
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a)) :
    ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β)
        (KasparovDescent.Module β E) (KasparovDescent.Module β E) :=
  KasparovDescent.reducedSourceRepresentation β E α U π hπ

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (f : AlgebraicCrossedProduct α) :
    ‖KasparovDescent.algebraicSourceOperatorHom β E α U π hπ f‖ ≤
      ‖algebraicCrossedOperatorHom α f‖ :=
  KasparovDescent.algebraicSourceOperator_norm_le β E α U π hπ f

variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

-- The raw cycles retain the actual input operator and constructed action.
example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (c : KasparovCycle α β E) :
    (KasparovDescent.evenCycle β α c).operator =
      KasparovDescent.operatorHom β E c.operator := rfl

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (c : OddKasparovCycle α β E) :
    (KasparovDescent.oddCycle β α c).operator =
      KasparovDescent.operatorHom β E c.operator := rfl

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (c : KasparovCycle α β E) (z : ReducedCrossedProduct α) :
    (KasparovDescent.evenCycle β α c).representation z =
      KasparovDescent.reducedSourceRepresentation β E α c.groupAction
        c.representation c.representation_equivariant z := rfl

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (c : OddKasparovCycle α β E) (z : ReducedCrossedProduct α) :
    (KasparovDescent.oddCycle β α c).representation z =
      KasparovDescent.reducedSourceRepresentation β E α c.groupAction
        c.representation c.representation_equivariant z := rfl
end ActualReducedRepresentation

section ActualQuotients
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A) :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →+
      KasparovHomotopyClass.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)}
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  KasparovDescent.evenClassHom β α

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A) :
    OddKK.{uΓ, uA, uB, uE} α β →+
      OddKK.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)}
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  KasparovDescent.oddClassHom β α

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β} (H : FullKasparovHomotopy c d) :
    FullKasparovHomotopy
      (KasparovDescent.bundledEvenCycle β α c)
      (KasparovDescent.bundledEvenCycle β α d) :=
  KasparovDescent.evenFullHomotopy β α H

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β} (H : FullOddKasparovHomotopy c d) :
    FullOddKasparovHomotopy
      (KasparovDescent.bundledOddCycle β α c)
      (KasparovDescent.bundledOddCycle β α d) :=
  KasparovDescent.oddFullHomotopy β α H

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    KasparovDescent.evenClassHom β α (KasparovHomotopyClass.mk c) =
      KasparovHomotopyClass.mk (KasparovDescent.bundledEvenCycle β α c) := rfl

example (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
    (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    KasparovDescent.oddClassHom β α (OddKK.mk c) =
      OddKK.mk (KasparovDescent.bundledOddCycle β α c) := rfl
end ActualQuotients

section ActualNativeProduct
universe uC u
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC}
  [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]

-- This statement uses the pre-existing native product on both sides.
-- Boolean p,q quantify all four parity branches, including odd-odd.
example (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (γ : CStarAlgebraAction Γ C) (p q : Bool)
    (x : BC4lean.KKTheory.GroupUniverseParityGroup.KKParityGroup.{uΓ,uA,uB,
      max u (max uΓ (max uA (max uB uC)))} p α β)
    (y : BC4lean.KKTheory.GroupUniverseParityGroup.KKParityGroup.{uΓ,uB,uC,
      max u (max uΓ (max uA (max uB uC)))} q β γ) :
    KasparovDescent.classHom γ α (Bool.xor p q)
        (BC4lean.KKTheory.GroupUniverseCommonParityProduct.product.{uΓ,uA,uB,uC,max u uΓ} p q x y) =
      BC4lean.KKTheory.GroupUniverseCommonParityProduct.product.{0,max uΓ uA,max uΓ uB,max uΓ uC,u} p q
        (KasparovDescent.classHom β α p x) (KasparovDescent.classHom γ β q y) :=
  KasparovDescent.classHom_product α β γ p q x y
end ActualNativeProduct

section ActualAssembly
variable (Γ : Type*) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type*) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

example (S : CocompactPiece Γ X) :
    TopologicalKHomology.pieceGroup false S →+ ReducedK0 Γ :=
  Assembly.pieceAssemblyEvenHom Γ X S

example (S : CocompactPiece Γ X) :
    TopologicalKHomology.pieceGroup true S →+ ReducedK1 Γ :=
  Assembly.pieceAssemblyOddHom Γ X S

example : TopologicalKHomology.group (Γ := Γ) (X := X) false →+ ReducedK0 Γ :=
  Assembly.assemblyEvenHom Γ X

example : TopologicalKHomology.group (Γ := Γ) (X := X) true →+ ReducedK1 Γ :=
  Assembly.assemblyOddHom Γ X

example (p : Bool) (S : CocompactPiece Γ X)
    (x : TopologicalKHomology.pieceGroup p S) :
    Assembly.assemblyHom Γ X p (TopologicalKHomology.ofPiece p S x) =
      Assembly.pieceAssemblyHom Γ X p S x :=
  Assembly.assemblyHom_ofPiece Γ X p S x

example (p : Bool)
    (F : TopologicalKHomology.group (Γ := Γ) (X := X) p →+ Assembly.analyticGroup Γ p)
    (hF : ∀ S : CocompactPiece Γ X,
      F.comp (TopologicalKHomology.ofPiece p S) = Assembly.pieceAssemblyHom Γ X p S) :
    F = Assembly.assemblyHom Γ X p :=
  Assembly.assemblyHom_unique Γ X p F hF

-- The representative value is the concrete cutoff/native-product formula.
example (p : Bool) (S : CocompactPiece Γ X)
    (x : TopologicalKHomology.pieceGroup p S) :
    letI : LocallyCompactSpace S.toInvariantSubset := S.locallyCompact
    Assembly.pieceAssemblyHom Γ X p S x =
      Assembly.reducedScalarKKToAnalyticHom Γ p
        (Assembly.cutoffProductHom Γ S.toInvariantSubset p (Assembly.pieceCutoff Γ X S)
          (KasparovDescent.classHom
            (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := S.toInvariantSubset)) p x)) := by
  let : LocallyCompactSpace S.toInvariantSubset := S.locallyCompact
  rfl

example (p : Bool) {S T : CocompactPiece Γ X} (h : S ≤ T)
    (x : TopologicalKHomology.pieceGroup p S) :
    Assembly.pieceAssemblyHom Γ X p T (TopologicalKHomology.transition p h x) =
      Assembly.pieceAssemblyHom Γ X p S x :=
  Assembly.pieceAssemblyHom_transition Γ X p h x

variable {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]

-- The actual cofinality condition is a hypothesis; pointwise covering is not used.
example (p : Bool) (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j)
    (x : ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).Colimit) :
    Assembly.assemblyHom Γ X p (TopologicalKHomology.cofinalIndexEquiv p φ hφ x) =
      Assembly.indexedAssemblyHom Γ X p φ x :=
  Assembly.assemblyHom_cofinalIndexEquiv Γ X p φ hφ x

variable {L : Type*} [Preorder L] [Nonempty L] [IsDirectedOrder L]

example (p : Bool) (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) (hψ : ∀ S, ∃ j, S ≤ ψ j)
    (x : ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).Colimit) :
    Assembly.indexedAssemblyHom Γ X p ψ
        ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalComparisonEquiv
          φ ψ hφ hψ x) = Assembly.indexedAssemblyHom Γ X p φ x :=
  Assembly.indexedAssemblyHom_cofinalComparisonEquiv Γ X p φ ψ hφ hψ x
end ActualAssembly

section ActualModelMap
universe umΓ umX
-- Chapter 6's actual pushforward API compares spaces in one ambient universe.
variable (Γ : Type umΓ) (X Y : Type umX) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [TopologicalSpace X] [TopologicalSpace Y] [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [ProperSMul Γ X] [ProperSMul Γ Y]

-- The ambient comparison map is not assumed globally proper.
example (p : Bool) (f : EquivariantMap Γ X Y)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    Assembly.assemblyHom Γ Y p (TopologicalKHomology.pushforward p f x) =
      Assembly.assemblyHom Γ X p x :=
  Assembly.assemblyHom_pushforward Γ X Y p f x
end ActualModelMap

section ActualCanonicalAssembly
variable (Γ : Type*) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]

example : TopologicalKHomology.topologicalGroup false Γ →+ ReducedK0 Γ :=
  Assembly.reducedAssemblyEvenHom Γ

example : TopologicalKHomology.topologicalGroup true Γ →+ ReducedK1 Γ :=
  Assembly.reducedAssemblyOddHom Γ
end ActualCanonicalAssembly

-- Independent signatures for arbitrary source and coefficient algebra gradings.
-- All six examples use the original complete countably generated cycles or
-- full interval witnesses; desired descended data are not additional inputs.
section ActualGradedDescent
universe ugΓ ugA ugB ugE
variable {Γ : Type ugΓ} {A : Type ugA} {B : Type ugB} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
  (δA : CStarGrading A) (δB : CStarGrading B)
  (hα : α.PreservesGrading δA) (hβ : β.PreservesGrading δB)

-- The target is a genuine cycle with both actual induced crossed gradings.
example {E : Type ugE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (reducedCrossedProductGrading α δA hα)
      (reducedCrossedProductGrading β δB hβ) (KasparovDescent.Module β E) :=
  KasparovDescent.gradedCycle β α c

-- One actual module unitary intertwines all four pieces of the graded cycle.
example {E F : Type ugE}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
    [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
    {c : GradedKasparovCycle α β δA δB E}
    {d : GradedKasparovCycle α β δA δB F} (u : GradedKasparovCycleIso c d) :
    GradedKasparovCycleIso
      (show GradedKasparovCycle
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
        (reducedCrossedProductGrading α δA hα)
        (reducedCrossedProductGrading β δB hβ) (KasparovDescent.Module β E) from
        KasparovDescent.gradedCycle β α c)
      (show GradedKasparovCycle
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
        (reducedCrossedProductGrading α δA hα)
        (reducedCrossedProductGrading β δB hβ) (KasparovDescent.Module β F) from
        KasparovDescent.gradedCycle β α d) :=
  KasparovDescent.gradedCycleIso β α u

-- This retains the full witness's arbitrary interval coefficient module.
example {c d : BundledGradedKasparovCycle.{ugΓ,ugA,ugB,ugE} α β δA δB}
    (H : FullGradedKasparovHomotopy c d) :
    FullGradedKasparovHomotopy.{0,max ugΓ ugA,max ugΓ ugB,max ugE (max ugΓ ugB)}
      (KasparovDescent.bundledGradedCycleFixed β α hα hβ c)
      (KasparovDescent.bundledGradedCycleFixed β α hα hβ d) :=
  KasparovDescent.gradedFullHomotopyFixed β α hα hβ H

-- The actual arbitrary-module fibre unitary is a whole graded cycle unitary.
example {M : Type ugE} [NormedAddCommGroup M] [NormedSpace ℂ M]
    [SMul C(unitInterval, B)ᵐᵒᵖ M]
    [CStarModule C(unitInterval, B)ᵐᵒᵖ M] [CompleteSpace M]
    (c : GradedKasparovCycle α (β.continuousSections (X := unitInterval))
      δA δB.continuousSections M) (t : unitInterval) :
    GradedKasparovCycleIso
      (show GradedKasparovCycle
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
        (reducedCrossedProductGrading α δA hα)
        (reducedCrossedProductGrading β δB hβ)
        (HilbertModuleFibre (ReducedCrossedProduct β)
          (KasparovDescent.IntervalModule (X := unitInterval) β M) t) from
        (KasparovDescent.intervalGradedCycle β M α hβ c).fibre t)
      (show GradedKasparovCycle
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
        (reducedCrossedProductGrading α δA hα)
        (reducedCrossedProductGrading β δB hβ)
        (KasparovDescent.Module β (HilbertModuleFibre B M t)) from
        KasparovDescent.gradedCycle β α (c.fibre t)) :=
  KasparovDescent.intervalGradedCycleFibreIso β M α hβ c t

-- General graded full-homotopy classes currently carry precisely AddHom here.
example : AddHom
    (GradedKasparovHomotopyClass.{ugΓ,ugA,ugB,ugE} α β δA δB)
    (GradedKasparovHomotopyClass.{0,max ugΓ ugA,max ugΓ ugB,max ugE (max ugΓ ugB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (reducedCrossedProductGrading α δA hα)
      (reducedCrossedProductGrading β δB hβ)) :=
  KasparovDescent.gradedClassHom β α hα hβ

-- The raw cycle stores the original lifted operator and completed source action.
example {E : Type ugE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : GradedKasparovCycle α β δA δB E) (z : ReducedCrossedProduct α) :
    (KasparovDescent.gradedCycle β α c).operator =
        KasparovDescent.operatorHom β E c.operator ∧
      (KasparovDescent.gradedCycle β α c).representation z =
        KasparovDescent.reducedSourceRepresentation β E α c.groupAction
          c.representation c.representation_equivariant z := ⟨rfl, rfl⟩
end ActualGradedDescent
