import BC4lean.KasparovDescentCycleIso
import BC4lean.GradedMatrixMoritaTensorDirectSumCycle
import BC4lean.OddKasparovDirectSumIso

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Whole-cycle direct-sum compatibility of actual reduced descent

The construction uses the concrete reduced source representation and raw cycle
prerequisites. The generic
first-factor tensor distributivity theorem is reused from the existing checked
GradedMatrixMoritaTensorDirectSum module; its name does not restrict its
representation to a matrix-Morita example.

No direct-sum compatibility is assumed. The underlying map is constructed from
the coefficient form and pure-tensor density. Its grading, actual group
operators and integrated source representation are genuinely intertwined.
The target ordinary cycle action is the trivial Unit action. This is the
additivity input for a later full homotopy quotient map; it does not itself
define that quotient map or assert compatibility with Kasparov products.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

variable (β : CStarAlgebraAction Γ B)

local instance descentSourceSumComplete : CompleteSpace (HilbertModuleSum B E F) :=
  hilbertModuleSum_complete
local instance descentTargetSumComplete : CompleteSpace
    (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β F)) :=
  hilbertModuleSum_complete

/-- The concrete completed coefficient-form tensor distributivity unitary. -/
def sumModuleEquiv : HilbertModuleEquiv (ReducedCrossedProduct β)
    (Module β (HilbertModuleSum B E F))
    (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β F)) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv (coefficientRepresentation β)

@[simp] theorem sumModuleEquiv_mk (x : HilbertModuleSum B E F)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    sumModuleEquiv β (mk β (HilbertModuleSum B E F) x c) =
      sumMk (mk β E x.fst c) (mk β F x.snd c) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv_mk (coefficientRepresentation β) x c

theorem sumModuleEquiv_operator (S : AdjointableMap B E E) (T : AdjointableMap B F F)
    (z : Module β (HilbertModuleSum B E F)) :
    sumModuleEquiv β (operatorHom β (HilbertModuleSum B E F) (sumMap S T) z) =
      sumMap (operatorHom β E S) (operatorHom β F T) (sumModuleEquiv β z) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv_operator (coefficientRepresentation β) S T z

theorem sumModuleEquiv_grading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (K : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) F)
    (z : Module β (HilbertModuleSum B E F)) :
    sumModuleEquiv β ((ordinaryModuleGrading β (J.sum K)).grading z) =
      ((ordinaryModuleGrading β J).sum (ordinaryModuleGrading β K)).grading
        (sumModuleEquiv β z) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv_grading (coefficientRepresentation β) J K
    (GradedHilbertModule.trivial (B := ReducedCrossedProduct β)
      (E := (ReducedCrossedProduct β)ᵐᵒᵖ)) (fun _ _ => rfl) z

theorem sumModuleEquiv_groupOperator (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule β F) (g : Γ)
    (z : Module β (HilbertModuleSum B E F)) :
    sumModuleEquiv β (groupOperator β (HilbertModuleSum B E F) (U.sum V) g z) =
      sumMap (groupOperator β E U g) (groupOperator β F V g) (sumModuleEquiv β z) := by
  simpa only [sumModuleEquiv, groupOperator_apply, groupAction, sumMap_apply,
    EquivariantHilbertModule.sum_action_apply] using
    GradedMatrixMoritaTensorDirectSum.hilbertEquiv_action (coefficientRepresentation β)
      U V (leftRegularAction β) (coefficientRepresentation_equivariant β) g z

omit [PartialOrder A] [StarOrderedRing A] in
/-- Both genuine crossed generators are carried to the block sum. -/
theorem sumModuleEquiv_sourceGenerator (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule β F)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (σ : A →⋆ₙₐ[ℂ] AdjointableMap B F F) (a : A) (g : Γ)
    (z : Module β (HilbertModuleSum B E F)) :
    sumModuleEquiv β
      (sourceGenerator β (HilbertModuleSum B E F) (U.sum V) (sumRepresentation π σ) a g z) =
      sumMap (sourceGenerator β E U π a g) (sourceGenerator β F V σ a g)
        (sumModuleEquiv β z) := by
  change sumModuleEquiv β
      (operatorHom β (HilbertModuleSum B E F) (sumMap (π a) (σ a))
        (groupOperator β (HilbertModuleSum B E F) (U.sum V) g z)) =
    sumMap (operatorHom β E (π a) * groupOperator β E U g)
      (operatorHom β F (σ a) * groupOperator β F V g) (sumModuleEquiv β z)
  calc
    sumModuleEquiv β
        (operatorHom β (HilbertModuleSum B E F) (sumMap (π a) (σ a))
          (groupOperator β (HilbertModuleSum B E F) (U.sum V) g z)) =
      sumMap (operatorHom β E (π a)) (operatorHom β F (σ a))
        (sumModuleEquiv β (groupOperator β (HilbertModuleSum B E F) (U.sum V) g z)) :=
      sumModuleEquiv_operator (Γ := Γ) (B := B) (E := E) (F := F)
        β (π a) (σ a) (groupOperator β (HilbertModuleSum B E F) (U.sum V) g z)
    _ = sumMap (operatorHom β E (π a)) (operatorHom β F (σ a))
        (sumMap (groupOperator β E U g) (groupOperator β F V g) (sumModuleEquiv β z)) :=
      congrArg
        (fun w : HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β F) =>
          sumMap (operatorHom β E (π a)) (operatorHom β F (σ a)) w)
        (sumModuleEquiv_groupOperator (Γ := Γ) (B := B) (E := E) (F := F) β U V g z)
    _ = sumMap (operatorHom β E (π a) * groupOperator β E U g)
        (operatorHom β F (σ a) * groupOperator β F V g) (sumModuleEquiv β z) :=
      congrArg
        (fun T : AdjointableMap (ReducedCrossedProduct β)
            (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β F))
            (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β F)) =>
          T (sumModuleEquiv β z))
        (sumMap_mul (B := ReducedCrossedProduct β) (E := Module β E) (F := Module β F)
          (operatorHom β E (π a)) (groupOperator β E U g)
          (operatorHom β F (σ a)) (groupOperator β F V g)).symm

variable (α : CStarAlgebraAction Γ A)

/-- Density proves direct-sum compatibility for the actual completed source
representation, rather than merely for a formal finite-sum surrogate. -/
theorem sumModuleEquiv_reducedSourceRepresentation
    (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (σ : A →⋆ₙₐ[ℂ] AdjointableMap B F F)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (hσ : ∀ g a, V.conjugateOperator g (σ a) = σ (α.automorphism g a))
    (hSum : ∀ g a, (U.sum V).conjugateOperator g (sumRepresentation π σ a) =
      sumRepresentation π σ (α.automorphism g a))
    (z : ReducedCrossedProduct α) (x : Module β (HilbertModuleSum B E F)) :
    sumModuleEquiv β
      (reducedSourceRepresentation β (HilbertModuleSum B E F) α
        (U.sum V) (sumRepresentation π σ) hSum z x) =
      sumMap (reducedSourceRepresentation β E α U π hπ z)
        (reducedSourceRepresentation β F α V σ hσ z) (sumModuleEquiv β x) := by
  have hS : Continuous (fun w : ReducedCrossedProduct α =>
      reducedSourceRepresentation β (HilbertModuleSum B E F) α
        (U.sum V) (sumRepresentation π σ) hSum w x) :=
    ((AdjointableMap.toCLM_isometry
      (B := ReducedCrossedProduct β)
      (E := Module β (HilbertModuleSum B E F))
      (F := Module β (HilbertModuleSum B E F))).continuous.comp
      (continuous_reducedSourceRepresentation β (HilbertModuleSum B E F) α
        (U.sum V) (sumRepresentation π σ) hSum)).clm_apply continuous_const
  have hT : Continuous (fun w : ReducedCrossedProduct α =>
      sumMap (reducedSourceRepresentation β E α U π hπ w)
        (reducedSourceRepresentation β F α V σ hσ w) (sumModuleEquiv β x)) := by
    have hblock :
        (fun w : ReducedCrossedProduct α =>
          sumMap (reducedSourceRepresentation β E α U π hπ w)
            (reducedSourceRepresentation β F α V σ hσ w) (sumModuleEquiv β x)) =
        (fun w : ReducedCrossedProduct α =>
          sumMk (B := ReducedCrossedProduct β)
            (reducedSourceRepresentation β E α U π hπ w (sumModuleEquiv β x).fst)
            (reducedSourceRepresentation β F α V σ hσ w (sumModuleEquiv β x).snd)) := by
      funext w
      exact sumMap_apply (B := ReducedCrossedProduct β)
        (reducedSourceRepresentation β E α U π hπ w)
        (reducedSourceRepresentation β F α V σ hσ w) (sumModuleEquiv β x)
    rw [hblock]
    have hE : Continuous (fun w : ReducedCrossedProduct α =>
        reducedSourceRepresentation β E α U π hπ w (sumModuleEquiv β x).fst) :=
      ((AdjointableMap.toCLM_isometry
        (B := ReducedCrossedProduct β) (E := Module β E) (F := Module β E)).continuous.comp
        (continuous_reducedSourceRepresentation β E α U π hπ)).clm_apply continuous_const
    have hF : Continuous (fun w : ReducedCrossedProduct α =>
        reducedSourceRepresentation β F α V σ hσ w (sumModuleEquiv β x).snd) :=
      ((AdjointableMap.toCLM_isometry
        (B := ReducedCrossedProduct β) (E := Module β F) (F := Module β F)).continuous.comp
        (continuous_reducedSourceRepresentation β F α V σ hσ)).clm_apply continuous_const
    exact (WithCStarModule.equivL ℂ (A := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (E := Module β E × Module β F)).symm.continuous.comp (hE.prodMk hF)
  refine (algebraicToReducedCrossed_denseRange α).induction_on z
    (isClosed_eq ((sumModuleEquiv (E := E) (F := F) β).linearIsometryEquiv.continuous.comp hS) hT) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero =>
    simp only [map_zero, AdjointableMap.coe_zero_apply,
      sumMap_zero]
  | single g a =>
    simpa only [reducedSourceRepresentation_single] using
      sumModuleEquiv_sourceGenerator β U V π σ a g x
  | add f h ihf ihh =>
    simp only [map_add, AdjointableMap.coe_add_apply,
      sumMap_add, ihf, ihh]

variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- The actual descended even cycle of a direct sum is isomorphic to the direct
sum of the actual descended cycles, including every part of cycle data. -/
def evenDirectSumIso (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycleIso (evenCycle β α (c.directSum d))
      ((evenCycle β α c).directSum (evenCycle β α d)) where
  moduleEquiv := sumModuleEquiv β
  grading_intertwine := sumModuleEquiv_grading β c.grading d.grading
  action_intertwine _ _ := rfl
  representation_intertwine := sumModuleEquiv_reducedSourceRepresentation β α
    c.groupAction d.groupAction c.representation d.representation
    c.representation_equivariant d.representation_equivariant
    (c.directSum d).representation_equivariant
  operator_intertwine := sumModuleEquiv_operator β c.operator d.operator

/-- The same genuine additivity isomorphism in the odd picture. -/
def oddDirectSumIso (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) :
    OddKasparovCycleIso (oddCycle β α (c.directSum d))
      ((oddCycle β α c).directSum (oddCycle β α d)) where
  moduleEquiv := sumModuleEquiv β
  action_intertwine _ _ := rfl
  representation_intertwine := sumModuleEquiv_reducedSourceRepresentation β α
    c.groupAction d.groupAction c.representation d.representation
    c.representation_equivariant d.representation_equivariant
    (c.directSum d).representation_equivariant
  operator_intertwine := sumModuleEquiv_operator β c.operator d.operator

end BC4lean.KKTheory.KasparovDescent
