import BC4lean.KasparovDescentGradedCycle
import BC4lean.GradedKasparovRegrade
import BC4lean.GroupUniverseEvenBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual coherence with the native even/graded bridge

The only grading-index transports below use
the proved fact that the actual crossed grading of a trivial grading is
trivial. The whole-module isomorphism is the identity, and its grading law
is proved by actual tensor density. No bridge compatibility is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B E : Type*} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)

/-- The actual descended graded cycle with its provably trivial indices. -/
def trivialGradedCycle
    (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E) :=
  (gradedCycle β α c).regrade (reducedCrossedProductGrading_trivial α)
    (reducedCrossedProductGrading_trivial β)

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] in
/-- Both genuine induced module gradings coincide on whole vectors; their
identity on crossed coefficients is the proved crossed trivial-grading law. -/
theorem moduleGrading_trivial_apply
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) (u : Module β E) :
    (moduleGrading β CStarGrading.trivial β.preservesGrading_trivial J).grading u =
      (ordinaryModuleGrading β J).grading u := by
  let L := (moduleGrading β CStarGrading.trivial β.preservesGrading_trivial J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let R := (ordinaryModuleGrading β J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L = R := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x d
    change (moduleGrading β CStarGrading.trivial β.preservesGrading_trivial J).grading (mk β E x d) =
      (ordinaryModuleGrading β J).grading (mk β E x d)
    rw [moduleGrading_mk, ordinaryModuleGrading_mk,
      reducedCrossedProductGrading_trivial_apply, MulOpposite.op_unop]
  exact DFunLike.congr_fun h u

private theorem evenGradedDescentIso_grading_aux
    (c : KasparovCycle α β E) (u : Module β E) :
    (trivialGradedCycle β α (GradedKasparovCycle.ofKasparovCycle c)).grading.grading u =
      (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c)).grading.grading u := by
  exact (GradedKasparovCycle.regrade_grading_apply
    (Γ := Unit) (A := ReducedCrossedProduct α)
    (B := ReducedCrossedProduct β) (E := Module β E)
    (gradedCycle (E := E) β α (GradedKasparovCycle.ofKasparovCycle c))
    (reducedCrossedProductGrading_trivial (Γ := Γ) (B := A) α)
    (reducedCrossedProductGrading_trivial (Γ := Γ) (B := B) β) u).trans
      (moduleGrading_trivial_apply (Γ := Γ) (B := B) (E := E) β c.grading u)

private theorem evenGradedDescentIso_action_aux
    (c : KasparovCycle α β E) (g : Unit) (u : Module β E) :
    (trivialGradedCycle β α (GradedKasparovCycle.ofKasparovCycle c)).groupAction.action g u =
      (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c)).groupAction.action g u := by
  exact congrArg
    (fun V : EquivariantHilbertModule
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (Module β E) => V.action g u)
    (GradedKasparovCycle.regrade_action
      (Γ := Unit) (A := ReducedCrossedProduct α)
      (B := ReducedCrossedProduct β) (E := Module β E)
      (gradedCycle (E := E) β α (GradedKasparovCycle.ofKasparovCycle c))
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := A) α)
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := B) β))

private theorem evenGradedDescentIso_representation_aux
    (c : KasparovCycle α β E) (z : ReducedCrossedProduct α) (u : Module β E) :
    (trivialGradedCycle β α (GradedKasparovCycle.ofKasparovCycle c)).representation z u =
      (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c)).representation z u := by
  exact congrArg
    (fun ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) => ρ z u)
    (GradedKasparovCycle.regrade_representation
      (Γ := Unit) (A := ReducedCrossedProduct α)
      (B := ReducedCrossedProduct β) (E := Module β E)
      (gradedCycle (E := E) β α (GradedKasparovCycle.ofKasparovCycle c))
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := A) α)
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := B) β))

private theorem evenGradedDescentIso_operator_aux
    (c : KasparovCycle α β E) (u : Module β E) :
    (trivialGradedCycle β α (GradedKasparovCycle.ofKasparovCycle c)).operator u =
      (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c)).operator u := by
  exact congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) => T u)
    (GradedKasparovCycle.regrade_operator
      (Γ := Unit) (A := ReducedCrossedProduct α)
      (B := ReducedCrossedProduct β) (E := Module β E)
      (gradedCycle (E := E) β α (GradedKasparovCycle.ofKasparovCycle c))
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := A) α)
      (reducedCrossedProductGrading_trivial (Γ := Γ) (B := B) β))

/-- Actual graded descent commutes with the original even raw conversion,
through the constructed identity whole-cycle unitary. -/
def evenGradedDescentIso (c : KasparovCycle α β E) :
    GradedKasparovCycleIso (trivialGradedCycle β α (GradedKasparovCycle.ofKasparovCycle c))
      (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine u := evenGradedDescentIso_grading_aux (E := E) β α c u
  action_intertwine g u := evenGradedDescentIso_action_aux (E := E) β α c g u
  representation_intertwine z u :=
    evenGradedDescentIso_representation_aux (E := E) β α c z u
  operator_intertwine u := evenGradedDescentIso_operator_aux (E := E) β α c u

/-- The same isomorphism for an arbitrary actual trivially graded cycle,
using the already proved inverse raw conversion to the existing even cycle. -/
def toEvenDescentIso
    (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E) :
    GradedKasparovCycleIso (trivialGradedCycle β α c)
      (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c.toKasparovCycle)) := by
  simpa only [GradedKasparovCycle.ofKasparovCycle_toKasparovCycle] using
    evenGradedDescentIso β α c.toKasparovCycle

end BC4lean.KKTheory.KasparovDescent
