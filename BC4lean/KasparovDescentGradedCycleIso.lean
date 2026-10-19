import BC4lean.KasparovDescentGradedCycle
import BC4lean.KasparovDescentCycleIso
import BC4lean.GradedKasparovCycleIso

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine whole-cycle unitaries for fully graded descent

The construction uses the concrete reduced norm bridge and induced crossed
gradings. The module unitary is the actual
completed first-factor tensor unitary. Its same map intertwines all four
parts of the whole graded cycle, including the completed source action.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

variable (β : CStarAlgebraAction Γ B)

theorem moduleEquiv_graded_grading (δB : CStarGrading B) (hβ : β.PreservesGrading δB)
    (u : HilbertModuleEquiv B E F) (J : GradedHilbertModule δB E)
    (K : GradedHilbertModule δB F)
    (hJK : ∀ x, u (J.grading x) = K.grading (u x)) (z : Module β E) :
    moduleEquiv β u ((moduleGrading β δB hβ J).grading z) =
      (moduleGrading β δB hβ K).grading (moduleEquiv β u z) := by
  let L : Module β E →L[ℂ] Module β F :=
    (moduleEquiv β u).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let JE : Module β E →L[ℂ] Module β E :=
    (moduleGrading β δB hβ J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let KF : Module β F →L[ℂ] Module β F :=
    (moduleGrading β δB hβ K).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let G : (ReducedCrossedProduct β)ᵐᵒᵖ → (ReducedCrossedProduct β)ᵐᵒᵖ := fun c =>
    MulOpposite.op ((reducedCrossedProductGrading β δB hβ).automorphism (MulOpposite.unop c))
  have h : L.comp JE = KF.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B) (C := ReducedCrossedProduct β) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (φ := coefficientRepresentation β) (P := Module β F)
      (f := L.comp JE) (g := KF.comp L)
    intro x c
    have hJE : JE (mk β E x c) = mk β E (J.grading x) (G c) :=
      moduleGrading_mk β δB hβ J x c
    have hL (y : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
        L (mk β E y d) = mk β F (u y) d := moduleEquiv_mk β u y d
    have hKF : KF (mk β F (u x) c) = mk β F (K.grading (u x)) (G c) :=
      moduleGrading_mk β δB hβ K (u x) c
    change L (JE (mk β E x c)) = KF (L (mk β E x c))
    calc
      L (JE (mk β E x c)) = L (mk β E (J.grading x) (G c)) :=
        congrArg (fun v : Module β E => L v) hJE
      _ = mk β F (u (J.grading x)) (G c) := hL (J.grading x) (G c)
      _ = mk β F (K.grading (u x)) (G c) :=
        congrArg (fun y : F => mk β F y (G c)) (hJK x)
      _ = KF (mk β F (u x) c) := hKF.symm
      _ = KF (L (mk β E x c)) :=
        congrArg (fun v : Module β F => KF v) (hL x c).symm
  exact DFunLike.congr_fun h z

variable (α : CStarAlgebraAction Γ A) {δA : CStarGrading A} {δB : CStarGrading B}
  [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- A genuine fully graded source cycle unitary descends to a whole-cycle unitary. -/
def gradedCycleIso {c : GradedKasparovCycle α β δA δB E}
    {d : GradedKasparovCycle α β δA δB F} (u : GradedKasparovCycleIso c d) :
    GradedKasparovCycleIso (gradedCycle β α c) (gradedCycle β α d) where
  moduleEquiv := moduleEquiv β u.moduleEquiv
  grading_intertwine := moduleEquiv_graded_grading β δB c.coefficientAction_preservesGrading
    u.moduleEquiv c.grading d.grading u.grading_intertwine
  action_intertwine _ _ := rfl
  representation_intertwine := moduleEquiv_reducedSourceRepresentation β α u.moduleEquiv
    c.groupAction d.groupAction c.representation d.representation
    c.representation_equivariant d.representation_equivariant
    u.action_intertwine u.representation_intertwine
  operator_intertwine := moduleEquiv_operator β u.moduleEquiv c.operator d.operator u.operator_intertwine

end BC4lean.KKTheory.KasparovDescent
