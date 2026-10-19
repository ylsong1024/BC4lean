import BC4lean.KasparovDescentIntervalCycle
import BC4lean.KasparovDescentCycleIso

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Whole-cycle endpoint unitaries for the actual interval descent

The construction imports the concrete ordinary reduced source
representation. Both comparison maps below use the actual whole
fibre tensor unitary and intertwine grading, source representation and
Fredholm operator on every completed vector.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

private theorem unitAction_apply_aux {D H : Type*}
    [NonUnitalCStarAlgebra D] [PartialOrder D]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Dᵐᵒᵖ H] [CStarModule Dᵐᵒᵖ H]
    (η : CStarAlgebraAction Unit D) (W : EquivariantHilbertModule η H)
    (g : Unit) (x : H) : W.action g x = x :=
  (congrArg (fun k : Unit => W.action k x) (Subsingleton.elim g (1 : Unit))).trans
    (W.one_apply x)

variable {Γ A B X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]

variable (β : CStarAlgebraAction Γ B) (M : Type*)
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

theorem intervalEvaluation_grading (t : X)
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (u : IntervalModule (X := X) β M) :
    intervalEvaluation β M t ((intervalModuleGrading β M J).grading u) =
      (ordinaryModuleGrading β (J.fibre t)).grading (intervalEvaluation β M t u) := by
  let ev : IntervalModule (X := X) β M →L[ℂ]
      Module β (HilbertModuleFibre B M t) := intervalEvaluation (X := X) β M t
  let JI : IntervalModule (X := X) β M →L[ℂ] IntervalModule (X := X) β M :=
    (intervalModuleGrading (X := X) β M J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let JT : Module β (HilbertModuleFibre B M t) →L[ℂ]
      Module β (HilbertModuleFibre B M t) :=
    (ordinaryModuleGrading β (J.fibre t)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let q : M →L[ℂ] HilbertModuleFibre B M t :=
    hilbertModuleFibreMk (B := B) (X := X) (M := M) t
  have h : ev.comp JI = JT.comp ev := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := C(X, B)) (C := C(X, ReducedCrossedProduct β))
      (E := M) (F := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))
      (φ := intervalCoefficientRepresentation (X := X) β)
      (P := Module β (HilbertModuleFibre B M t))
      (f := ev.comp JI) (g := JT.comp ev)
    intro x s
    have hsource : JI (intervalMk (X := X) β M x s) =
        intervalMk (X := X) β M (J.grading x) s :=
      intervalModuleGrading_mk (X := X) β M J x s
    have heval (y : M) : ev (intervalMk (X := X) β M y s) =
        mk β (HilbertModuleFibre B M t) (q y) (s t) :=
      GradedMatrixMoritaFibreTensor.evaluation_mk
        (B := B) (C := ReducedCrossedProduct β) (X := X)
        (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
        (coefficientRepresentation β) t y s
    have hfibre : (J.fibre t).grading (q x) = q (J.grading x) :=
      J.fibre_grading_mk (B := B) (X := X) (M := M) t x
    have htarget : JT (mk β (HilbertModuleFibre B M t) (q x) (s t)) =
        mk β (HilbertModuleFibre B M t) ((J.fibre t).grading (q x)) (s t) :=
      ordinaryModuleGrading_mk (E := HilbertModuleFibre B M t)
        β (J.fibre t) (q x) (s t)
    change ev (JI (intervalMk (X := X) β M x s)) =
      JT (ev (intervalMk (X := X) β M x s))
    calc
      ev (JI (intervalMk (X := X) β M x s)) =
          ev (intervalMk (X := X) β M (J.grading x) s) :=
        congrArg (fun v : IntervalModule (X := X) β M => ev v) hsource
      _ = mk β (HilbertModuleFibre B M t) (q (J.grading x)) (s t) :=
        heval (J.grading x)
      _ = mk β (HilbertModuleFibre B M t) ((J.fibre t).grading (q x)) (s t) :=
        congrArg
          (fun y : HilbertModuleFibre B M t => mk β (HilbertModuleFibre B M t) y (s t))
          hfibre.symm
      _ = JT (mk β (HilbertModuleFibre B M t) (q x) (s t)) := htarget.symm
      _ = JT (ev (intervalMk (X := X) β M x s)) :=
        congrArg (fun v : Module β (HilbertModuleFibre B M t) => JT v) (heval x).symm
  exact DFunLike.congr_fun h u

theorem intervalFibreEquiv_grading (t : X)
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (z : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :
    intervalFibreEquiv β M t (((intervalModuleGrading β M J).fibre t).grading z) =
      (ordinaryModuleGrading β (J.fibre t)).grading (intervalFibreEquiv β M t z) := by
  let q : IntervalModule (X := X) β M →L[ℂ]
      HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t :=
    hilbertModuleFibreMk (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t
  let e : HilbertModuleEquiv (ReducedCrossedProduct β)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t)
      (Module β (HilbertModuleFibre B M t)) := intervalFibreEquiv (X := X) β M t
  let ev : IntervalModule (X := X) β M →L[ℂ]
      Module β (HilbertModuleFibre B M t) := intervalEvaluation (X := X) β M t
  let GI : IntervalModule (X := X) β M →L[ℂ] IntervalModule (X := X) β M :=
    (intervalModuleGrading (X := X) β M J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let GQ : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t →L[ℂ]
      HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t :=
    ((intervalModuleGrading (X := X) β M J).fibre t).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let GT : Module β (HilbertModuleFibre B M t) →L[ℂ] Module β (HilbertModuleFibre B M t) :=
    (ordinaryModuleGrading β (J.fibre t)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have hsurj : Function.Surjective q :=
    hilbertModuleFibreMk_surjective (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t
  let u : IntervalModule (X := X) β M := Classical.choose (hsurj z)
  have hu : q u = z := Classical.choose_spec (hsurj z)
  have hq (v : IntervalModule (X := X) β M) : GQ (q v) = q (GI v) :=
    GradedHilbertModule.fibre_grading_mk
      (B := ReducedCrossedProduct β) (X := X) (M := IntervalModule (X := X) β M)
      (intervalModuleGrading (X := X) β M J) t v
  have he (v : IntervalModule (X := X) β M) : e (q v) = ev v :=
    GradedMatrixMoritaFibreTensor.hilbertEquiv_mk
      (B := B) (C := ReducedCrossedProduct β) (X := X)
      (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (coefficientRepresentation β) t v
  have hev : ev (GI u) = GT (ev u) :=
    intervalEvaluation_grading (X := X) β M t J u
  change e (GQ z) = GT (e z)
  calc
    e (GQ z) = e (GQ (q u)) :=
      congrArg (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) t => e (GQ w)) hu.symm
    _ = e (q (GI u)) :=
      congrArg (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) t => e w) (hq u)
    _ = ev (GI u) := he (GI u)
    _ = GT (ev u) := hev
    _ = GT (e (q u)) :=
      congrArg (fun w : Module β (HilbertModuleFibre B M t) => GT w) (he u).symm
    _ = GT (e z) :=
      congrArg (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) t => GT (e w)) hu

theorem intervalFibreEquiv_targetAction (t : X) (g : Unit)
    (z : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :
    intervalFibreEquiv β M t (((intervalTargetAction β M).fibre t).action g z) =
      (ordinaryTargetAction (E := HilbertModuleFibre B M t) β).action g
        (intervalFibreEquiv β M t z) := by
  exact (congrArg
    (fun w : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t =>
      intervalFibreEquiv (X := X) β M t w)
    (unitAction_apply_aux
      (D := ReducedCrossedProduct β)
      (H := HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      ((intervalTargetAction (X := X) β M).fibre t) g z)).trans
    (unitAction_apply_aux
      (D := ReducedCrossedProduct β) (H := Module β (HilbertModuleFibre B M t))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (ordinaryTargetAction (E := HilbertModuleFibre B M t) β) g
      (intervalFibreEquiv (X := X) β M t z)).symm

variable (α : CStarAlgebraAction Γ A)
  [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- Every evaluated even interval cycle is unitarily the actual descent of
the corresponding original fibre cycle, including its completed source action. -/
def intervalEvenCycleFibreIso
    (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    KasparovCycleIso ((intervalEvenCycle β M α c).fibre t) (evenCycle β α (c.fibre t)) where
  moduleEquiv := intervalFibreEquiv β M t
  grading_intertwine := intervalFibreEquiv_grading β M t c.grading
  action_intertwine := intervalFibreEquiv_targetAction β M t
  representation_intertwine := intervalFibreEquiv_reducedSourceRepresentation β M α
    c.groupAction c.representation c.representation_equivariant t
  operator_intertwine := intervalFibreEquiv_operator β M t c.operator

/-- The whole odd cycle comparison uses the same genuine fibre unitary. -/
def intervalOddCycleFibreIso
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    OddKasparovCycleIso ((intervalOddCycle β M α c).fibre t) (oddCycle β α (c.fibre t)) where
  moduleEquiv := intervalFibreEquiv β M t
  action_intertwine := intervalFibreEquiv_targetAction β M t
  representation_intertwine := intervalFibreEquiv_reducedSourceRepresentation β M α
    c.groupAction c.representation c.representation_equivariant t
  operator_intertwine := intervalFibreEquiv_operator β M t c.operator

end BC4lean.KKTheory.KasparovDescent
