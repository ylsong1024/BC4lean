import BC4lean.KasparovDescentIntervalNorm
import BC4lean.ReducedCrossedRepresentationExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Concrete reduced source representation on arbitrary interval modules

This uses the concrete ordinary `reducedSourceRepresentation` through
`KasparovDescentIntervalNorm`.
The representation below is its proved fibrewise norm-bound extension on
the actual interval coefficient-extension module. No completed source action
or norm bound is supplied as an arbitrary hypothesis.
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

omit [T2Space X] in
/-- Shared name for the existing inferred additive dictionary. All five
values are captured before any of these names become local instances. -/
@[instance_reducible] private def intervalRepresentationSharedNormedAddCommGroup :
    NormedAddCommGroup (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
@[instance_reducible] private def intervalRepresentationSharedNormedSpace :
    NormedSpace ℂ (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
@[instance_reducible] private def intervalRepresentationSharedSMul :
    SMul C(X, ReducedCrossedProduct β)ᵐᵒᵖ
      (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
@[instance_reducible] private def intervalRepresentationSharedCStarModule :
    CStarModule C(X, ReducedCrossedProduct β)ᵐᵒᵖ
      (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
private theorem intervalRepresentationSharedCompleteSpace :
    CompleteSpace (IntervalModule (X := X) β M) := inferInstance

attribute [local instance] intervalRepresentationSharedNormedAddCommGroup
  intervalRepresentationSharedNormedSpace intervalRepresentationSharedSMul
  intervalRepresentationSharedCStarModule intervalRepresentationSharedCompleteSpace

variable (α : CStarAlgebraAction Γ A)
  (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
  (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))

/-- Completion of the actual finite interval action by its proved reduced bound. -/
def intervalReducedSourceRepresentation : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
    AdjointableMap C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
  extendReducedRepresentation α (intervalAlgebraicSourceOperatorHom β M α U π hπ)
    (intervalAlgebraicSourceOperatorHom_reducedNorm_le β M α U π hπ)

@[simp] private theorem intervalReducedSourceRepresentation_algebraic (f : AlgebraicCrossedProduct α) :
    intervalReducedSourceRepresentation β M α U π hπ (algebraicToReducedCrossed α f) =
      intervalAlgebraicSourceOperatorHom β M α U π hπ f :=
  extendReducedRepresentation_algebraic α _ _ f

@[simp] theorem intervalReducedSourceRepresentation_single (g : Γ) (a : A) :
    intervalReducedSourceRepresentation β M α U π hπ
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) =
      intervalSourceRepresentation β M π a * intervalGroupOperator β M U g := by
  exact (intervalReducedSourceRepresentation_algebraic (X := X) β M α U π hπ
    (AlgebraicCrossedProduct.single α g a)).trans
      (covariantAlgebraicRepresentation_single
        (Γ := Γ) (A := A) (C := C(X, ReducedCrossedProduct β))
        (H := IntervalModule (X := X) β M)
        (intervalGroupAction (X := X) β M U)
        (intervalSourceRepresentation (X := X) β M π) α
        (intervalSourceRepresentation_equivariant (X := X) β M α U π hπ) g a)

private theorem intervalEvaluation_reducedSourceRepresentation_finite_aux
    (t : X) (f : AlgebraicCrossedProduct α) (u : IntervalModule (X := X) β M) :
    intervalEvaluation (X := X) β M t
        (intervalReducedSourceRepresentation (X := X) β M α U π hπ
          (algebraicToReducedCrossed α f) u) =
      reducedSourceRepresentation β (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation (X := X) M π t)
        (fibreSourceRepresentation_equivariant (X := X) β M α U π hπ t)
        (algebraicToReducedCrossed α f) (intervalEvaluation (X := X) β M t u) := by
  have hΦ := intervalReducedSourceRepresentation_algebraic
    (Γ := Γ) (A := A) (B := B) (X := X) β M α U π hπ f
  have hΨ := reducedSourceRepresentation_algebraic
    (Γ := Γ) (A := A) (B := B) β (HilbertModuleFibre B M t) α (U.fibre t)
    (fibreSourceRepresentation (X := X) M π t)
    (fibreSourceRepresentation_equivariant (X := X) β M α U π hπ t) f
  exact
    (congrArg
      (fun T : AdjointableMap C(X, ReducedCrossedProduct β)
          (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) =>
        intervalEvaluation (X := X) β M t (T u)) hΦ).trans
      ((intervalEvaluation_algebraic (Γ := Γ) (A := A) (B := B) (X := X)
        β M α U π hπ t f u).trans
        (congrArg
          (fun T : AdjointableMap (ReducedCrossedProduct β)
              (Module β (HilbertModuleFibre B M t))
              (Module β (HilbertModuleFibre B M t)) =>
            T (intervalEvaluation (X := X) β M t u)) hΨ).symm)

private theorem intervalEvaluation_reducedSourceRepresentation_left_cont_aux
    (t : X) (u : IntervalModule (X := X) β M) :
    Continuous (fun w : ReducedCrossedProduct α =>
      intervalEvaluation (X := X) β M t
        (intervalReducedSourceRepresentation (X := X) β M α U π hπ w u)) := by
  let ev : IntervalModule (X := X) β M →L[ℂ]
      Module β (HilbertModuleFibre B M t) := intervalEvaluation (X := X) β M t
  let Φ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalReducedSourceRepresentation (X := X) β M α U π hπ
  let evalI : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) →L[ℂ]
      IntervalModule (X := X) β M :=
    (ContinuousLinearMap.apply ℂ (IntervalModule (X := X) β M) u).comp
      (AdjointableMap.toCLMContinuousLinearMap
        (B := C(X, ReducedCrossedProduct β))
        (E := IntervalModule (X := X) β M) (F := IntervalModule (X := X) β M))
  change Continuous (fun w : ReducedCrossedProduct α => ev (evalI (Φ w)))
  exact ev.continuous.comp (evalI.continuous.comp (map_continuous Φ))

private theorem intervalEvaluation_reducedSourceRepresentation_right_cont_aux
    (t : X) (u : IntervalModule (X := X) β M) :
    Continuous (fun w : ReducedCrossedProduct α =>
      reducedSourceRepresentation β (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation (X := X) M π t)
        (fibreSourceRepresentation_equivariant (X := X) β M α U π hπ t)
        w (intervalEvaluation (X := X) β M t u)) := by
  let ev : IntervalModule (X := X) β M →L[ℂ]
      Module β (HilbertModuleFibre B M t) := intervalEvaluation (X := X) β M t
  let Ψ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β)
        (Module β (HilbertModuleFibre B M t)) (Module β (HilbertModuleFibre B M t)) :=
    reducedSourceRepresentation (Γ := Γ) (A := A) (B := B) β
      (HilbertModuleFibre B M t) α (U.fibre t)
      (fibreSourceRepresentation (X := X) M π t)
      (fibreSourceRepresentation_equivariant (X := X) β M α U π hπ t)
  let evalF : AdjointableMap (ReducedCrossedProduct β)
      (Module β (HilbertModuleFibre B M t)) (Module β (HilbertModuleFibre B M t)) →L[ℂ]
      Module β (HilbertModuleFibre B M t) :=
    (ContinuousLinearMap.apply ℂ (Module β (HilbertModuleFibre B M t)) (ev u)).comp
      (AdjointableMap.toCLMContinuousLinearMap
        (B := ReducedCrossedProduct β)
        (E := Module β (HilbertModuleFibre B M t))
        (F := Module β (HilbertModuleFibre B M t)))
  change Continuous (fun w : ReducedCrossedProduct α => evalF (Ψ w))
  exact evalF.continuous.comp (map_continuous Ψ)

/-- Evaluation intertwines the actual completed source actions on every vector. -/
private theorem intervalEvaluation_reducedSourceRepresentation (t : X)
    (z : ReducedCrossedProduct α) (u : IntervalModule (X := X) β M) :
    intervalEvaluation β M t (intervalReducedSourceRepresentation β M α U π hπ z u) =
      reducedSourceRepresentation β (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation M π t) (fibreSourceRepresentation_equivariant β M α U π hπ t)
        z (intervalEvaluation β M t u) := by
  exact congrFun
    ((algebraicToReducedCrossed_denseRange α).equalizer
      (intervalEvaluation_reducedSourceRepresentation_left_cont_aux
        (Γ := Γ) (A := A) (B := B) (X := X) β M α U π hπ t u)
      (intervalEvaluation_reducedSourceRepresentation_right_cont_aux
        (Γ := Γ) (A := A) (B := B) (X := X) β M α U π hπ t u)
      (funext fun f => intervalEvaluation_reducedSourceRepresentation_finite_aux
        (Γ := Γ) (A := A) (B := B) (X := X) β M α U π hπ t f u)) z

/-- The genuine whole-fibre tensor unitary intertwines the completed source action. -/
theorem intervalFibreEquiv_reducedSourceRepresentation (t : X)
    (z : ReducedCrossedProduct α)
    (u : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :
    intervalFibreEquiv β M t
        (hilbertModuleFibreOperator t (intervalReducedSourceRepresentation β M α U π hπ z) u) =
      reducedSourceRepresentation β (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation M π t) (fibreSourceRepresentation_equivariant β M α U π hπ t)
        z (intervalFibreEquiv β M t u) := by
  let q : IntervalModule (X := X) β M →L[ℂ]
      HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t :=
    hilbertModuleFibreMk
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t
  let e : HilbertModuleEquiv (ReducedCrossedProduct β)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t)
      (Module β (HilbertModuleFibre B M t)) :=
    intervalFibreEquiv (X := X) β M t
  let ev : IntervalModule (X := X) β M →L[ℂ]
      Module β (HilbertModuleFibre B M t) :=
    intervalEvaluation (X := X) β M t
  let L : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalReducedSourceRepresentation (X := X) β M α U π hπ z
  let Lt : AdjointableMap (ReducedCrossedProduct β)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :=
    hilbertModuleFibreOperator
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t L
  let R : AdjointableMap (ReducedCrossedProduct β)
      (Module β (HilbertModuleFibre B M t))
      (Module β (HilbertModuleFibre B M t)) :=
    reducedSourceRepresentation β (HilbertModuleFibre B M t) α (U.fibre t)
      (fibreSourceRepresentation (X := X) M π t)
      (fibreSourceRepresentation_equivariant (X := X) β M α U π hπ t) z
  have hsurj : Function.Surjective q :=
    hilbertModuleFibreMk_surjective
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t
  let v : IntervalModule (X := X) β M := Classical.choose (hsurj u)
  have hu : q v = u := Classical.choose_spec (hsurj u)
  have hop : Lt (q v) = q (L v) :=
    hilbertModuleFibreOperator_mk
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t L v
  have he (v : IntervalModule (X := X) β M) : e (q v) = ev v :=
    GradedMatrixMoritaFibreTensor.hilbertEquiv_mk
      (B := B) (C := ReducedCrossedProduct β) (X := X)
      (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (coefficientRepresentation β) t v
  have hev : ev (L v) = R (ev v) :=
    intervalEvaluation_reducedSourceRepresentation (X := X) β M α U π hπ t z v
  change e (Lt u) = R (e u)
  calc
    e (Lt u) = e (Lt (q v)) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e (Lt w)) hu.symm
    _ = e (q (L v)) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e w) hop
    _ = ev (L v) := he (L v)
    _ = R (ev v) := hev
    _ = R (e (q v)) :=
      congrArg (fun w : Module β (HilbertModuleFibre B M t) => R w) (he v).symm
    _ = R (e u) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => R (e w)) hu



end BC4lean.KKTheory.KasparovDescent
