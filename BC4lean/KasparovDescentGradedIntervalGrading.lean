import BC4lean.KasparovDescentGradedCycle
import BC4lean.KasparovDescentIntervalCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The genuine grading on the direct interval descent module

The construction imports the concrete reduced source representations and
their norm proofs.

The arbitrary original interval module retains its semilinear coefficient
grading. Its actual completed tensor with continuous crossed coefficients
uses the pointwise crossed standard grading. The actual left regular action
commutes with this grading, and the finite integrated source action respects
the original source grading. Actual reduced-norm density extends that law
to the completed source crossed product. The existing whole-fibre tensor
unitary intertwines the resulting genuine fibre gradings.

No crossed representation, descended cycle, or homotopy witness is supplied
as an assumption. The original actions' grading-preservation hypotheses are
explicit; no reflection from sections over a possibly empty space is used.
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
/-- The actual section left action respects the original and crossed gradings. -/
theorem gradedIntervalCoefficientRepresentation_graded
    (δB : CStarGrading B) (hβ : β.PreservesGrading δB) :
    ModuleTensorRepresentationGraded (δB := δB.continuousSections (X := X))
      (intervalCoefficientRepresentation (X := X) β)
      ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X)) :=
  GradedMatrixMoritaSectionRepresentation.leftAction_graded
    (coefficientRepresentation β) (crossedStandardGrading β δB hβ)
    (coefficientRepresentation_graded β δB hβ)

/-- The actual direct interval module has the tensor of the two genuine
semilinear gradings, including the grading of crossed coefficients. -/
def gradedIntervalModuleGrading (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M) :
    GradedHilbertModule
      ((reducedCrossedProductGrading β δB hβ).continuousSections (X := X))
      (IntervalModule (X := X) β M) :=
  J.interiorTensor (φ := intervalCoefficientRepresentation (X := X) β)
    ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X))
    (gradedIntervalCoefficientRepresentation_graded (X := X) β δB hβ)

omit [T2Space X] in
/-- The tensor grading acts on both factors of every actual elementary vector. -/
@[simp] theorem gradedIntervalModuleGrading_mk (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    (x : M) (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
    (gradedIntervalModuleGrading β M δB hβ J).grading (intervalMk β M x s) =
      intervalMk β M (J.grading x)
        (((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X)).grading s) :=
  J.interiorTensor_grading_mk (φ := intervalCoefficientRepresentation (X := X) β)
    ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X))
    (gradedIntervalCoefficientRepresentation_graded (X := X) β δB hβ) x s

omit [T2Space X] in
/-- The second-factor grading is the actual pointwise crossed grading. -/
@[simp] theorem gradedIntervalCrossedSectionGrading_apply (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB)
    (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) (t : X) :
    (((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X)).grading s) t =
      MulOpposite.op ((reducedCrossedProductGrading β δB hβ).automorphism
        (MulOpposite.unop (s t))) := rfl

omit [T2Space X] in
/-- Oddness, with its actual minus sign, survives the completed interval tensor. -/
theorem intervalOperatorHom_graded_odd (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    {T : AdjointableMap C(X, B) M M} (hT : J.IsOdd J T) :
    (gradedIntervalModuleGrading β M δB hβ J).IsOdd
      (gradedIntervalModuleGrading β M δB hβ J) (intervalOperatorHom β M T) :=
  hT.interiorModuleTensorOperator (φ := intervalCoefficientRepresentation (X := X) β)
    ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X))
    (gradedIntervalCoefficientRepresentation_graded (X := X) β δB hβ)

omit [T2Space X] in
/-- Evenness is preserved by the same actual first-factor operator homomorphism. -/
theorem intervalOperatorHom_graded_even (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    {T : AdjointableMap C(X, B) M M} (hT : J.IsEven J T) :
    (gradedIntervalModuleGrading β M δB hβ J).IsEven
      (gradedIntervalModuleGrading β M δB hβ J) (intervalOperatorHom β M T) :=
  hT.interiorModuleTensorOperator (φ := intervalCoefficientRepresentation (X := X) β)
    ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X))
    (gradedIntervalCoefficientRepresentation_graded (X := X) β δB hβ)

omit [T2Space X] in
/-- The genuine pointwise left regular action preserves the crossed section grading. -/
theorem intervalLeftRegularAction_preserves_gradedCrossedSections
    (δB : CStarGrading B) (hβ : β.PreservesGrading δB) :
    (intervalLeftRegularAction (X := X) β).PreservesGrading
      ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X)) := by
  intro g s
  ext t
  exact leftRegularAction_preserves_crossedGrading β δB hβ g (s t)

omit [T2Space X] in
/-- The actual integrated group operator is even for the genuine tensor grading. -/
theorem intervalGroupOperator_graded_even (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (hU : U.PreservesGrading J) (g : Γ) :
    (gradedIntervalModuleGrading β M δB hβ J).IsEven
      (gradedIntervalModuleGrading β M δB hβ J) (intervalGroupOperator β M U g) := by
  have h := U.interiorTensor_preservesGrading (φ := intervalCoefficientRepresentation (X := X) β) (intervalLeftRegularAction β) J
    ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X)) hU
    (intervalLeftRegularAction_preserves_gradedCrossedSections (X := X) β δB hβ)
    (intervalCoefficientRepresentation_equivariant β)
    (gradedIntervalCoefficientRepresentation_graded (X := X) β δB hβ)
  intro u
  exact (h g u).symm

omit [PartialOrder A] [StarOrderedRing A] [T2Space X] in
/-- The actual coefficient source action retains the original source grading law. -/
theorem intervalSourceRepresentation_graded_tensor
    (δA : CStarGrading A) (δB : CStarGrading B) (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπJ : ∀ a x, J.grading (π a x) = π (δA.automorphism a) (J.grading x))
    (a : A) (u : IntervalModule (X := X) β M) :
    (gradedIntervalModuleGrading β M δB hβ J).grading
        (intervalSourceRepresentation β M π a u) =
      intervalSourceRepresentation β M π (δA.automorphism a)
        ((gradedIntervalModuleGrading β M δB hβ J).grading u) := by
  let K : IntervalModule (X := X) β M →L[ℂ] IntervalModule (X := X) β M :=
    (gradedIntervalModuleGrading (X := X) β M δB hβ J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let L : IntervalModule (X := X) β M →L[ℂ] IntervalModule (X := X) β M :=
    (intervalSourceRepresentation (X := X) β M π a).toCLM
  let R : IntervalModule (X := X) β M →L[ℂ] IntervalModule (X := X) β M :=
    (intervalSourceRepresentation (X := X) β M π (δA.automorphism a)).toCLM
  let G : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ) →L[ℂ]
      C(X, (ReducedCrossedProduct β)ᵐᵒᵖ) :=
    ((crossedStandardGrading β δB hβ).gradedContinuousSections (X := X)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : K.comp L = R.comp K := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := C(X, B)) (C := C(X, ReducedCrossedProduct β))
      (E := M) (F := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))
      (φ := intervalCoefficientRepresentation (X := X) β)
      (P := IntervalModule (X := X) β M)
      (f := K.comp L) (g := R.comp K)
    intro x s
    have hL (y : M) (r : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
        L (intervalMk (X := X) β M y r) = intervalMk (X := X) β M (π a y) r :=
      interiorModuleTensorOperator_mk (intervalCoefficientRepresentation (X := X) β) (π a) y r
    have hR (y : M) (r : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
        R (intervalMk (X := X) β M y r) =
          intervalMk (X := X) β M (π (δA.automorphism a) y) r :=
      interiorModuleTensorOperator_mk
        (intervalCoefficientRepresentation (X := X) β) (π (δA.automorphism a)) y r
    have hK (y : M) (r : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
        K (intervalMk (X := X) β M y r) =
          intervalMk (X := X) β M (J.grading y) (G r) :=
      gradedIntervalModuleGrading_mk (X := X) β M δB hβ J y r
    change K (L (intervalMk (X := X) β M x s)) =
      R (K (intervalMk (X := X) β M x s))
    calc
      K (L (intervalMk (X := X) β M x s)) =
          K (intervalMk (X := X) β M (π a x) s) :=
        congrArg (fun v : IntervalModule (X := X) β M => K v) (hL x s)
      _ = intervalMk (X := X) β M (J.grading (π a x)) (G s) := hK (π a x) s
      _ = intervalMk (X := X) β M (π (δA.automorphism a) (J.grading x)) (G s) :=
        congrArg (fun y : M => intervalMk (X := X) β M y (G s)) (hπJ a x)
      _ = R (intervalMk (X := X) β M (J.grading x) (G s)) := (hR (J.grading x) (G s)).symm
      _ = R (K (intervalMk (X := X) β M x s)) :=
        congrArg (fun v : IntervalModule (X := X) β M => R v) (hK x s).symm
  exact DFunLike.congr_fun h u

omit [PartialOrder A] [StarOrderedRing A] [T2Space X] in
/-- Each actual covariant crossed generator has the original graded source law. -/
theorem intervalSourceGenerator_graded
    (δA : CStarGrading A) (δB : CStarGrading B) (hβ : β.PreservesGrading δB)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    (hU : U.PreservesGrading J)
    (hπJ : ∀ a x, J.grading (π a x) = π (δA.automorphism a) (J.grading x))
    (a : A) (g : Γ) (u : IntervalModule (X := X) β M) :
    (gradedIntervalModuleGrading β M δB hβ J).grading
        ((intervalSourceRepresentation β M π a * intervalGroupOperator β M U g) u) =
      (intervalSourceRepresentation β M π (δA.automorphism a) *
        intervalGroupOperator β M U g)
          ((gradedIntervalModuleGrading β M δB hβ J).grading u) := by
  let V : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalGroupOperator (X := X) β M U g
  let P : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalSourceRepresentation (X := X) β M π (δA.automorphism a)
  have hs := intervalSourceRepresentation_graded_tensor
    (Γ := Γ) (A := A) (B := B) (X := X) β M δA δB hβ J π hπJ a (V u)
  have hv := intervalGroupOperator_graded_even
    (Γ := Γ) (B := B) (X := X) β M δB hβ J U hU g u
  exact hs.trans (congrArg (fun v : IntervalModule (X := X) β M => P v) hv)

variable (α : CStarAlgebraAction Γ A)

/-- Actual finite integration and reduced-norm density give the graded law
for every completed source crossed-product element. -/
theorem intervalReducedSourceRepresentation_graded
    (δA : CStarGrading A) (δB : CStarGrading B)
    (hα : α.PreservesGrading δA) (hβ : β.PreservesGrading δB)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    (hU : U.PreservesGrading J)
    (hπJ : ∀ a x, J.grading (π a x) = π (δA.automorphism a) (J.grading x))
    (z : ReducedCrossedProduct α) (u : IntervalModule (X := X) β M) :
    (gradedIntervalModuleGrading β M δB hβ J).grading
        (intervalReducedSourceRepresentation β M α U π hπ z u) =
      intervalReducedSourceRepresentation β M α U π hπ
        ((reducedCrossedProductGrading α δA hα).automorphism z)
        ((gradedIntervalModuleGrading β M δB hβ J).grading u) := by
  let ρ := intervalReducedSourceRepresentation β M α U π hπ
  let JT := gradedIntervalModuleGrading β M δB hβ J
  let σ := (reducedCrossedProductGrading α δA hα).automorphism
  have heval (v : IntervalModule (X := X) β M) :
      Continuous (fun w : ReducedCrossedProduct α => ρ w v) :=
    (AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρ)).clm_apply continuous_const
  change JT.grading (ρ z u) = ρ (σ z) (JT.grading u)
  refine (algebraicToReducedCrossed_denseRange α).induction_on z
    (isClosed_eq (JT.grading.continuous.comp (heval u))
      ((heval (JT.grading u)).comp (NonUnitalStarAlgHom.isometry σ σ.injective).continuous)) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp only [map_zero, AdjointableMap.coe_zero_apply]
  | single g a =>
    simp only [ρ, σ, intervalReducedSourceRepresentation_single, crossedGrading_single]
    exact intervalSourceGenerator_graded β M δA δB hβ U π J hU hπJ a g u
  | add f h ihf ihh =>
    simpa only [map_add, AdjointableMap.coe_add_apply] using congrArg₂ (· + ·) ihf ihh

/-- The genuine whole-fibre tensor unitary intertwines the actual evaluated
interval grading with the ordinary descended fibre grading. -/
theorem intervalFibreEquiv_gradedGrading (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB) (t : X)
    (J : GradedHilbertModule (δB.continuousSections (X := X)) M)
    (z : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :
    intervalFibreEquiv (X := X) β M t
        (((gradedIntervalModuleGrading (X := X) β M δB hβ J).gradedFibre (X := X) t).grading z) =
      (moduleGrading β δB hβ (J.gradedFibre (X := X) t)).grading
        (intervalFibreEquiv (X := X) β M t z) := by
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
  let L : IntervalModule (X := X) β M → IntervalModule (X := X) β M :=
    (gradedIntervalModuleGrading (X := X) β M δB hβ J).grading
  let Lt :
      HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t →
      HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t :=
    ((gradedIntervalModuleGrading (X := X) β M δB hβ J).gradedFibre (X := X) t).grading
  let R : Module β (HilbertModuleFibre B M t) → Module β (HilbertModuleFibre B M t) :=
    (moduleGrading β δB hβ (J.gradedFibre (X := X) t)).grading
  have hsurj : Function.Surjective q :=
    hilbertModuleFibreMk_surjective
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t
  let u : IntervalModule (X := X) β M := Classical.choose (hsurj z)
  have hu : q u = z := Classical.choose_spec (hsurj z)
  have hop : Lt (q u) = q (L u) :=
    GradedHilbertModule.gradedFibre_grading_mk
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M)
      (δ := reducedCrossedProductGrading β δB hβ)
      (gradedIntervalModuleGrading (X := X) β M δB hβ J) t u
  have he (v : IntervalModule (X := X) β M) : e (q v) = ev v :=
    GradedMatrixMoritaFibreTensor.hilbertEquiv_mk
      (B := B) (C := ReducedCrossedProduct β) (X := X) (E := M)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (coefficientRepresentation β) t v
  have hev : ev (L u) = R (ev u) :=
    GradedMatrixMoritaFibreTensor.evaluation_grading
      (B := B) (C := ReducedCrossedProduct β) (X := X) (E := M)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (δB := δB) (δC := reducedCrossedProductGrading β δB hβ)
      (coefficientRepresentation β) t J (crossedStandardGrading β δB hβ)
      (coefficientRepresentation_graded β δB hβ) u
  have h : e (Lt z) = R (e z) := by
    calc
      e (Lt z) = e (Lt (q u)) :=
        congrArg
          (fun v : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e (Lt v)) hu.symm
      _ = e (q (L u)) :=
        congrArg
          (fun v : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e v) hop
      _ = ev (L u) := he (L u)
      _ = R (ev u) := hev
      _ = R (e (q u)) :=
        congrArg (fun v : Module β (HilbertModuleFibre B M t) => R v) (he u).symm
      _ = R (e z) :=
        congrArg
          (fun v : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => R (e v)) hu
  exact h

end BC4lean.KKTheory.KasparovDescent
