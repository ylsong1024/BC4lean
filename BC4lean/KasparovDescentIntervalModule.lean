import BC4lean.KasparovDescentAlgebraicRepresentation
import BC4lean.CovariantAlgebraicRepresentation
import BC4lean.GradedMatrixMoritaFibreTensorCompatibility

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Direct interval coefficient extension for reduced descent

The original interval module may be arbitrary. Its second tensor factor is
the actual continuous-section module C(X,(B crossed_r Gamma)^op), acted on
pointwise by the genuine left regular multiplier. The completed module,
balanced group action, finite integrated source action and genuine evaluated
fibre intertwinings are constructed directly. No crossed path-algebra
isomorphism and no arbitrary completed crossed representation is an input.

-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped InnerProductSpace KasparovDescent

variable {Γ A B X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]

variable (β : CStarAlgebraAction Γ B)

def intervalCoefficientRepresentation :
    C(X, B) →⋆ₙₐ[ℂ] AdjointableMap C(X, ReducedCrossedProduct β)
      C(X, (ReducedCrossedProduct β)ᵐᵒᵖ) C(X, (ReducedCrossedProduct β)ᵐᵒᵖ) :=
  GradedMatrixMoritaSectionRepresentation.leftAction (coefficientRepresentation β)

omit [T2Space X] in
@[simp] theorem intervalCoefficientRepresentation_apply (b : C(X, B))
    (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) (t : X) :
    intervalCoefficientRepresentation (X := X) β b s t = coefficientRepresentation β (b t) (s t) := rfl

/-- The actual pointwise lambda action, packaged over the trivial right
action on the continuous crossed-coefficient algebra. -/
def intervalLeftRegularAction :
    EquivariantHilbertModule
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ C(X, ReducedCrossedProduct β))
      C(X, (ReducedCrossedProduct β)ᵐᵒᵖ) where
  action := ((leftRegularAction β).continuousSections (X := X)).action
  inner_action g s r := by
    have h := ((leftRegularAction β).continuousSections (X := X)).inner_action g s r
    change ⟪_, _⟫_(C(X, ReducedCrossedProduct β)ᵐᵒᵖ) =
      ⟪s, r⟫_(C(X, ReducedCrossedProduct β)ᵐᵒᵖ) at h ⊢
    exact h

omit [T2Space X] in
@[simp] theorem intervalLeftRegularAction_apply (g : Γ)
    (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) (t : X) :
    (intervalLeftRegularAction (X := X) β).action g s t =
      MulOpposite.op (leftRegular β g (MulOpposite.unop (s t))) := rfl

omit [T2Space X] in
theorem intervalCoefficientRepresentation_equivariant :
    ModuleTensorRepresentationEquivariant (intervalCoefficientRepresentation (X := X) β)
      (β.continuousSections (X := X)) (intervalLeftRegularAction (X := X) β) := by
  intro g b s
  ext t
  exact coefficientRepresentation_equivariant β g (b t) (s t)

variable (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- The direct completed extension of the actual arbitrary interval module. -/
abbrev IntervalModule := InteriorModuleTensor (E := M) (intervalCoefficientRepresentation (X := X) β)

omit [T2Space X] in
/-- Shared name for the existing inferred additive dictionary. All five
values are captured before any of these names become local instances. -/
@[instance_reducible] private def intervalModuleSharedNormedAddCommGroup :
    NormedAddCommGroup (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
@[instance_reducible] private def intervalModuleSharedNormedSpace :
    NormedSpace ℂ (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
@[instance_reducible] private def intervalModuleSharedSMul :
    SMul C(X, ReducedCrossedProduct β)ᵐᵒᵖ
      (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
@[instance_reducible] private def intervalModuleSharedCStarModule :
    CStarModule C(X, ReducedCrossedProduct β)ᵐᵒᵖ
      (IntervalModule (X := X) β M) := inferInstance

omit [T2Space X] in
private theorem intervalModuleSharedCompleteSpace :
    CompleteSpace (IntervalModule (X := X) β M) := inferInstance

attribute [local instance] intervalModuleSharedNormedAddCommGroup
  intervalModuleSharedNormedSpace intervalModuleSharedSMul
  intervalModuleSharedCStarModule intervalModuleSharedCompleteSpace

def intervalMk (x : M) (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) : IntervalModule (X := X) β M :=
  interiorModuleTensorMk (intervalCoefficientRepresentation (X := X) β) x s

def intervalOperatorHom : AdjointableMap C(X, B) M M →⋆ₐ[ℂ]
    AdjointableMap C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
  interiorModuleTensorOperatorHom (E := M) (intervalCoefficientRepresentation (X := X) β)

def intervalGroupAction (U : EquivariantHilbertModule (β.continuousSections (X := X)) M) :
    EquivariantHilbertModule
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ C(X, ReducedCrossedProduct β))
      (IntervalModule (X := X) β M) :=
  U.interiorTensor (intervalLeftRegularAction (X := X) β) (intervalCoefficientRepresentation_equivariant (X := X) β)

def intervalGroupOperator (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (g : Γ) :
    AdjointableMap C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
  (intervalGroupAction (X := X) β M U).trivialActionOperator g

omit [T2Space X] in
@[simp] theorem intervalGroupOperator_mk
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (g : Γ) (x : M) (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
    intervalGroupOperator (X := X) β M U g (intervalMk (X := X) β M x s) =
      intervalMk (X := X) β M (U.action g x) ((intervalLeftRegularAction (X := X) β).action g s) :=
  U.interiorTensor_action_mk (intervalLeftRegularAction (X := X) β)
    (intervalCoefficientRepresentation_equivariant (X := X) β) g x s

omit [T2Space X] in
theorem intervalGroupAction_conjugateOperator
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (g : Γ) (T : AdjointableMap C(X, B) M M) :
    (intervalGroupAction (X := X) β M U).conjugateOperator g (intervalOperatorHom (X := X) β M T) =
      intervalOperatorHom (X := X) β M (U.conjugateOperator g T) :=
  U.interiorTensor_conjugateOperator (intervalLeftRegularAction (X := X) β)
    (intervalCoefficientRepresentation_equivariant (X := X) β) g T

def intervalSourceRepresentation (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M) :
    A →⋆ₙₐ[ℂ]
      AdjointableMap C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
  (intervalOperatorHom (X := X) β M).toNonUnitalStarAlgHom.comp π

omit [T2Space X] in
theorem intervalSourceRepresentation_equivariant (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a)) (g : Γ) (a : A) :
    (intervalGroupAction (X := X) β M U).conjugateOperator g (intervalSourceRepresentation (X := X) β M π a) =
      intervalSourceRepresentation (X := X) β M π (α.automorphism g a) := by
  change (intervalGroupAction (X := X) β M U).conjugateOperator g
      (intervalOperatorHom (X := X) β M (π a)) =
    intervalOperatorHom (X := X) β M (π (α.automorphism g a))
  exact (intervalGroupAction_conjugateOperator (X := X) β M U g (π a)).trans
    (congrArg (fun T : AdjointableMap C(X, B) M M =>
      intervalOperatorHom (X := X) β M T) (hπ g a))

/-- Actual finite source integration globally on the interval extension. -/
def intervalAlgebraicSourceOperatorHom (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a)) :
    AlgebraicCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
  covariantAlgebraicRepresentation (intervalGroupAction (X := X) β M U)
    (intervalSourceRepresentation (X := X) β M π) α (intervalSourceRepresentation_equivariant β M α U π hπ)

def intervalEvaluation (t : X) :
    IntervalModule (X := X) β M →L[ℂ] Module β (HilbertModuleFibre B M t) :=
  GradedMatrixMoritaFibreTensor.evaluation (B := B) (C := ReducedCrossedProduct β) (X := X)
    (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (coefficientRepresentation β) t

/-- The existing general whole-fibre tensor unitary, specialized to the
actual crossed coefficient inclusion. -/
def intervalFibreEquiv (t : X) :
    HilbertModuleEquiv (ReducedCrossedProduct β)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t)
      (Module β (HilbertModuleFibre B M t)) :=
  GradedMatrixMoritaFibreTensor.hilbertEquiv (B := B) (C := ReducedCrossedProduct β) (X := X)
    (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (coefficientRepresentation β) t

private theorem intervalEvaluation_operator (t : X) (T : AdjointableMap C(X, B) M M)
    (u : IntervalModule (X := X) β M) :
    intervalEvaluation (X := X) β M t (intervalOperatorHom (X := X) β M T u) =
      operatorHom β (HilbertModuleFibre B M t) (hilbertModuleFibreOperator t T)
        (intervalEvaluation (X := X) β M t u) :=
  GradedMatrixMoritaFibreTensor.evaluation_operator (B := B) (C := ReducedCrossedProduct β) (X := X)
    (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
    (coefficientRepresentation β) t T u

theorem intervalFibreEquiv_operator (t : X) (T : AdjointableMap C(X, B) M M)
    (z : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :
    intervalFibreEquiv (X := X) β M t (hilbertModuleFibreOperator t (intervalOperatorHom (X := X) β M T) z) =
      operatorHom β (HilbertModuleFibre B M t) (hilbertModuleFibreOperator t T)
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
  let L : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalOperatorHom (X := X) β M T
  let Lt : AdjointableMap (ReducedCrossedProduct β)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :=
    hilbertModuleFibreOperator
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t L
  let R : AdjointableMap (ReducedCrossedProduct β)
      (Module β (HilbertModuleFibre B M t))
      (Module β (HilbertModuleFibre B M t)) :=
    operatorHom β (HilbertModuleFibre B M t) (hilbertModuleFibreOperator t T)
  have hsurj : Function.Surjective q :=
    hilbertModuleFibreMk_surjective
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t
  let u : IntervalModule (X := X) β M := Classical.choose (hsurj z)
  have hu : q u = z := Classical.choose_spec (hsurj z)
  have hop : Lt (q u) = q (L u) :=
    hilbertModuleFibreOperator_mk
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t L u
  have he (v : IntervalModule (X := X) β M) : e (q v) = ev v :=
    GradedMatrixMoritaFibreTensor.hilbertEquiv_mk
      (B := B) (C := ReducedCrossedProduct β) (X := X)
      (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (coefficientRepresentation β) t v
  have hev : ev (L u) = R (ev u) :=
    intervalEvaluation_operator (X := X) β M t T u
  change e (Lt z) = R (e z)
  calc
    e (Lt z) = e (Lt (q u)) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e (Lt w)) hu.symm
    _ = e (q (L u)) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e w) hop
    _ = ev (L u) := he (L u)
    _ = R (ev u) := hev
    _ = R (e (q u)) :=
      congrArg (fun w : Module β (HilbertModuleFibre B M t) => R w) (he u).symm
    _ = R (e z) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => R (e w)) hu


private theorem intervalEvaluation_mk_aux
    (t : X) (x : M) (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
    intervalEvaluation (X := X) β M t (intervalMk (X := X) β M x s) =
      mk β (HilbertModuleFibre B M t)
        (hilbertModuleFibreMk (B := B) (X := X) (M := M) t x) (s t) :=
  GradedMatrixMoritaFibreTensor.evaluation_mk
    (B := B) (C := ReducedCrossedProduct β) (X := X)
    (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
    (coefficientRepresentation β) t x s

private theorem intervalEvaluation_groupOperator_mk_aux
    (t : X)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (g : Γ) (x : M) (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
    intervalEvaluation (X := X) β M t
        (intervalGroupOperator (X := X) β M U g
          (intervalMk (X := X) β M x s)) =
      groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g
        (intervalEvaluation (X := X) β M t (intervalMk (X := X) β M x s)) := by
  let ev : IntervalModule (X := X) β M →L[ℂ]
      Module β (HilbertModuleFibre B M t) :=
    intervalEvaluation (X := X) β M t
  let L : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalGroupOperator (X := X) β M U g
  let R : AdjointableMap (ReducedCrossedProduct β)
      (Module β (HilbertModuleFibre B M t))
      (Module β (HilbertModuleFibre B M t)) :=
    groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g
  have hL (x : M) (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
      L (intervalMk (X := X) β M x s) =
        intervalMk (X := X) β M (U.action g x)
          ((intervalLeftRegularAction (X := X) β).action g s) :=
    intervalGroupOperator_mk (X := X) β M U g x s
  have hR (x : HilbertModuleFibre B M t) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      R (mk β (HilbertModuleFibre B M t) x c) =
        mk β (HilbertModuleFibre B M t) ((U.fibre t).action g x)
          (MulOpposite.op (leftRegular β g (MulOpposite.unop c))) :=
    groupOperator_mk (Γ := Γ) (B := B)
      β (HilbertModuleFibre B M t) (U.fibre t) g x c
  have hU (x : M) :
      (U.fibre t).action g
          (hilbertModuleFibreMk (B := B) (X := X) (M := M) t x) =
        hilbertModuleFibreMk (B := B) (X := X) (M := M) t (U.action g x) :=
    EquivariantHilbertModule.fibre_action_mk
      (Γ := Γ) (B := B) (X := X) (M := M) (β := β) U t g x
  have hs (s : C(X, (ReducedCrossedProduct β)ᵐᵒᵖ)) :
      ((intervalLeftRegularAction (X := X) β).action g s) t =
        MulOpposite.op (leftRegular β g (MulOpposite.unop (s t))) :=
    intervalLeftRegularAction_apply (X := X) β g s t
  calc
    ev (L (intervalMk (X := X) β M x s)) =
        ev (intervalMk (X := X) β M (U.action g x)
          ((intervalLeftRegularAction (X := X) β).action g s)) :=
      congrArg (fun w : IntervalModule (X := X) β M => ev w) (hL x s)
    _ = mk β (HilbertModuleFibre B M t)
        (hilbertModuleFibreMk (B := B) (X := X) (M := M) t (U.action g x))
        (((intervalLeftRegularAction (X := X) β).action g s) t) :=
      intervalEvaluation_mk_aux (Γ := Γ) (B := B) (X := X) β M t (U.action g x) ((intervalLeftRegularAction (X := X) β).action g s)
    _ = mk β (HilbertModuleFibre B M t)
        ((U.fibre t).action g
          (hilbertModuleFibreMk (B := B) (X := X) (M := M) t x))
        (MulOpposite.op (leftRegular β g (MulOpposite.unop (s t)))) :=
      congrArg₂
        (fun (w : HilbertModuleFibre B M t) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) =>
          mk β (HilbertModuleFibre B M t) w c)
        (hU x).symm (hs s)
    _ = R (mk β (HilbertModuleFibre B M t)
        (hilbertModuleFibreMk (B := B) (X := X) (M := M) t x) (s t)) :=
      (hR (hilbertModuleFibreMk (B := B) (X := X) (M := M) t x) (s t)).symm
    _ = R (ev (intervalMk (X := X) β M x s)) :=
      congrArg
        (fun w : Module β (HilbertModuleFibre B M t) => R w) (intervalEvaluation_mk_aux (Γ := Γ) (B := B) (X := X) β M t x s).symm

private theorem intervalEvaluation_groupOperator_clm_aux
    (t : X)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (g : Γ) :
    (intervalEvaluation (X := X) β M t).comp
        (intervalGroupOperator (X := X) β M U g).toCLM =
      (groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g).toCLM.comp
        (intervalEvaluation (X := X) β M t) := by
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    (B := C(X, B)) (C := C(X, ReducedCrossedProduct β))
    (E := M) (F := C(X, (ReducedCrossedProduct β)ᵐᵒᵖ))
    (φ := intervalCoefficientRepresentation (X := X) β)
    (P := Module β (HilbertModuleFibre B M t))
  intro x s
  exact intervalEvaluation_groupOperator_mk_aux
    (Γ := Γ) (B := B) (X := X) β M t U g x s

private theorem intervalEvaluation_groupOperator (t : X)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M) (g : Γ)
    (u : IntervalModule (X := X) β M) :
    intervalEvaluation (X := X) β M t (intervalGroupOperator (X := X) β M U g u) =
      groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g (intervalEvaluation (X := X) β M t u) := by
  exact DFunLike.congr_fun
    (intervalEvaluation_groupOperator_clm_aux
      (Γ := Γ) (B := B) (X := X) β M t U g) u

private theorem intervalFibreEquiv_groupOperator (t : X)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M) (g : Γ)
    (z : HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :
    intervalFibreEquiv (X := X) β M t (hilbertModuleFibreOperator t (intervalGroupOperator (X := X) β M U g) z) =
      groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g (intervalFibreEquiv (X := X) β M t z) := by
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
    intervalGroupOperator (X := X) β M U g
  let Lt : AdjointableMap (ReducedCrossedProduct β)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t)
      (HilbertModuleFibre (ReducedCrossedProduct β) (IntervalModule (X := X) β M) t) :=
    hilbertModuleFibreOperator
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t L
  let R : AdjointableMap (ReducedCrossedProduct β)
      (Module β (HilbertModuleFibre B M t))
      (Module β (HilbertModuleFibre B M t)) :=
    groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g
  have hsurj : Function.Surjective q :=
    hilbertModuleFibreMk_surjective
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t
  let u : IntervalModule (X := X) β M := Classical.choose (hsurj z)
  have hu : q u = z := Classical.choose_spec (hsurj z)
  have hop : Lt (q u) = q (L u) :=
    hilbertModuleFibreOperator_mk
      (B := ReducedCrossedProduct β) (X := X)
      (M := IntervalModule (X := X) β M) t L u
  have he (v : IntervalModule (X := X) β M) : e (q v) = ev v :=
    GradedMatrixMoritaFibreTensor.hilbertEquiv_mk
      (B := B) (C := ReducedCrossedProduct β) (X := X)
      (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (coefficientRepresentation β) t v
  have hev : ev (L u) = R (ev u) :=
    intervalEvaluation_groupOperator (X := X) β M t U g u
  change e (Lt z) = R (e z)
  calc
    e (Lt z) = e (Lt (q u)) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e (Lt w)) hu.symm
    _ = e (q (L u)) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => e w) hop
    _ = ev (L u) := he (L u)
    _ = R (ev u) := hev
    _ = R (e (q u)) :=
      congrArg (fun w : Module β (HilbertModuleFibre B M t) => R w) (he u).symm
    _ = R (e z) :=
      congrArg
        (fun w : HilbertModuleFibre (ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) t => R (e w)) hu

def fibreSourceRepresentation (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M) (t : X) :
    A →⋆ₙₐ[ℂ] AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t) :=
  (hilbertModuleFibreOperatorHom t).toNonUnitalStarAlgHom.comp π

omit [T2Space X] in
theorem fibreSourceRepresentation_equivariant (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (t : X) (g : Γ) (a : A) :
    (U.fibre t).conjugateOperator g (fibreSourceRepresentation (X := X) M π t a) =
      fibreSourceRepresentation (X := X) M π t (α.automorphism g a) := by
  change (U.fibre t).conjugateOperator g (hilbertModuleFibreOperator t (π a)) = _
  rw [U.fibre_conjugateOperator]
  exact congrArg (hilbertModuleFibreOperator (B := B) t) (hπ g a)

theorem intervalEvaluation_algebraic (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (t : X) (f : AlgebraicCrossedProduct α) (u : IntervalModule (X := X) β M) :
    intervalEvaluation (X := X) β M t (intervalAlgebraicSourceOperatorHom (X := X) β M α U π hπ f u) =
      algebraicSourceOperatorHom β (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation (X := X) M π t) (fibreSourceRepresentation_equivariant β M α U π hπ t)
        f (intervalEvaluation (X := X) β M t u) := by
  let ε : IntervalModule (X := X) β M →L[ℂ]
      Module β (HilbertModuleFibre B M t) := intervalEvaluation (X := X) β M t
  let Φ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalAlgebraicSourceOperatorHom (X := X) β M α U π hπ
  let Ψ : AlgebraicCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β)
        (Module β (HilbertModuleFibre B M t)) (Module β (HilbertModuleFibre B M t)) :=
    algebraicSourceOperatorHom (Γ := Γ) (A := A) (B := B) β
      (HilbertModuleFibre B M t) α (U.fibre t)
      (fibreSourceRepresentation (X := X) M π t)
      (fibreSourceRepresentation_equivariant (X := X) β M α U π hπ t)
  change ε (Φ f u) = Ψ f (ε u)
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp only [map_zero, AdjointableMap.coe_zero_apply]
  | single g a =>
    have hΦ : Φ (AlgebraicCrossedProduct.single α g a) =
        intervalOperatorHom (X := X) β M (π a) * intervalGroupOperator (X := X) β M U g :=
      covariantAlgebraicRepresentation_single
        (Γ := Γ) (A := A) (C := C(X, ReducedCrossedProduct β))
        (H := IntervalModule (X := X) β M)
        (intervalGroupAction (X := X) β M U)
        (intervalSourceRepresentation (X := X) β M π) α
        (intervalSourceRepresentation_equivariant (X := X) β M α U π hπ) g a
    have hΨ : Ψ (AlgebraicCrossedProduct.single α g a) =
        operatorHom β (HilbertModuleFibre B M t)
            (hilbertModuleFibreOperator (B := B) (M := M) t (π a)) *
          groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g :=
      algebraicSourceOperatorHom_single (Γ := Γ) (A := A) (B := B) β
        (HilbertModuleFibre B M t) α (U.fibre t)
        (fibreSourceRepresentation (X := X) M π t)
        (fibreSourceRepresentation_equivariant (X := X) β M α U π hπ t) g a
    calc
      ε (Φ (AlgebraicCrossedProduct.single α g a) u) =
          ε (intervalOperatorHom (X := X) β M (π a)
            (intervalGroupOperator (X := X) β M U g u)) :=
        congrArg (fun T : AdjointableMap C(X, ReducedCrossedProduct β)
          (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => ε (T u)) hΦ
      _ = operatorHom β (HilbertModuleFibre B M t)
          (hilbertModuleFibreOperator (B := B) (M := M) t (π a))
          (ε (intervalGroupOperator (X := X) β M U g u)) :=
        intervalEvaluation_operator (X := X) β M t (π a)
          (intervalGroupOperator (X := X) β M U g u)
      _ = operatorHom β (HilbertModuleFibre B M t)
          (hilbertModuleFibreOperator (B := B) (M := M) t (π a))
          (groupOperator β (HilbertModuleFibre B M t) (U.fibre t) g (ε u)) :=
        congrArg (fun v : Module β (HilbertModuleFibre B M t) =>
          operatorHom β (HilbertModuleFibre B M t)
            (hilbertModuleFibreOperator (B := B) (M := M) t (π a)) v)
          (intervalEvaluation_groupOperator (X := X) β M t U g u)
      _ = Ψ (AlgebraicCrossedProduct.single α g a) (ε u) :=
        congrArg (fun T : AdjointableMap (ReducedCrossedProduct β)
          (Module β (HilbertModuleFibre B M t)) (Module β (HilbertModuleFibre B M t)) =>
          T (ε u)) hΨ.symm
  | add f h ihf ihh =>
    simp only [map_add, AdjointableMap.coe_add_apply, ihf, ihh]

/-- The actual continuous coefficient inner product recovers the global
norm from all the evaluated module norms. -/
theorem intervalNorm_le_of_evaluations (u : IntervalModule (X := X) β M) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ t : X, ‖intervalEvaluation (X := X) β M t u‖ ≤ r) : ‖u‖ ≤ r := by
  have hsq : ‖u‖ ^ 2 ≤ r ^ 2 := by
    rw [CStarModule.norm_sq_eq (C(X, ReducedCrossedProduct β)ᵐᵒᵖ),
      ← MulOpposite.norm_unop]
    apply (ContinuousMap.norm_le _ (sq_nonneg r)).mpr
    intro t
    have ht := (sq_le_sq₀ (norm_nonneg (intervalEvaluation (X := X) β M t u)) hr).mpr (h t)
    rw [CStarModule.norm_sq_eq ((ReducedCrossedProduct β)ᵐᵒᵖ)] at ht
    have hinner :
        ⟪intervalEvaluation (X := X) β M t u,
          intervalEvaluation (X := X) β M t u⟫_((ReducedCrossedProduct β)ᵐᵒᵖ) =
          MulOpposite.op
            ((MulOpposite.unop ⟪u, u⟫_(C(X, ReducedCrossedProduct β)ᵐᵒᵖ)) t) :=
      GradedMatrixMoritaFibreTensor.evaluation_inner
        (B := B) (C := ReducedCrossedProduct β) (X := X)
        (E := M) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
        (coefficientRepresentation β) t u u
    have hnorm :
        ‖⟪intervalEvaluation (X := X) β M t u,
          intervalEvaluation (X := X) β M t u⟫_((ReducedCrossedProduct β)ᵐᵒᵖ)‖ =
          ‖(MulOpposite.unop ⟪u, u⟫_(C(X, ReducedCrossedProduct β)ᵐᵒᵖ)) t‖ :=
      (congrArg (fun c : (ReducedCrossedProduct β)ᵐᵒᵖ => ‖c‖) hinner).trans
        (MulOpposite.norm_op
          ((MulOpposite.unop ⟪u, u⟫_(C(X, ReducedCrossedProduct β)ᵐᵒᵖ)) t))
    exact hnorm.symm.le.trans ht
  exact (sq_le_sq₀ (norm_nonneg u) hr).mp hsq

end BC4lean.KKTheory.KasparovDescent
