import BC4lean.ProjectionHilbertModule
import BC4lean.IntervalModuleFibre

/-! # Genuine fibres of continuous projection range modules

A continuous family of actual projections gives a projection on the actual
continuous-section Hilbert module. Evaluation of its range is onto the
pointwise projection range: project a constant section to lift every supported
vector. The coefficient inner product evaluates exactly, so the proved
radical-quotient completion construction yields a genuine fibre unitary.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Pointwise projection laws imply the actual section operator is a projection. -/
theorem continuousSectionOperator_isStarProjection
    (P : C(X, AdjointableMap B E E)) (hP : ∀ t, IsStarProjection (P t)) :
    IsStarProjection (continuousSectionOperator P) := by
  apply isStarProjection_iff'.mpr
  constructor
  · ext x t
    change P t (P t (x t)) = P t (x t)
    simpa only [AdjointableMap.mul_apply] using
      congrArg (fun T : AdjointableMap B E E => T (x t)) (hP t).isIdempotentElem.eq
  · ext x t
    change (P t).adjoint (x t) = P t (x t)
    have hs : (P t).adjoint = P t := by
      simpa only [AdjointableMap.star_eq_adjoint] using (hP t).isSelfAdjoint.star_eq
    rw [hs]

/-- Evaluation of the true section range, corestricted to its true pointwise range. -/
def projectionSectionEvaluation (P : C(X, AdjointableMap B E E)) (t : X) :
    ProjectionModule (continuousSectionOperator P) →L[ℂ] ProjectionModule (P t) :=
  ((continuousSectionEvaluation (E := E) t).comp
    (projectionFixedSubmodule (continuousSectionOperator P)).subtypeL).codRestrict
      (projectionFixedSubmodule (P t)) (fun x => by
        change P t ((x : C(X, E)) t) = (x : C(X, E)) t
        exact congrArg (fun y : C(X, E) => y t) x.property)

omit [CompleteSpace E] in
@[simp] theorem projectionSectionEvaluation_coe (P : C(X, AdjointableMap B E E))
    (t : X) (x : ProjectionModule (continuousSectionOperator P)) :
    ((projectionSectionEvaluation P t x : ProjectionModule (P t)) : E) = (x : C(X, E)) t := rfl

omit [CompleteSpace E] in
/-- Projecting a constant section gives an actual lift of every supported vector. -/
theorem projectionSectionEvaluation_surjective (P : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (t : X) :
    Function.Surjective (projectionSectionEvaluation P t) := by
  intro x
  refine ⟨projectionCorestrict (continuousSectionOperator P)
    (continuousSectionOperator_isStarProjection P hP) (ContinuousMap.const X (x : E)), ?_⟩
  apply Subtype.ext
  change P t (x : E) = (x : E)
  exact x.property

omit [CompleteSpace E] in
/-- The full coefficient form evaluates to the pointwise supported inner product. -/
theorem projectionSectionEvaluation_inner (P : C(X, AdjointableMap B E E))
    (t : X) (x y : ProjectionModule (continuousSectionOperator P)) :
    ⟪projectionSectionEvaluation P t x, projectionSectionEvaluation P t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := rfl

/-- Evaluation descends the actual fibre radical and completes to a unitary. -/
def projectionSectionFibreEquiv (P : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (t : X) :
    HilbertModuleEquiv B
      (HilbertModuleFibre B (ProjectionModule (continuousSectionOperator P)) t)
      (ProjectionModule (P t)) :=
  hilbertModuleFibreEquivOfEvaluation t (projectionSectionEvaluation P t)
    (projectionSectionEvaluation_inner P t) (projectionSectionEvaluation_surjective P hP t)

@[simp] theorem projectionSectionFibreEquiv_mk (P : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (t : X)
    (x : ProjectionModule (continuousSectionOperator P)) :
    projectionSectionFibreEquiv P hP t (hilbertModuleFibreMk (B := B) t x) =
      projectionSectionEvaluation P t x :=
  hilbertModuleFibreEquivOfEvaluation_mk _ _ _ _ _

/-- Compression of a continuous operator family to the actual section range. -/
def projectionSectionCompression (P S : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) :
    AdjointableMap C(X, B) (ProjectionModule (continuousSectionOperator P))
      (ProjectionModule (continuousSectionOperator P)) :=
  (projectionCorestrict (continuousSectionOperator P)
    (continuousSectionOperator_isStarProjection P hP)).comp
      ((continuousSectionOperator S).comp (projectionInclusion (continuousSectionOperator P)
        (continuousSectionOperator_isStarProjection P hP)))

/-- Actual fibre evaluation intertwines actual compressed section operators. -/
theorem projectionSectionFibreEquiv_compression (P S : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (t : X)
    (x : HilbertModuleFibre B (ProjectionModule (continuousSectionOperator P)) t) :
    projectionSectionFibreEquiv P hP t
        (hilbertModuleFibreOperator (B := B) t (projectionSectionCompression P S hP) x) =
      ((projectionCorestrict (P t) (hP t)).comp
        ((S t).comp (projectionInclusion (P t) (hP t))))
          (projectionSectionFibreEquiv P hP t x) := by
  refine (hilbertModuleFibreMk_denseRange (B := B)
    (M := ProjectionModule (continuousSectionOperator P)) t).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro y
    rw [hilbertModuleFibreOperator_mk, projectionSectionFibreEquiv_mk,
      projectionSectionFibreEquiv_mk]
    apply Subtype.ext
    rfl

end BC4lean.KKTheory
