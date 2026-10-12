import BC4lean.ProjectionHilbertModuleFibre
import BC4lean.RelativeProjectionKasparovCycle
import BC4lean.KasparovHomotopyGroup

/-! # Actual relative projection homotopies with varying supported modules

A continuous pair of projections with compact difference acts on the genuine
continuous-section module. Uniform finite-rank approximation proves compactness
of the section difference. The two supported section ranges have actual onto
evaluations, giving a fibre unitary of their sum and whole-cycle endpoint
isomorphisms. Thus the homotopy uses the varying projection range modules.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} {X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [completeE : CompleteSpace E]

/-- The actual sum of the two supported section ranges. -/
abbrev ProjectionPairSectionModule (P Q : C(X, AdjointableMap B E E)) :=
  HilbertModuleSum C(X, B) (ProjectionModule (continuousSectionOperator P))
    (ProjectionModule (continuousSectionOperator Q))

/-- The actual sum of the two pointwise supported ranges. -/
abbrev ProjectionPairPointModule (P Q : C(X, AdjointableMap B E E)) (t : X) :=
  HilbertModuleSum B (ProjectionModule (P t)) (ProjectionModule (Q t))

/-- The genuine bounded evaluation on the sum of the supported ranges. -/
def projectionPairSectionEvaluation (P Q : C(X, AdjointableMap B E E)) (t : X) :
    ProjectionPairSectionModule P Q →L[ℂ] ProjectionPairPointModule P Q t :=
  sumInlCLM.comp ((projectionSectionEvaluation P t).comp sumFstCLM) +
    sumInrCLM.comp ((projectionSectionEvaluation Q t).comp sumSndCLM)

omit completeE in
@[simp] theorem projectionPairSectionEvaluation_apply [CompleteSpace E]
    (P Q : C(X, AdjointableMap B E E)) (t : X) (x : ProjectionPairSectionModule P Q) :
    projectionPairSectionEvaluation P Q t x =
      sumMk (projectionSectionEvaluation P t x.fst) (projectionSectionEvaluation Q t x.snd) := by
  simp only [projectionPairSectionEvaluation, _root_.add_apply,
    ContinuousLinearMap.comp_apply, sumInlCLM_apply, sumInrCLM_apply,
    sumFstCLM_apply, sumSndCLM_apply, sumMk_add, add_zero, zero_add]

/-- The full coefficient-valued sum form evaluates exactly. -/
theorem projectionPairSectionEvaluation_inner
    (P Q : C(X, AdjointableMap B E E)) (t : X) (x y : ProjectionPairSectionModule P Q) :
    ⟪projectionPairSectionEvaluation P Q t x, projectionPairSectionEvaluation P Q t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  simp only [projectionPairSectionEvaluation_apply, inner_sum, sumMk_fst, sumMk_snd,
    projectionSectionEvaluation_inner, MulOpposite.unop_add, ContinuousMap.add_apply,
    MulOpposite.op_add]

/-- Surjectivity uses the two actual projected constant lifts. -/
theorem projectionPairSectionEvaluation_surjective
    (P Q : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (hQ : ∀ t, IsStarProjection (Q t)) (t : X) :
    Function.Surjective (projectionPairSectionEvaluation P Q t) := by
  intro x
  obtain ⟨y, hy⟩ := projectionSectionEvaluation_surjective P hP t x.fst
  obtain ⟨z, hz⟩ := projectionSectionEvaluation_surjective Q hQ t x.snd
  refine ⟨sumMk y z, ?_⟩
  simp only [projectionPairSectionEvaluation_apply, sumMk_fst, sumMk_snd, hy, hz,
    sumMk_eta]

/-- The true completed evaluated fibre of the supported sum. -/
def projectionPairSectionFibreEquiv
    (P Q : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (hQ : ∀ t, IsStarProjection (Q t)) (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (ProjectionPairSectionModule P Q) t)
      (ProjectionPairPointModule P Q t) :=
  hilbertModuleFibreEquivOfEvaluation t (projectionPairSectionEvaluation P Q t)
    (projectionPairSectionEvaluation_inner P Q t)
    (projectionPairSectionEvaluation_surjective P Q hP hQ t)

@[simp] theorem projectionPairSectionFibreEquiv_mk
    (P Q : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (hQ : ∀ t, IsStarProjection (Q t)) (t : X)
    (x : ProjectionPairSectionModule P Q) :
    projectionPairSectionFibreEquiv P Q hP hQ t (hilbertModuleFibreMk (B := B) t x) =
      projectionPairSectionEvaluation P Q t x :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

variable [T2Space X]

/-- Uniform compact section approximation gives the actual relative section cycle. -/
def relativeProjectionSectionCycle (P Q : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (hQ : ∀ t, IsStarProjection (Q t))
    (hc : ∀ t, IsModuleCompact (P t - Q t)) (hE : IsCountablyGeneratedModule B E) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      ((CStarAlgebraAction.trivial : CStarAlgebraAction Γ B).continuousSections (X := X))
      (ProjectionPairSectionModule P Q) :=
  relativeProjectionCycle (continuousSectionOperator P) (continuousSectionOperator Q)
    (continuousSectionOperator_isStarProjection P hP)
    (continuousSectionOperator_isStarProjection Q hQ)
    (by
      rw [← continuousSectionOperator_sub]
      exact continuousSectionOperator_isModuleCompact (P - Q) hc)
    (continuousSection_isCountablyGenerated hE)

set_option maxHeartbeats 800000 in
/-- Evaluation identifies the entire relative cycle, including its actual
cross-range Fredholm operator, rather than only the underlying module. -/
def relativeProjectionSectionFibreIso (P Q : C(X, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (hQ : ∀ t, IsStarProjection (Q t))
    (hc : ∀ t, IsModuleCompact (P t - Q t)) (hE : IsCountablyGeneratedModule B E) (t : X) :
    KasparovCycleIso ((relativeProjectionSectionCycle (Γ := Γ) P Q hP hQ hc hE).fibre t)
      (relativeProjectionCycle (Γ := Γ) (P t) (Q t) (hP t) (hQ t) (hc t) hE) := by
  let c : KasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      ((CStarAlgebraAction.trivial : CStarAlgebraAction Γ B).continuousSections (X := X))
      (ProjectionPairSectionModule P Q) :=
    relativeProjectionSectionCycle (Γ := Γ) P Q hP hQ hc hE
  let d : KasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
      (ProjectionPairPointModule P Q t) :=
    relativeProjectionCycle (Γ := Γ) (P t) (Q t) (hP t) (hQ t) (hc t) hE
  let cf : KasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
      (HilbertModuleFibre B (ProjectionPairSectionModule P Q) t) := c.fibre t
  let U : HilbertModuleEquiv B
      (HilbertModuleFibre B (ProjectionPairSectionModule P Q) t)
      (ProjectionPairPointModule P Q t) := projectionPairSectionFibreEquiv P Q hP hQ t
  have hsurj : Function.Surjective
      (hilbertModuleFibreMk (B := B) (M := ProjectionPairSectionModule P Q) t) :=
    hilbertModuleFibreMk_surjective (B := B) (M := ProjectionPairSectionModule P Q) t
  have hU (x : ProjectionPairSectionModule P Q) :
      U (hilbertModuleFibreMk (B := B) t x) = projectionPairSectionEvaluation P Q t x :=
    projectionPairSectionFibreEquiv_mk P Q hP hQ t x
  have hgrading (z : HilbertModuleFibre B (ProjectionPairSectionModule P Q) t) :
      U (cf.grading.grading z) = d.grading.grading (U z) := by
    obtain ⟨x, rfl⟩ := hsurj z
    rw [KasparovCycle.fibre_grading_mk c t x, hU, hU]
    change projectionPairSectionEvaluation P Q t (sumMk (B := C(X, B)) x.fst (-x.snd)) =
      sumMk (B := B) (projectionPairSectionEvaluation P Q t x).fst
        (-(projectionPairSectionEvaluation P Q t x).snd)
    simp only [projectionPairSectionEvaluation_apply, sumMk_fst, sumMk_snd, map_neg]
  have haction (g : Γ) (z : HilbertModuleFibre B (ProjectionPairSectionModule P Q) t) :
      U (cf.groupAction.action g z) = d.groupAction.action g (U z) := by
    obtain ⟨x, rfl⟩ := hsurj z
    rw [KasparovCycle.fibre_action_mk c t g x, hU, hU]
    rfl
  have hrepresentation (a : ℂ) (z : HilbertModuleFibre B (ProjectionPairSectionModule P Q) t) :
      U (cf.representation a z) = d.representation a (U z) := by
    obtain ⟨x, rfl⟩ := hsurj z
    rw [KasparovCycle.fibre_representation_mk c t a x, hU, hU]
    change projectionPairSectionEvaluation P Q t (a • x) =
      a • projectionPairSectionEvaluation P Q t x
    exact (projectionPairSectionEvaluation P Q t).map_smul a x
  have hoperator (z : HilbertModuleFibre B (ProjectionPairSectionModule P Q) t) :
      U (cf.operator z) = d.operator (U z) := by
    obtain ⟨x, rfl⟩ := hsurj z
    rw [KasparovCycle.fibre_operator_mk c t x, hU, hU]
    change projectionPairSectionEvaluation P Q t
      (offDiagonalAdjointable (projectionCrossMap
        (continuousSectionOperator P) (continuousSectionOperator Q)
        (continuousSectionOperator_isStarProjection P hP)
        (continuousSectionOperator_isStarProjection Q hQ)) x) =
      offDiagonalAdjointable (projectionCrossMap (P t) (Q t) (hP t) (hQ t))
        (projectionPairSectionEvaluation P Q t x)
    apply Prod.ext <;> apply Subtype.ext
    · simp only [projectionPairSectionEvaluation_apply, offDiagonalAdjointable_apply,
        projectionCrossMap_adjoint, sumMk_fst, projectionSectionEvaluation_coe,
        projectionCrossMap_coe, continuousSectionOperator_apply, sumMk_snd]
    · simp only [projectionPairSectionEvaluation_apply, offDiagonalAdjointable_apply,
        sumMk_snd, projectionSectionEvaluation_coe, projectionCrossMap_coe,
        continuousSectionOperator_apply, sumMk_fst]
  exact
    { moduleEquiv := U
      grading_intertwine := hgrading
      action_intertwine := haction
      representation_intertwine := hrepresentation
      operator_intertwine := hoperator }

end BC4lean.KKTheory

namespace BC4lean.KKTheory
open unitInterval

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The constructed interval cycle on the supported section ranges is a genuine
full homotopy for the two endpoint relative projection cycles. -/
def relativeProjectionFullHomotopy (P Q : C(I, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (hQ : ∀ t, IsStarProjection (Q t))
    (hc : ∀ t, IsModuleCompact (P t - Q t)) (hE : IsCountablyGeneratedModule B E) :
    FullKasparovHomotopy
      (BundledKasparovCycle.of (relativeProjectionCycle (Γ := Γ) (P 0) (Q 0) (hP 0) (hQ 0) (hc 0) hE))
      (BundledKasparovCycle.of (relativeProjectionCycle (Γ := Γ) (P 1) (Q 1) (hP 1) (hQ 1) (hc 1) hE)) where
  intervalCycle := BundledKasparovCycle.of (relativeProjectionSectionCycle P Q hP hQ hc hE)
  sourceIso := relativeProjectionSectionFibreIso P Q hP hQ hc hE 0
  targetIso := relativeProjectionSectionFibreIso P Q hP hQ hc hE 1

/-- A genuine continuous compact-relative projection path preserves its full class. -/
theorem relativeProjectionPath_class (P Q : C(I, AdjointableMap B E E))
    (hP : ∀ t, IsStarProjection (P t)) (hQ : ∀ t, IsStarProjection (Q t))
    (hc : ∀ t, IsModuleCompact (P t - Q t)) (hE : IsCountablyGeneratedModule B E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) (P 0) (Q 0) (hP 0) (hQ 0) (hc 0) hE)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) (P 1) (Q 1) (hP 1) (hQ 1) (hc 1) hE)) :=
  KasparovHomotopyClass.mk_eq_of_full (relativeProjectionFullHomotopy P Q hP hQ hc hE)

end BC4lean.KKTheory
