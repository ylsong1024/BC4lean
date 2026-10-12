import BC4lean.RelativeProjectionSum
import BC4lean.ProjectionHilbertModuleSplit
import BC4lean.RelativeProjectionIntertwiningCycleIso

/-! # Genuine cutoff splitting and removal of an equal reference tail

An actual projection commuting with a cutoff compresses to projections on the
true cutoff and complementary ranges. The proved orthogonal range unitary
identifies the pair with its two blocks. When the projections agree on the
entire complementary tail, that relative block is exactly degenerate and its
full homotopy class vanishes. No cutoff compactness is required.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

omit [StarOrderedRing B] in
/-- Complementing an actual cutoff preserves its commutation law. -/
theorem projection_complement_commute {C P : AdjointableMap B E E} (h : Commute C P) :
    Commute (1 - C) P := (Commute.one_left P).sub_left h

/-- Actual compression, with the cutoff range as both source and target. -/
def projectionCompression (C : AdjointableMap B E E) (hC : IsStarProjection C)
    (T : AdjointableMap B E E) : AdjointableMap B (ProjectionModule C) (ProjectionModule C) :=
  (projectionCorestrict C hC).comp (T.comp (projectionInclusion C hC))

omit [StarOrderedRing B] in
@[simp] theorem projectionCompression_coe (C : AdjointableMap B E E) (hC : IsStarProjection C)
    (T : AdjointableMap B E E) (x : ProjectionModule C) :
    ((projectionCompression C hC T x : ProjectionModule C) : E) = C (T (x : E)) := rfl

omit [StarOrderedRing B] in
/-- A commuting actual projection remains a projection on the actual range. -/
theorem projectionCompression_isStarProjection (C P : AdjointableMap B E E)
    (hC : IsStarProjection C) (hP : IsStarProjection P) (hCommute : Commute C P) :
    IsStarProjection (projectionCompression C hC P) := by
  have hCP (x : E) : C (P x) = P (C x) :=
    congrArg (fun T : AdjointableMap B E E => T x) hCommute.eq
  have hPP (x : E) : P (P x) = P x :=
    congrArg (fun T : AdjointableMap B E E => T x) hP.isIdempotentElem.eq
  apply isStarProjection_iff'.mpr
  constructor
  · ext x
    change C (P (C (P (x : E)))) = C (P (x : E))
    have hx : C (x : E) = (x : E) := x.property
    have hFixed : C (P (x : E)) = P (x : E) :=
      (hCP (x : E)).trans (congrArg P hx)
    calc
      C (P (C (P (x : E)))) = C (P (P (x : E))) :=
        congrArg (fun y : E => C (P y)) hFixed
      _ = C (P (x : E)) := congrArg C (hPP (x : E))
  · ext x
    change C (P.adjoint (x : E)) = C (P (x : E))
    have hstar : P.adjoint = P := by
      simpa only [AdjointableMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
    rw [hstar]

/-- Compression of a true compact difference remains compact by both actual maps. -/
theorem projectionCompression_difference_isModuleCompact (C P Q : AdjointableMap B E E)
    (hC : IsStarProjection C) (hc : IsModuleCompact (P - Q)) :
    IsModuleCompact (projectionCompression C hC P - projectionCompression C hC Q) := by
  have heq : projectionCompression C hC P - projectionCompression C hC Q =
      projectionCompression C hC (P - Q) := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    simpa only [AdjointableMap.coe_sub_apply, Submodule.coe_sub, projectionCompression_coe] using
      (C.toCLM.map_sub (P (x : E)) (Q (x : E))).symm
  rw [heq]
  exact (hc.comp_right (projectionInclusion C hC)).comp_left (projectionCorestrict C hC)

/-- The actual orthogonal split sends every commuting operator to its two compressions. -/
theorem projectionModuleSplitEquiv_transport (C P : AdjointableMap B E E)
    (hC : IsStarProjection C) (hCommute : Commute C P) :
    (projectionModuleSplitEquiv C hC).transport P =
      sumMap (projectionCompression C hC P) (projectionCompression (1 - C) hC.one_sub P) := by
  have hCP (x : E) : C (P x) = P (C x) :=
    congrArg (fun T : AdjointableMap B E E => T x) hCommute.eq
  have hQP (x : E) : (1 - C) (P x) = P ((1 - C) x) :=
    congrArg (fun T : AdjointableMap B E E => T x) (projection_complement_commute hCommute).eq
  apply AdjointableMap.ext
  intro x
  rw [HilbertModuleEquiv.transport_apply, projectionModuleSplitEquiv_symm_apply,
    projectionModuleSplitEquiv_apply, sumMap_apply]
  apply Prod.ext
  · apply Subtype.ext
    change C (P ((x.fst : E) + (x.snd : E))) = C (P (x.fst : E))
    rw [P.toCLM.map_add, C.toCLM.map_add, hCP (x.snd : E),
      projection_complement_fixed_eq_zero, map_zero, add_zero]
  · apply Subtype.ext
    change (1 - C) (P ((x.fst : E) + (x.snd : E))) = (1 - C) (P (x.snd : E))
    rw [P.toCLM.map_add, (1 - C).toCLM.map_add, hQP (x.fst : E),
      projection_complement_apply_fixed, map_zero, zero_add]

variable [CompleteSpace E]

/-- The true cutoff and tail blocks add to the actual original relative class. -/
theorem relativeProjectionCutoffSplit_class (C P Q : AdjointableMap B E E)
    (hC : IsStarProjection C) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hCP : Commute C P) (hCQ : Commute C Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of (relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE)) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := Γ) (projectionCompression C hC P) (projectionCompression C hC Q)
          (projectionCompression_isStarProjection C P hC hP hCP)
          (projectionCompression_isStarProjection C Q hC hQ hCQ)
          (projectionCompression_difference_isModuleCompact C P Q hC hc)
          (projectionModule_isCountablyGenerated C hC hE))) +
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := Γ) (projectionCompression (1 - C) hC.one_sub P)
          (projectionCompression (1 - C) hC.one_sub Q)
          (projectionCompression_isStarProjection (1 - C) P hC.one_sub hP (projection_complement_commute hCP))
          (projectionCompression_isStarProjection (1 - C) Q hC.one_sub hQ (projection_complement_commute hCQ))
          (projectionCompression_difference_isModuleCompact (1 - C) P Q hC.one_sub hc)
          (projectionModule_isCountablyGenerated (1 - C) hC.one_sub hE))) := by
  have hP₀ := projectionCompression_isStarProjection C P hC hP hCP
  have hQ₀ := projectionCompression_isStarProjection C Q hC hQ hCQ
  have hP₁ := projectionCompression_isStarProjection (1 - C) P hC.one_sub hP
    (projection_complement_commute hCP)
  have hQ₁ := projectionCompression_isStarProjection (1 - C) Q hC.one_sub hQ
    (projection_complement_commute hCQ)
  have hc₀ := projectionCompression_difference_isModuleCompact C P Q hC hc
  have hc₁ := projectionCompression_difference_isModuleCompact (1 - C) P Q hC.one_sub hc
  have hE₀ := projectionModule_isCountablyGenerated C hC hE
  have hE₁ := projectionModule_isCountablyGenerated (1 - C) hC.one_sub hE
  have hTransport := KasparovHomotopyClass.mk_eq_of_iso
    (c := BundledKasparovCycle.of _) (d := BundledKasparovCycle.of _)
    (relativeProjectionIntertwiningCycleIso (Γ := Γ) (projectionModuleSplitEquiv C hC) P Q
      (sumMap (projectionCompression C hC P) (projectionCompression (1 - C) hC.one_sub P))
      (sumMap (projectionCompression C hC Q) (projectionCompression (1 - C) hC.one_sub Q))
      hP hQ (sumMap_isStarProjection hP₀ hP₁) (sumMap_isStarProjection hQ₀ hQ₁)
      hc (by rw [← sumMap_sub]; exact hc₀.sumMap hc₁) hE (hE₀.sum hE₁)
      (by
        intro x
        have h := congrArg (fun T => T (projectionModuleSplitEquiv C hC x))
          (projectionModuleSplitEquiv_transport C P hC hCP)
        simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h)
      (by
        intro x
        have h := congrArg (fun T => T (projectionModuleSplitEquiv C hC x))
          (projectionModuleSplitEquiv_transport C Q hC hCQ)
        simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h))
  exact hTransport.trans (relativeProjectionSum_class _ _ _ _
    (projectionCompression_isStarProjection C P hC hP hCP)
    (projectionCompression_isStarProjection C Q hC hQ hCQ)
    (projectionCompression_isStarProjection (1 - C) P hC.one_sub hP (projection_complement_commute hCP))
    (projectionCompression_isStarProjection (1 - C) Q hC.one_sub hQ (projection_complement_commute hCQ))
    (projectionCompression_difference_isModuleCompact C P Q hC hc)
    (projectionCompression_difference_isModuleCompact (1 - C) P Q hC.one_sub hc)
    (projectionModule_isCountablyGenerated C hC hE)
    (projectionModule_isCountablyGenerated (1 - C) hC.one_sub hE))

/-- Agreement on the entire tail is exact degeneracy of the actual tail cycle. -/
theorem relativeProjectionEqualTail_class (C P Q : AdjointableMap B E E)
    (hC : IsStarProjection C) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hCP : Commute C P) (hCQ : Commute C Q)
    (hTail : (1 - C) * P = (1 - C) * Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of (relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE)) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := Γ) (projectionCompression C hC P) (projectionCompression C hC Q)
          (projectionCompression_isStarProjection C P hC hP hCP)
          (projectionCompression_isStarProjection C Q hC hQ hCQ)
          (projectionCompression_difference_isModuleCompact C P Q hC hc)
          (projectionModule_isCountablyGenerated C hC hE))) := by
  have hCompressionTail : projectionCompression (1 - C) hC.one_sub P =
      projectionCompression (1 - C) hC.one_sub Q := by
    ext x
    exact congrArg (fun T : AdjointableMap B E E => T (x : E)) hTail
  have hDegenerate {R S : AdjointableMap B (ProjectionModule (1 - C)) (ProjectionModule (1 - C))}
      (hR : IsStarProjection R) (hS : IsStarProjection S) (hRS : IsModuleCompact (R - S))
      (hModule : IsCountablyGeneratedModule B (ProjectionModule (1 - C))) (hEq : R = S) :
      (relativeProjectionCycle (Γ := Γ) R S hR hS hRS hModule).IsDegenerate := by
    subst S
    exact relativeProjectionCycle_diagonal_isDegenerate R hR hRS hModule
  have hZero := KasparovHomotopyClass.mk_eq_zero_of_degenerate
    (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) (projectionCompression (1 - C) hC.one_sub P)
        (projectionCompression (1 - C) hC.one_sub Q)
        (projectionCompression_isStarProjection (1 - C) P hC.one_sub hP (projection_complement_commute hCP))
        (projectionCompression_isStarProjection (1 - C) Q hC.one_sub hQ (projection_complement_commute hCQ))
        (projectionCompression_difference_isModuleCompact (1 - C) P Q hC.one_sub hc)
        (projectionModule_isCountablyGenerated (1 - C) hC.one_sub hE))) (by
      exact hDegenerate
        (projectionCompression_isStarProjection (1 - C) P hC.one_sub hP
          (projection_complement_commute hCP))
        (projectionCompression_isStarProjection (1 - C) Q hC.one_sub hQ
          (projection_complement_commute hCQ))
        (projectionCompression_difference_isModuleCompact (1 - C) P Q hC.one_sub hc)
        (projectionModule_isCountablyGenerated (1 - C) hC.one_sub hE) hCompressionTail)
  rw [relativeProjectionCutoffSplit_class C P Q hC hP hQ hCP hCQ hc hE, hZero, add_zero]

end BC4lean.KKTheory
