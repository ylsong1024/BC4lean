import BC4lean.StandardCountableGeneration
import BC4lean.StandardCountableFiniteProjection
import BC4lean.RelativeProjectionCutoffSplit
import BC4lean.RelativeProjectionHomotopy

/-! # Genuine finite relative representatives in the full homotopy class

The actual finite coordinate isometry identifies the true cutoff range with
B^(n+n). Exact reference-tail equality removes the degenerate complementary
cycle. The constructed rounded projection path gives a genuine full homotopy,
so the resulting equal-scalar-part finite unitization pair represents the
original relative projection class. This is a pointwise finite representative;
independence and descent of an index remain separate obligations.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
open scoped InnerProductSpace
open unitInterval

variable {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)

/-- The actual finite coordinate image is fixed by the actual cutoff. -/
theorem pairedStandardFiniteInclusion_range (n : ℕ)
    (x : FiniteStandardModule B (PairedStandardFiniteIndex n)) :
    standardCountablePairedCutoff n (pairedStandardFiniteInclusion n x) = pairedStandardFiniteInclusion n x := by
  have hJ := congrArg (fun T : AdjointableMap B
      (FiniteStandardModule B (PairedStandardFiniteIndex n))
      (FiniteStandardModule B (PairedStandardFiniteIndex n)) => T x)
    (pairedStandardFiniteInclusion_adjoint_comp_self (B := B) n)
  change (pairedStandardFiniteInclusion n).adjoint (pairedStandardFiniteInclusion n x) = x at hJ
  rw [← pairedStandardFiniteInclusion_comp_adjoint]
  change pairedStandardFiniteInclusion n
    ((pairedStandardFiniteInclusion n).adjoint (pairedStandardFiniteInclusion n x)) = _
  rw [hJ]

/-- The full coefficient inner product is preserved by extraction on the true range. -/
theorem pairedStandardFiniteRange_inner (n : ℕ)
    (x y : ProjectionModule (standardCountablePairedCutoff (B := B) n)) :
    ⟪(pairedStandardFiniteInclusion (B := B) n).adjoint (x : StdPair),
      (pairedStandardFiniteInclusion (B := B) n).adjoint (y : StdPair)⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(pairedStandardFiniteInclusion (B := B) n).adjoint.adjoint_identity]
  change ⟪(x : StdPair), pairedStandardFiniteInclusion (B := B) n
    ((pairedStandardFiniteInclusion (B := B) n).adjoint (y : StdPair))⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
  have hC := congrArg (fun T : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) => T (y : StdPair))
    (pairedStandardFiniteInclusion_comp_adjoint (B := B) n)
  change pairedStandardFiniteInclusion (B := B) n ((pairedStandardFiniteInclusion (B := B) n).adjoint (y : StdPair)) =
    standardCountablePairedCutoff n (y : StdPair) at hC
  rw [hC, y.property]
  rfl

/-- The genuine cutoff range is unitarily the actual finite standard B-module. -/
def pairedStandardFiniteRangeEquiv (n : ℕ) :
    HilbertModuleEquiv B (ProjectionModule (standardCountablePairedCutoff (B := B) n))
      (FiniteStandardModule B (PairedStandardFiniteIndex n)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => (pairedStandardFiniteInclusion (B := B) n).adjoint (x : StdPair)
          invFun := fun y => ⟨pairedStandardFiniteInclusion (B := B) n y, pairedStandardFiniteInclusion_range n y⟩
          left_inv := fun x => by
            apply Subtype.ext
            change pairedStandardFiniteInclusion (B := B) n ((pairedStandardFiniteInclusion (B := B) n).adjoint (x : StdPair)) = (x : StdPair)
            have h := congrArg (fun T : AdjointableMap B
                (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
                (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) => T (x : StdPair))
              (pairedStandardFiniteInclusion_comp_adjoint (B := B) n)
            exact h.trans x.property
          right_inv := fun y => by
            exact congrArg (fun T : AdjointableMap B
                (FiniteStandardModule B (PairedStandardFiniteIndex n))
                (FiniteStandardModule B (PairedStandardFiniteIndex n)) => T y)
              (pairedStandardFiniteInclusion_adjoint_comp_self (B := B) n)
          map_add' := fun x y => (pairedStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_add (x : StdPair) (y : StdPair)
          map_smul' := fun c x => (pairedStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_smul c (x : StdPair) }
      norm_map' x := by
        change ‖(pairedStandardFiniteInclusion (B := B) n).adjoint (x : StdPair)‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
          ((pairedStandardFiniteInclusion (B := B) n).adjoint (x : StdPair)), pairedStandardFiniteRange_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := pairedStandardFiniteRange_inner n

/-- The actual range unitary transports compression to the actual finite matrix operator. -/
theorem pairedStandardFiniteRangeEquiv_transport (n : ℕ)
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hCP : Commute (standardCountablePairedCutoff n) P) :
    (pairedStandardFiniteRangeEquiv n).transport
        (projectionCompression (standardCountablePairedCutoff n)
          (standardCountablePairedCutoff_isStarProjection n) P) =
      pairedStandardFiniteCompression n P := by
  apply AdjointableMap.ext
  intro x
  change (pairedStandardFiniteInclusion (B := B) n).adjoint
      (standardCountablePairedCutoff n (P (pairedStandardFiniteInclusion (B := B) n x))) =
    (pairedStandardFiniteInclusion (B := B) n).adjoint (P (pairedStandardFiniteInclusion (B := B) n x))
  have hComm := congrArg (fun T : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) =>
        T (pairedStandardFiniteInclusion (B := B) n x)) hCP.eq
  change standardCountablePairedCutoff n (P (pairedStandardFiniteInclusion (B := B) n x)) =
    P (standardCountablePairedCutoff n (pairedStandardFiniteInclusion (B := B) n x)) at hComm
  rw [hComm, pairedStandardFiniteInclusion_range]

variable [TopologicalSpace.SeparableSpace B]

/-- Exact equal-tail removal followed by the actual coordinate range unitary. -/
theorem pairedStandardRelativeProjection_finite_class (n : ℕ)
    (R : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hR : IsStarProjection R) (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection))
    (hCR : Commute (standardCountablePairedCutoff n) R)
    (hTail : (1 - standardCountablePairedCutoff n) * R =
      (1 - standardCountablePairedCutoff n) * standardCountablePairedReferenceProjection)
    (p : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n))
    (hScalar : ∀ i j, (p.val i j).fst = (pairedStandardFiniteReferenceMatrix (B := B) n i j).fst)
    (hOperator : unitizedModuleMatrixRepresentation p.val = pairedStandardFiniteCompression n R) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := PUnit) R standardCountablePairedReferenceProjection hR
        standardCountablePairedReferenceProjection_isStarProjection hc
        (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (unitizedRelativeProjectionCycle (Γ := PUnit) p
          ⟨pairedStandardFiniteReferenceMatrix n, pairedStandardFiniteReferenceMatrix_isStarProjection n⟩ hScalar)) := by
  have hCQ : Commute (standardCountablePairedCutoff (B := B) n) standardCountablePairedReferenceProjection :=
    standardCountablePairedCutoff_commutes_reference n
  apply (relativeProjectionEqualTail_class (Γ := PUnit) (standardCountablePairedCutoff n) R
    standardCountablePairedReferenceProjection (standardCountablePairedCutoff_isStarProjection n)
    hR standardCountablePairedReferenceProjection_isStarProjection hCR hCQ hTail hc
    (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B)))).trans
  have h := relativeProjectionTransport_class (Γ := PUnit) (pairedStandardFiniteRangeEquiv n)
    (projectionCompression (standardCountablePairedCutoff n) (standardCountablePairedCutoff_isStarProjection n) R)
    (projectionCompression (standardCountablePairedCutoff n) (standardCountablePairedCutoff_isStarProjection n)
      standardCountablePairedReferenceProjection)
    (projectionCompression_isStarProjection _ _ (standardCountablePairedCutoff_isStarProjection n) hR hCR)
    (projectionCompression_isStarProjection _ _ (standardCountablePairedCutoff_isStarProjection n)
      standardCountablePairedReferenceProjection_isStarProjection hCQ)
    (projectionCompression_difference_isModuleCompact _ _ _ (standardCountablePairedCutoff_isStarProjection n) hc)
    (projectionModule_isCountablyGenerated _ (standardCountablePairedCutoff_isStarProjection n)
      (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))
  have hPoperator := (pairedStandardFiniteRangeEquiv_transport n R hCR).trans hOperator.symm
  have hQoperator :=
    (pairedStandardFiniteRangeEquiv_transport n standardCountablePairedReferenceProjection hCQ).trans
      (pairedStandardFiniteCompression_reference (B := B) n)
  have hFiniteClass
      (P' Q' : AdjointableMap B (FiniteStandardModule B (PairedStandardFiniteIndex n))
        (FiniteStandardModule B (PairedStandardFiniteIndex n)))
      (hP' : IsStarProjection P') (hQ' : IsStarProjection Q')
      (hc' : IsModuleCompact (P' - Q'))
      (hE' : IsCountablyGeneratedModule B (FiniteStandardModule B (PairedStandardFiniteIndex n)))
      (hPvalue : P' = unitizedModuleMatrixRepresentation p.val)
      (hQvalue : Q' = unitizedModuleMatrixRepresentation (pairedStandardFiniteReferenceMatrix (B := B) n)) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P' Q' hP' hQ' hc' hE')) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (unitizedRelativeProjectionCycle (Γ := PUnit) p
          ⟨pairedStandardFiniteReferenceMatrix n, pairedStandardFiniteReferenceMatrix_isStarProjection n⟩ hScalar)) := by
    subst P'
    subst Q'
    rfl
  exact h.trans (hFiniteClass _ _
    ((pairedStandardFiniteRangeEquiv n).transport_isStarProjection
      (projectionCompression_isStarProjection _ _ (standardCountablePairedCutoff_isStarProjection n) hR hCR))
    ((pairedStandardFiniteRangeEquiv n).transport_isStarProjection
      (projectionCompression_isStarProjection _ _ (standardCountablePairedCutoff_isStarProjection n)
        standardCountablePairedReferenceProjection_isStarProjection hCQ))
    ((pairedStandardFiniteRangeEquiv n).transport_difference_isModuleCompact
      (projectionCompression_difference_isModuleCompact _ _ _ (standardCountablePairedCutoff_isStarProjection n) hc))
    ((pairedStandardFiniteRangeEquiv n).isCountablyGeneratedModule
      (projectionModule_isCountablyGenerated _ (standardCountablePairedCutoff_isStarProjection n)
        (IsCountablyGeneratedModule.sum
          (standardCountableHilbertModule_isCountablyGenerated (B := B))
          (standardCountableHilbertModule_isCountablyGenerated (B := B)))))
    hPoperator hQoperator)

/-- Every actual standard relative projection has a genuine finite equal-scalar
pair in its full homotopy class. Cutoff size, rounding gap and range unitaries
are all constructed by the preceding genuine proofs. -/
theorem exists_standardCountableFiniteRelativeClass
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsStarProjection P) (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ,
    ∃ p : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n),
    ∃ hScalar : ∀ i j, (p.val i j).fst = (pairedStandardFiniteReferenceMatrix (B := B) n i j).fst,
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P standardCountablePairedReferenceProjection hP
          standardCountablePairedReferenceProjection_isStarProjection hc
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) =
        KasparovHomotopyClass.mk (BundledKasparovCycle.of
          (unitizedRelativeProjectionCycle (Γ := PUnit) p
            ⟨pairedStandardFiniteReferenceMatrix n, pairedStandardFiniteReferenceMatrix_isStarProjection n⟩ hScalar)) := by
  obtain ⟨n, M, γ, hM, hScalar, hOperator, hγ, _⟩ :=
    exists_standardCountableFiniteUnitizationProjectionPath P hP hc
  let R := spectralGapRoundedProjection (standardCountableReferenceCompression P n)
  have hR : IsStarProjection R := by simpa only [γ.target] using (hγ 1).1
  have hRc : IsModuleCompact (R - standardCountablePairedReferenceProjection) := by
    simpa only [γ.target] using (hγ 1).2
  let p : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) := ⟨M, hM⟩
  have hscalar : ∀ i j, (p.val i j).fst = (pairedStandardFiniteReferenceMatrix (B := B) n i j).fst := by
    intro i j
    exact congrArg (fun K : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) ℂ => K i j) hScalar
  refine ⟨n, p, hscalar, ?_⟩
  have hPath := relativeProjectionPath_class (Γ := PUnit) γ.toContinuousMap
    (ContinuousMap.const I standardCountablePairedReferenceProjection)
    (fun t => (hγ t).1) (fun _ => standardCountablePairedReferenceProjection_isStarProjection)
    (fun t => (hγ t).2)
    (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B)))
  simp only [ContinuousMap.const_apply] at hPath
  have hEndpointClass (S T : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
      (hS : IsStarProjection S) (hT : IsStarProjection T)
      (hSc : IsModuleCompact (S - standardCountablePairedReferenceProjection))
      (hTc : IsModuleCompact (T - standardCountablePairedReferenceProjection)) (hST : S = T) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) S standardCountablePairedReferenceProjection hS
          standardCountablePairedReferenceProjection_isStarProjection hSc
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) T standardCountablePairedReferenceProjection hT
          standardCountablePairedReferenceProjection_isStarProjection hTc
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) := by
    subst T
    rfl
  have hSourceClass := hEndpointClass (γ.toContinuousMap 0) P (hγ 0).1 hP (hγ 0).2 hc γ.source
  have hTargetClass := hEndpointClass (γ.toContinuousMap 1) R (hγ 1).1 hR (hγ 1).2 hRc γ.target
  exact hSourceClass.symm.trans (hPath.trans (hTargetClass.trans
    (pairedStandardRelativeProjection_finite_class n R hR hRc
      (spectralGapRoundedReferenceCompression_commutes_cutoff P hP.isSelfAdjoint n)
      (spectralGapRoundedReferenceCompression_left_tail P hP.isSelfAdjoint n) p hscalar hOperator)))

end BC4lean.KKTheory
