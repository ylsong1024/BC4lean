import BC4lean.ScalarKasparovK0IndexQuotient
import BC4lean.NonunitalRelativeProjectionKKMap
import BC4lean.StandardCountableFiniteClass
import BC4lean.GlobalFredholmStandardClass

/-! # The constructed Julia index recovers the full scalar cycle class

One genuine rounded path supplies both the finite relative cycle and its
canonical finite coefficient matrix. Path invariance of the independently
constructed index identifies its value with the same actual scalar-kernel
projection difference. The existing forward map then recovers the whole raw
cycle class through support reduction, stabilization and Julia range maps.
This proves the right inverse; finite-pair index recovery is a separate
obligation for the left inverse.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open unitInterval

variable {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

theorem nonunitalRelativeK0KasparovMap_standardProjectionIndex
    (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    nonunitalRelativeK0KasparovMap (standardCountableRelativeProjectionIndex P hP hc) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P standardCountablePairedReferenceProjection hP
          standardCountablePairedReferenceProjection_isStarProjection hc
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) := by
  obtain ⟨n, M, γ, hM, hScalar, hOperator, hγ, hCorner⟩ :=
    exists_standardCountableFiniteUnitizationProjectionPath P hP hc
  let R := spectralGapRoundedProjection (standardCountableReferenceCompression P n)
  have hR : IsStarProjection R := by simpa only [γ.target] using (hγ 1).1
  have hRc : IsModuleCompact (R - standardCountablePairedReferenceProjection) := by
    simpa only [γ.target] using (hγ 1).2
  let p : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) := ⟨M, hM⟩
  let q : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n) :=
    ⟨pairedStandardFiniteReferenceMatrix n, pairedStandardFiniteReferenceMatrix_isStarProjection n⟩
  have hs : ∀ i j, (p.val i j).fst = (q.val i j).fst := fun i j =>
    congrArg (fun N : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) ℂ => N i j)
      hScalar
  have hIndexPath : standardCountableRelativeProjectionIndex P hP hc =
      standardCountableRelativeProjectionIndex R hR hRc := by
    have h := standardCountableRelativeProjectionIndex_path γ.toContinuousMap
      (fun t => (hγ t).1) (fun t => (hγ t).2)
    change standardCountableRelativeProjectionIndex (γ 0) ((hγ 0).1) ((hγ 0).2) =
      standardCountableRelativeProjectionIndex (γ 1) ((hγ 1).1) ((hγ 1).2) at h
    simpa only [γ.source, γ.target] using h
  have hIndexFinite : standardCountableRelativeProjectionIndex R hR hRc =
      equalScalarProjectionDifference p q hs := by
    rw [standardCountableRelativeProjectionIndex_supported R hR hRc n hCorner]
    apply operatorK0Inclusion_injective
    have hUnique : M = standardCountableRelativeFiniteMatrix R hRc n :=
      standardCountableRelativeFiniteMatrix_unique R hRc n M hScalar hOperator
    change k0Projection (unitizationFiniteProjection _ _) -
      k0Projection (unitizationFiniteProjection _ _) =
      k0Projection (finiteProjectionOfMatrix p) - k0Projection (finiteProjectionOfMatrix q)
    rw [k0Projection_finiteProjectionOfMatrix p, k0Projection_finiteProjectionOfMatrix q]
    change k0Projection (unitizationFiniteProjection _ _) -
      k0Projection (unitizationFiniteProjection _ _) =
      k0Projection (unitizationFiniteProjection M hM) -
        k0Projection (unitizationFiniteProjection (pairedStandardFiniteReferenceMatrix n)
          (pairedStandardFiniteReferenceMatrix_isStarProjection n))
    simp only [← hUnique]
  rw [hIndexPath, hIndexFinite]
  apply (nonunitalRelativeK0KasparovMap_equalScalarProjectionDifference p q hs).trans
  have hClassPath := relativeProjectionPath_class (Γ := PUnit) γ.toContinuousMap
    (ContinuousMap.const I standardCountablePairedReferenceProjection)
    (fun t => (hγ t).1) (fun _ => standardCountablePairedReferenceProjection_isStarProjection)
    (fun t => (hγ t).2)
    (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B)))
  change KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := PUnit) (γ 0) standardCountablePairedReferenceProjection
        ((hγ 0).1) standardCountablePairedReferenceProjection_isStarProjection ((hγ 0).2)
        (IsCountablyGeneratedModule.sum
          (standardCountableHilbertModule_isCountablyGenerated (B := B))
          (standardCountableHilbertModule_isCountablyGenerated (B := B))))) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := PUnit) (γ 1) standardCountablePairedReferenceProjection
        ((hγ 1).1) standardCountablePairedReferenceProjection_isStarProjection ((hγ 1).2)
        (IsCountablyGeneratedModule.sum
          (standardCountableHilbertModule_isCountablyGenerated (B := B))
          (standardCountableHilbertModule_isCountablyGenerated (B := B))))) at hClassPath
  have hEndpointClass
      (P₁ P₂ : StdEnd) (hP₁ : IsStarProjection P₁) (hP₂ : IsStarProjection P₂)
      (hc₁ : IsModuleCompact (P₁ - standardCountablePairedReferenceProjection))
      (hc₂ : IsModuleCompact (P₂ - standardCountablePairedReferenceProjection))
      (hPvalue : P₁ = P₂) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P₁ standardCountablePairedReferenceProjection hP₁
          standardCountablePairedReferenceProjection_isStarProjection hc₁
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P₂ standardCountablePairedReferenceProjection hP₂
          standardCountablePairedReferenceProjection_isStarProjection hc₂
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) := by
    subst P₂
    rfl
  have hClassSource := hEndpointClass (γ 0) P ((hγ 0).1) hP ((hγ 0).2) hc γ.source
  have hClassTarget := hEndpointClass (γ 1) R ((hγ 1).1) hR ((hγ 1).2) hRc γ.target
  exact ((hClassSource.symm.trans (hClassPath.trans hClassTarget)).trans
    (pairedStandardRelativeProjection_finite_class n R hR hRc
    (spectralGapRoundedReferenceCompression_commutes_cutoff P hP.isSelfAdjoint n)
    (spectralGapRoundedReferenceCompression_left_tail P hP.isSelfAdjoint n) p hs hOperator)).symm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

theorem KasparovCycle.nonunitalRelativeK0KasparovMap_operatorK0Index
    (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B) E) :
    nonunitalRelativeK0KasparovMap c.operatorK0Index =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c) := by
  let P : StdEnd := standardRectangularJuliaProjection c.scalarRectangularFredholm
    c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated
  have hP : IsStarProjection P := standardRectangularJuliaProjection_isStarProjection
    c.scalarRectangularFredholm c.scalarRectangularEvenModule_isCountablyGenerated
    c.scalarRectangularOddModule_isCountablyGenerated
  have hc : IsModuleCompact (P - standardCountablePairedReferenceProjection) :=
    standardRectangularJuliaProjection_sub_reference_isModuleCompact c.scalarRectangularFredholm
      c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated
      c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
  have h := nonunitalRelativeK0KasparovMap_standardProjectionIndex P hP hc
  change nonunitalRelativeK0KasparovMap c.operatorK0Index = _ at h
  let QJ : StdEnd := juliaReferenceProjection (B := B)
    (E := StandardCountableHilbertModule B) (F := StandardCountableHilbertModule B)
  have hReference : QJ = standardCountablePairedReferenceProjection := by
    apply AdjointableMap.ext
    intro x
    change juliaReferenceProjection (B := B) (E := StandardCountableHilbertModule B)
      (F := StandardCountableHilbertModule B) x =
      sumMap (0 : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) (1 : AdjointableMap B
          (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) x
    rw [juliaReferenceProjection_apply, sumMap_apply, AdjointableMap.coe_zero_apply,
      AdjointableMap.one_apply]
  have hQJ : IsStarProjection QJ := juliaReferenceProjection_isStarProjection
  have hcJ : IsModuleCompact (P - QJ) := by
    rw [hReference]
    exact hc
  have hReferenceClass
      (Q₁ Q₂ : StdEnd) (hQ₁ : IsStarProjection Q₁) (hQ₂ : IsStarProjection Q₂)
      (hc₁ : IsModuleCompact (P - Q₁)) (hc₂ : IsModuleCompact (P - Q₂))
      (hQvalue : Q₁ = Q₂) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P Q₁ hP hQ₁ hc₁
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P Q₂ hP hQ₂ hc₂
          (IsCountablyGeneratedModule.sum
            (standardCountableHilbertModule_isCountablyGenerated (B := B))
            (standardCountableHilbertModule_isCountablyGenerated (B := B))))) := by
    subst Q₂
    rfl
  have hBridge := hReferenceClass standardCountablePairedReferenceProjection QJ
    standardCountablePairedReferenceProjection_isStarProjection hQJ hc hcJ hReference.symm
  change KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := PUnit) P standardCountablePairedReferenceProjection hP
        standardCountablePairedReferenceProjection_isStarProjection hc
        (IsCountablyGeneratedModule.sum
          (standardCountableHilbertModule_isCountablyGenerated (B := B))
          (standardCountableHilbertModule_isCountablyGenerated (B := B))))) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (standardRectangularJuliaRelativeCycle c.scalarRectangularFredholm
        c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
        c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated)) at hBridge
  exact h.trans (hBridge.trans (scalarStandardJulia_class c).symm)

theorem nonunitalRelativeK0KasparovMap_scalarKKOperatorK0Index_rightInverse :
    Function.RightInverse (scalarKKOperatorK0Index (B := B)) nonunitalRelativeK0KasparovMap := by
  intro z
  obtain ⟨c, rfl⟩ := KasparovHomotopyClass.mk_surjective z
  rw [scalarKKOperatorK0Index_mk]
  simpa only [BundledKasparovCycle.of_storedCycle] using c.cycle.nonunitalRelativeK0KasparovMap_operatorK0Index

end BC4lean.KKTheory
