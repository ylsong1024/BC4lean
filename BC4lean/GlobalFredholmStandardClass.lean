import BC4lean.GlobalFredholmStabilizationCycleIso
import BC4lean.GlobalFredholmNormalizationHomotopy
import BC4lean.ScalarKasparovSupportClass

/-! # Actual scalar Fredholm classes on the standard graded module

The class equalities use the constructed degenerate identity cycle, the actual
homogeneous shuffle and stabilization unitaries, the genuine compact affine
normalization homotopy, and the actual Julia range unitaries. They do not assume
index descent or independence of the eventual finite projection representative.
All carriers in these equalities use the indicated common module universe.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory

variable {B E F : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The constructed compact affine normalization preserves the full class. -/
theorem globalFredholmNormalization_class (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) (globalFredholmNormalization T)
        (globalFredholmNormalization_sourceDefect_isModuleCompact T hSource)
        (globalFredholmNormalization_targetDefect_isModuleCompact T hSource hTarget) hE hF)) := by
  have h := KasparovHomotopyClass.mk_eq_of_full
    (FullKasparovHomotopy.ofOperatorHomotopy
      (globalFredholmNormalizationHomotopy (Γ := PUnit) T hSource hTarget hE hF))
  change KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) (globalFredholmNormalization T)
        (globalFredholmNormalization_sourceDefect_isModuleCompact T hSource)
        (globalFredholmNormalization_targetDefect_isModuleCompact T hSource hTarget) hE hF)) at h
  exact h

variable [TopologicalSpace.SeparableSpace B]

-- Use the same original coefficient-inner-product norms as the actual
-- augmentation cycle isomorphism. Their dictionaries are Mathlib's native ones.
local instance globalFredholmClassAugmentationSourceNorm :
    NormedAddCommGroup
      (HilbertModuleSum B (HilbertModuleSum B E F)
        (HilbertModuleSum B (StandardCountableHilbertModule B)
          (StandardCountableHilbertModule B))) :=
  WithCStarModule.instNormedAddCommGroupProd (A := Bᵐᵒᵖ)
    (E := HilbertModuleSum B E F)
    (F := HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B))

local instance globalFredholmClassAugmentationTargetNorm :
    NormedAddCommGroup
      (HilbertModuleSum B (HilbertModuleSum B E (StandardCountableHilbertModule B))
        (HilbertModuleSum B F (StandardCountableHilbertModule B))) :=
  WithCStarModule.instNormedAddCommGroupProd (A := Bᵐᵒᵖ)
    (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
    (F := HilbertModuleSum B F (StandardCountableHilbertModule B))

/-- Augmentation by the actual standard identity map adds a degenerate cycle. -/
theorem globalFredholmAugmentation_class (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) (augmentedRectangularFredholm T)
        (augmentedRectangularFredholm_source_defect T hSource)
        (augmentedRectangularFredholm_target_defect T hTarget)
        (hE.sum standardCountableHilbertModule_isCountablyGenerated)
        (hF.sum standardCountableHilbertModule_isCountablyGenerated))) := by
  have hZero := KasparovHomotopyClass.mk_eq_zero_of_degenerate
    (BundledKasparovCycle.of (standardIdentityFredholmCycle (B := B)))
    (standardIdentityFredholmCycle_isDegenerate (B := B))
  calc
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF)) +
        KasparovHomotopyClass.mk (BundledKasparovCycle.of (standardIdentityFredholmCycle (B := B))) := by
      rw [hZero, add_zero]
    _ = KasparovHomotopyClass.mk
        ((BundledKasparovCycle.of (globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF)).directSum
          (BundledKasparovCycle.of (standardIdentityFredholmCycle (B := B)))) :=
      (KasparovHomotopyClass.mk_directSum _ _).symm
    _ = _ := KasparovHomotopyClass.mk_eq_of_iso
      (c := BundledKasparovCycle.of _) (d := BundledKasparovCycle.of _)
      (globalFredholmAugmentationCycleIso T hSource hTarget hE hF)

/-- The actual homogeneous stabilization preserves the augmented full class. -/
theorem globalFredholmStandardStabilization_class (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) (standardStabilizedRectangularFredholm T hE hF)
        (standardStabilizedRectangularFredholm_source_defect T hE hF hSource)
        (standardStabilizedRectangularFredholm_target_defect T hE hF hTarget)
        standardCountableHilbertModule_isCountablyGenerated standardCountableHilbertModule_isCountablyGenerated)) :=
  (globalFredholmAugmentation_class T hSource hTarget hE hF).trans
    (KasparovHomotopyClass.mk_eq_of_iso
      (c := BundledKasparovCycle.of _) (d := BundledKasparovCycle.of _)
      (globalFredholmStandardStabilizationCycleIso T hSource hTarget hE hF))

/-- The actual Julia relative cycle of the normalized constructed standard map. -/
def standardRectangularJuliaRelativeCycle (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :=
  relativeProjectionCycle (Γ := PUnit) (standardRectangularJuliaProjection T hE hF)
    juliaReferenceProjection (standardRectangularJuliaProjection_isStarProjection T hE hF)
    juliaReferenceProjection_isStarProjection
    (juliaFredholmProjection_difference_isModuleCompact
      (normalizedStandardRectangularFredholm T hE hF) (norm_globalFredholmNormalization_le _)
      (globalFredholmNormalization_sourceDefect_isModuleCompact _
        (standardStabilizedRectangularFredholm_source_defect T hE hF hSource))
      (globalFredholmNormalization_targetDefect_isModuleCompact _
        (standardStabilizedRectangularFredholm_source_defect T hE hF hSource)
        (standardStabilizedRectangularFredholm_target_defect T hE hF hTarget)))
    (IsCountablyGeneratedModule.sum
      (standardCountableHilbertModule_isCountablyGenerated (B := B))
      (standardCountableHilbertModule_isCountablyGenerated (B := B)))

/-- The normalized actual Julia range unitaries close the pointwise class bridge. -/
theorem globalFredholmStandardJulia_class (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (standardRectangularJuliaRelativeCycle T hSource hTarget hE hF)) := by
  apply (globalFredholmStandardStabilization_class T hSource hTarget hE hF).trans
  apply (globalFredholmNormalization_class (standardStabilizedRectangularFredholm T hE hF)
    (standardStabilizedRectangularFredholm_source_defect T hE hF hSource)
    (standardStabilizedRectangularFredholm_target_defect T hE hF hTarget)
    standardCountableHilbertModule_isCountablyGenerated standardCountableHilbertModule_isCountablyGenerated).trans
  exact KasparovHomotopyClass.mk_eq_of_iso
    (c := BundledKasparovCycle.of _) (d := BundledKasparovCycle.of _)
    (globalFredholmJuliaCycleIso (Γ := PUnit) (normalizedStandardRectangularFredholm T hE hF)
      (norm_globalFredholmNormalization_le _)
      (globalFredholmNormalization_sourceDefect_isModuleCompact _
        (standardStabilizedRectangularFredholm_source_defect T hE hF hSource))
      (globalFredholmNormalization_targetDefect_isModuleCompact _
        (standardStabilizedRectangularFredholm_source_defect T hE hF hSource)
        (standardStabilizedRectangularFredholm_target_defect T hE hF hTarget))
      standardCountableHilbertModule_isCountablyGenerated standardCountableHilbertModule_isCountablyGenerated)

/-- The original ordinary scalar cycle has the constructed standard Julia
relative cycle in its full class, through the actual support and grading splits. -/
theorem scalarStandardJulia_class
    (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B) E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (standardRectangularJuliaRelativeCycle c.scalarRectangularFredholm
        c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
        c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated)) :=
  c.scalarRectangularFredholm_class.trans
    (globalFredholmStandardJulia_class c.scalarRectangularFredholm
      c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
      c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated)

end BC4lean.KKTheory
