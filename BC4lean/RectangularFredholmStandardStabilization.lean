import BC4lean.StandardModuleStabilization
import BC4lean.GlobalFredholmNormalization
import BC4lean.StandardCountableFiniteProjection
import BC4lean.GlobalFredholmScalarCycle

/-! # Actual homogeneous standard stabilization of rectangular Fredholm maps

Both genuine countably generated homogeneous modules are stabilized by the
proved frame/Julia absorption construction. The sum of the two actual unitary
maps preserves the positive/negative grading. Adding the identity on H_B and
transporting the rectangular map preserves both actual compact defects. Its
proved contraction normalization gives the actual Julia projection on H_B⊕H_B,
to which the genuine finite relative projection homotopy applies.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- Add the actual identity map on the standard module to a rectangular map. -/
def augmentedRectangularFredholm (T : AdjointableMap B E F) :
    AdjointableMap B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (HilbertModuleSum B F (StandardCountableHilbertModule B)) := sumMap T 1

omit [CompleteSpace E] [CompleteSpace F] in
theorem augmentedRectangularFredholm_source_defect (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T)) :
    IsModuleCompact (1 - (augmentedRectangularFredholm T).adjoint.comp (augmentedRectangularFredholm T)) := by
  have hOne : (1 : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)).adjoint = 1 := rfl
  have hEq : 1 - (augmentedRectangularFredholm T).adjoint.comp (augmentedRectangularFredholm T) =
      sumMap (1 - T.adjoint.comp T) (0 : AdjointableMap B
        (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) := by
    ext x
    apply Prod.ext <;> simp only [augmentedRectangularFredholm, sumMap_adjoint,
      AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
      sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_zero_apply,
      WithCStarModule.sub_fst, WithCStarModule.sub_snd, hOne, sub_self]
  rw [hEq]
  exact hSource.sumMap IsModuleCompact.zero

omit [CompleteSpace E] [CompleteSpace F] in
theorem augmentedRectangularFredholm_target_defect (T : AdjointableMap B E F)
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact ((augmentedRectangularFredholm T).comp (augmentedRectangularFredholm T).adjoint - 1) := by
  have hOne : (1 : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)).adjoint = 1 := rfl
  have hEq : (augmentedRectangularFredholm T).comp (augmentedRectangularFredholm T).adjoint - 1 =
      sumMap (T.comp T.adjoint - 1) (0 : AdjointableMap B
        (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) := by
    ext x
    apply Prod.ext <;> simp only [augmentedRectangularFredholm, sumMap_adjoint,
      AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
      sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_zero_apply,
      WithCStarModule.sub_fst, WithCStarModule.sub_snd, hOne, sub_self]
  rw [hEq]
  exact hTarget.sumMap IsModuleCompact.zero

/-- Both actual frame/Julia stabilization maps together give the canonical
graded stabilization of the augmented homogeneous modules. -/
def rectangularStandardGradedStabilization (hE : IsCountablyGeneratedModule B E)
    (hF : IsCountablyGeneratedModule B F) :=
  (standardModuleStabilization hE).sum (standardModuleStabilization hF)

section GradingIntertwining

-- Pin the existing native Hilbert-sum norm dictionary at the nested source.
-- This is the same product construction used by HilbertModuleSum itself.
local instance rectangularStandardStabilizationSourceNorm :
    NormedAddCommGroup
      (HilbertModuleSum B (HilbertModuleSum B E (StandardCountableHilbertModule B))
        (HilbertModuleSum B F (StandardCountableHilbertModule B))) :=
  WithCStarModule.instNormedAddCommGroupProd (A := Bᵐᵒᵖ)
    (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
    (F := HilbertModuleSum B F (StandardCountableHilbertModule B))

theorem rectangularStandardGradedStabilization_grading_intertwine
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (x : HilbertModuleSum B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (HilbertModuleSum B F (StandardCountableHilbertModule B))) :
    rectangularStandardGradedStabilization hE hF
        ((GradedHilbertModule.sum (B := B)
          (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
          (F := HilbertModuleSum B F (StandardCountableHilbertModule B))
          (GradedHilbertModule.trivial (B := B)
            (E := HilbertModuleSum B E (StandardCountableHilbertModule B)))
          (GradedHilbertModule.trivial (B := B)
            (E := HilbertModuleSum B F (StandardCountableHilbertModule B))).opposite).grading x) =
      (GradedHilbertModule.sum (B := B)
        (E := StandardCountableHilbertModule B) (F := StandardCountableHilbertModule B)
        (GradedHilbertModule.trivial (B := B) (E := StandardCountableHilbertModule B))
        (GradedHilbertModule.trivial (B := B)
          (E := StandardCountableHilbertModule B)).opposite).grading
        (rectangularStandardGradedStabilization hE hF x) := by
  change sumMk (standardModuleStabilization hE x.fst) (standardModuleStabilization hF (-x.snd)) =
    sumMk (standardModuleStabilization hE x.fst) (-(standardModuleStabilization hF x.snd))
  rw [HilbertModuleEquiv.map_neg]

end GradingIntertwining

/-- The actual transported rectangular operator on H_B. No stabilization
unitary is supplied as a hypothesis: both come from the proved construction. -/
def standardStabilizedRectangularFredholm (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B) :=
  (standardModuleStabilization hE).transportMap (standardModuleStabilization hF)
    (augmentedRectangularFredholm T)

theorem standardStabilizedRectangularFredholm_source_defect (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T)) :
    IsModuleCompact (1 - (standardStabilizedRectangularFredholm T hE hF).adjoint.comp
      (standardStabilizedRectangularFredholm T hE hF)) := by
  have hCompact := (standardModuleStabilization hE).transportMap_isModuleCompact
    (standardModuleStabilization hE) (augmentedRectangularFredholm_source_defect T hSource)
  have hEq : (standardModuleStabilization hE).transport
      (1 - (augmentedRectangularFredholm T).adjoint.comp (augmentedRectangularFredholm T)) =
      1 - (standardStabilizedRectangularFredholm T hE hF).adjoint.comp
        (standardStabilizedRectangularFredholm T hE hF) := by
    rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one]
    congr 1
    ext x
    simp only [standardStabilizedRectangularFredholm, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.transportMap_adjoint, HilbertModuleEquiv.transportMap_apply,
      AdjointableMap.comp_apply, HilbertModuleEquiv.symm_apply_apply]
  change IsModuleCompact ((standardModuleStabilization hE).transport
    (1 - (augmentedRectangularFredholm T).adjoint.comp (augmentedRectangularFredholm T))) at hCompact
  rwa [hEq] at hCompact

theorem standardStabilizedRectangularFredholm_target_defect (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact ((standardStabilizedRectangularFredholm T hE hF).comp
      (standardStabilizedRectangularFredholm T hE hF).adjoint - 1) := by
  have hCompact := (standardModuleStabilization hF).transportMap_isModuleCompact
    (standardModuleStabilization hF) (augmentedRectangularFredholm_target_defect T hTarget)
  have hEq : (standardModuleStabilization hF).transport
      ((augmentedRectangularFredholm T).comp (augmentedRectangularFredholm T).adjoint - 1) =
      (standardStabilizedRectangularFredholm T hE hF).comp
        (standardStabilizedRectangularFredholm T hE hF).adjoint - 1 := by
    rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one]
    congr 1
    ext x
    simp only [standardStabilizedRectangularFredholm, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.transportMap_adjoint, HilbertModuleEquiv.transportMap_apply,
      AdjointableMap.comp_apply, HilbertModuleEquiv.symm_apply_apply]
  change IsModuleCompact ((standardModuleStabilization hF).transport
    ((augmentedRectangularFredholm T).comp (augmentedRectangularFredholm T).adjoint - 1)) at hCompact
  rwa [hEq] at hCompact

/-- The actual normalized standard Fredholm operator. -/
def normalizedStandardRectangularFredholm (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :=
  globalFredholmNormalization (standardStabilizedRectangularFredholm T hE hF)

/-- The actual normalized Julia projection on the fixed canonical graded pair. -/
def standardRectangularJuliaProjection (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :=
  juliaFredholmProjection (normalizedStandardRectangularFredholm T hE hF)

theorem standardRectangularJuliaProjection_isStarProjection (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    IsStarProjection (standardRectangularJuliaProjection T hE hF) :=
  juliaFredholmProjection_isStarProjection _ (norm_globalFredholmNormalization_le _)

theorem standardRectangularJuliaProjection_sub_reference_isModuleCompact (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact (standardRectangularJuliaProjection T hE hF - standardCountablePairedReferenceProjection) := by
  have hS := standardStabilizedRectangularFredholm_source_defect T hE hF hSource
  have hT := standardStabilizedRectangularFredholm_target_defect T hE hF hTarget
  have hCompact := juliaFredholmProjection_difference_isModuleCompact
    (normalizedStandardRectangularFredholm T hE hF) (norm_globalFredholmNormalization_le _)
    (globalFredholmNormalization_sourceDefect_isModuleCompact _ hS)
    (globalFredholmNormalization_targetDefect_isModuleCompact _ hS hT)
  have hReference : juliaReferenceProjection (B := B) (E := StandardCountableHilbertModule B)
      (F := StandardCountableHilbertModule B) = standardCountablePairedReferenceProjection := by
    ext x
    change juliaReferenceProjection (B := B) (E := StandardCountableHilbertModule B)
        (F := StandardCountableHilbertModule B) x =
      sumMap (0 : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) (1 : AdjointableMap B
          (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) x
    rw [juliaReferenceProjection_apply, sumMap_apply, AdjointableMap.coe_zero_apply,
      AdjointableMap.one_apply]
  rwa [hReference] at hCompact

/-- The genuine stabilized Julia projection admits the constructed finite
relative unitization normalization. The finite coordinate dimension, matrix
projection, exact scalar part and continuous path are all derived. -/
theorem exists_standardRectangularFiniteProjectionHomotopy (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1)) :
    ∃ n : ℕ,
    ∃ M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B),
      IsStarProjection M ∧
      unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) ∧
      ∃ γ : Path (standardRectangularJuliaProjection T hE hF) (pairedStandardFiniteRelativeRealization n M),
        ∀ t : I, IsStarProjection (γ t) ∧
          IsModuleCompact (γ t - standardCountablePairedReferenceProjection) :=
  exists_standardCountableFiniteRelativeProjectionHomotopy (B := B) _
    (standardRectangularJuliaProjection_isStarProjection T hE hF)
    (standardRectangularJuliaProjection_sub_reference_isModuleCompact T hE hF hSource hTarget)

/-- The actual standard identity rectangular pair, available for separable
coefficients, is the degenerate cycle added during homogeneous stabilization. -/
def standardIdentityFredholmCycle [TopologicalSpace.SeparableSpace B] :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :=
  globalFredholmScalarCycle (Γ := PUnit) (1 : AdjointableMap B
    (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
    (by
      have hOne : (1 : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)).adjoint.comp
          (1 : AdjointableMap B (StandardCountableHilbertModule B)
            (StandardCountableHilbertModule B)) = 1 := by ext x; rfl
      rw [hOne, sub_self]
      exact IsModuleCompact.zero)
    (by
      have hOne : (1 : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)).comp (1 : AdjointableMap B
          (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)).adjoint = 1 := by ext x; rfl
      rw [hOne, sub_self]
      exact IsModuleCompact.zero)
    standardCountableHilbertModule_isCountablyGenerated standardCountableHilbertModule_isCountablyGenerated

theorem standardIdentityFredholmCycle_isDegenerate [TopologicalSpace.SeparableSpace B] :
    (standardIdentityFredholmCycle (B := B)).IsDegenerate := by
  have hSelf : star (offDiagonalAdjointable (1 : AdjointableMap B
      (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))) =
      offDiagonalAdjointable (1 : AdjointableMap B
        (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :=
    offDiagonalAdjointable_star _
  have hSquare : offDiagonalAdjointable (1 : AdjointableMap B
      (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) *
      offDiagonalAdjointable (1 : AdjointableMap B
        (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) = 1 := by
    ext x
    have hOne : (1 : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)).adjoint = 1 := rfl
    apply Prod.ext <;> simp only [AdjointableMap.mul_apply, offDiagonalAdjointable_apply,
      hOne, AdjointableMap.one_apply, sumMk_fst, sumMk_snd]
  constructor
  · intro z
    change (offDiagonalAdjointable (1 : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) - star (offDiagonalAdjointable
          (1 : AdjointableMap B (StandardCountableHilbertModule B)
            (StandardCountableHilbertModule B)))) * scalarModuleRepresentation z = 0
    rw [hSelf, sub_self, zero_mul]
  constructor
  · intro z
    change (offDiagonalAdjointable (1 : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) * offDiagonalAdjointable
          (1 : AdjointableMap B (StandardCountableHilbertModule B)
            (StandardCountableHilbertModule B)) - 1) * scalarModuleRepresentation z = 0
    rw [hSquare, sub_self, zero_mul]
  constructor
  · intro z
    ext x
    simp only [standardIdentityFredholmCycle, globalFredholmScalarCycle,
      AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, scalarModuleRepresentation_apply,
      AdjointableMap.coe_zero_apply]
    exact sub_eq_zero.mpr ((offDiagonalAdjointable (1 : AdjointableMap B
      (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))).toCLM.map_smul z x)
  · intro g z
    change ((EquivariantHilbertModule.trivial (Γ := PUnit) (B := B)
        (E := HilbertModuleSum B (StandardCountableHilbertModule B)
          (StandardCountableHilbertModule B))).conjugateOperator g
        (offDiagonalAdjointable (1 : AdjointableMap B (StandardCountableHilbertModule B)
          (StandardCountableHilbertModule B))) - offDiagonalAdjointable
            (1 : AdjointableMap B (StandardCountableHilbertModule B)
              (StandardCountableHilbertModule B))) * scalarModuleRepresentation z = 0
    have hTrivial : (EquivariantHilbertModule.trivial (Γ := PUnit)).conjugateOperator g
        (offDiagonalAdjointable (1 : AdjointableMap B
          (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))) =
        offDiagonalAdjointable (1 : AdjointableMap B
          (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) := by ext x; rfl
    rw [hTrivial, sub_self, zero_mul]

end BC4lean.KKTheory
