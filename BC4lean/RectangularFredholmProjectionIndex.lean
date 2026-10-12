import BC4lean.RectangularFredholmNormalizationNaturality
import BC4lean.RectangularFredholmStandardStabilization
import BC4lean.StandardCountableRelativeProjectionConjugation

/-! # The genuine rectangular Fredholm K₀ index and absorption independence

The index is the actual cutoff-independent scalar-kernel class of the
normalized Julia projection. Changing either actual stabilization unitary
conjugates that whole projection by a reference-preserving block unitary.
The proved doubled rotation and reference-augmentation cancellation remove
that conjugation. No contractibility of the multiplier unitary group and no
comparison isomorphism are assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

section Unitary
variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- A genuine module automorphism gives a genuine unitary operator. -/
def HilbertModuleEquiv.endUnitary (u : HilbertModuleEquiv B E E) : unitary (AdjointableMap B E E) :=
  ⟨u.toAdjointable, by
    constructor
    · apply AdjointableMap.ext
      intro x
      exact u.symm_apply_apply x
    · apply AdjointableMap.ext
      intro x
      exact u.apply_symm_apply x⟩

end Unitary

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
local notation "Std" => StandardCountableHilbertModule B
local notation "StdPair" => HilbertModuleSum B Std Std
local notation "StdOp" => AdjointableMap B Std Std
local notation "StdEnd" => AdjointableMap B StdPair StdPair

/-- The normalized actual standard Julia projection is a relative projection. -/
def standardNormalizedFredholmJuliaProjection (T : StdOp) : StdEnd :=
  juliaFredholmProjection (globalFredholmNormalization T)

theorem standardNormalizedFredholmJuliaProjection_isStarProjection (T : StdOp) :
    IsStarProjection (standardNormalizedFredholmJuliaProjection T) :=
  juliaFredholmProjection_isStarProjection _ (norm_globalFredholmNormalization_le _)

theorem standardNormalizedFredholmJuliaProjection_compact (T : StdOp)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact (standardNormalizedFredholmJuliaProjection T - standardCountablePairedReferenceProjection) := by
  have hReference : juliaReferenceProjection (B := B) (E := Std) (F := Std) =
      standardCountablePairedReferenceProjection := by
    ext x
    change juliaReferenceProjection (B := B) (E := Std) (F := Std) x =
      sumMap (0 : StdOp) (1 : StdOp) x
    rw [juliaReferenceProjection_apply, sumMap_apply, AdjointableMap.coe_zero_apply,
      AdjointableMap.one_apply]
  have hCompact := juliaFredholmProjection_difference_isModuleCompact
    (globalFredholmNormalization T)
    (norm_globalFredholmNormalization_le _)
    (globalFredholmNormalization_sourceDefect_isModuleCompact T hs)
    (globalFredholmNormalization_targetDefect_isModuleCompact T hs ht)
  simpa only [hReference, standardNormalizedFredholmJuliaProjection] using hCompact

/-- The actual scalar-kernel index of a standard rectangular Fredholm map. -/
def standardNormalizedRectangularFredholmIndex (T : StdOp)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1)) : OperatorK0 B :=
  standardCountableRelativeProjectionIndex (standardNormalizedFredholmJuliaProjection T)
    (standardNormalizedFredholmJuliaProjection_isStarProjection T)
    (standardNormalizedFredholmJuliaProjection_compact T hs ht)

/-- Source and target unitaries preserve the actual standard rectangular index. -/
theorem standardNormalizedRectangularFredholmIndex_transport
    (u v : HilbertModuleEquiv B Std Std) (T : StdOp)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1))
    (hs' : IsModuleCompact (1 - (u.transportMap v T).adjoint.comp (u.transportMap v T)))
    (ht' : IsModuleCompact ((u.transportMap v T).comp (u.transportMap v T).adjoint - 1)) :
    standardNormalizedRectangularFredholmIndex (u.transportMap v T) hs' ht' =
      standardNormalizedRectangularFredholmIndex T hs ht := by
  let W := (u.sum v).endUnitary
  have hReference : Commute (W : StdEnd) standardCountablePairedReferenceProjection := by
    apply AdjointableMap.ext
    intro x
    change ((u.sum v).toAdjointable * sumMap (0 : StdOp) (1 : StdOp)) x =
      (sumMap (0 : StdOp) (1 : StdOp) * (u.sum v).toAdjointable) x
    simp only [AdjointableMap.mul_apply, HilbertModuleEquiv.toAdjointable_apply,
      HilbertModuleEquiv.sum_apply, sumMap_apply, AdjointableMap.coe_zero_apply,
      AdjointableMap.one_apply, sumMk_fst, sumMk_snd, HilbertModuleEquiv.map_zero]
  have hProj : standardNormalizedFredholmJuliaProjection (u.transportMap v T) =
      standardRelativeProjectionConjugate W (standardNormalizedFredholmJuliaProjection T) := by
    unfold standardNormalizedFredholmJuliaProjection
    rw [globalFredholmNormalization_transport, juliaFredholmProjection_transport u v
      (globalFredholmNormalization T) (norm_globalFredholmNormalization_le T)]
    apply AdjointableMap.ext
    intro x
    rfl
  unfold standardNormalizedRectangularFredholmIndex
  simpa only [hProj] using standardCountableRelativeProjectionIndex_conjugation W
    (standardNormalizedFredholmJuliaProjection T)
    (standardNormalizedFredholmJuliaProjection_isStarProjection T) hReference
    (standardNormalizedFredholmJuliaProjection_compact T hs ht)

section Arbitrary
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

theorem rectangularTransport_source_defect_compact
    {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    [CompleteSpace E] [CompleteSpace F]
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (v : HilbertModuleEquiv B F (StandardCountableHilbertModule B)) (T : AdjointableMap B E F)
    (hs : IsModuleCompact (1 - T.adjoint.comp T)) :
    IsModuleCompact (1 - (u.transportMap v T).adjoint.comp (u.transportMap v T)) := by
  have h := u.transportMap_isModuleCompact u hs
  change IsModuleCompact (u.transport (1 - T.adjoint.comp T)) at h
  simpa only [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
    ← HilbertModuleEquiv.transportMap_source_square u v T] using h

theorem rectangularTransport_target_defect_compact
    {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    [CompleteSpace E] [CompleteSpace F]
    (u : HilbertModuleEquiv B E (StandardCountableHilbertModule B))
    (v : HilbertModuleEquiv B F (StandardCountableHilbertModule B)) (T : AdjointableMap B E F)
    (ht : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact ((u.transportMap v T).comp (u.transportMap v T).adjoint - 1) := by
  have h := v.transportMap_isModuleCompact v ht
  change IsModuleCompact (v.transport (T.comp T.adjoint - 1)) at h
  simpa only [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
    ← HilbertModuleEquiv.transportMap_target_square u v T] using h

/-- This intermediate definition accepts actual unitary identifications. -/
def rectangularFredholmIndexWith (T : AdjointableMap B E F)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1))
    (u : HilbertModuleEquiv B E Std) (v : HilbertModuleEquiv B F Std) : OperatorK0 B :=
  standardNormalizedRectangularFredholmIndex (u.transportMap v T)
    (rectangularTransport_source_defect_compact u v T hs)
    (rectangularTransport_target_defect_compact u v T ht)

/-- Two actual identifications give the same genuine scalar-kernel index. -/
theorem rectangularFredholmIndexWith_independent (T : AdjointableMap B E F)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1))
    (u₁ u₂ : HilbertModuleEquiv B E Std) (v₁ v₂ : HilbertModuleEquiv B F Std) :
    rectangularFredholmIndexWith T hs ht u₁ v₁ = rectangularFredholmIndexWith T hs ht u₂ v₂ := by
  let u := u₁.symm.trans u₂
  let v := v₁.symm.trans v₂
  have hT : u.transportMap v (u₁.transportMap v₁ T) = u₂.transportMap v₂ T := by
    apply AdjointableMap.ext
    intro x
    change v₂ (v₁.symm (v₁ (T (u₁.symm (u₁ (u₂.symm x)))))) = v₂ (T (u₂.symm x))
    rw [HilbertModuleEquiv.symm_apply_apply, HilbertModuleEquiv.symm_apply_apply]
  unfold rectangularFredholmIndexWith
  have hIndex := standardNormalizedRectangularFredholmIndex_transport u v (u₁.transportMap v₁ T)
    (rectangularTransport_source_defect_compact u₁ v₁ T hs)
    (rectangularTransport_target_defect_compact u₁ v₁ T ht)
    (rectangularTransport_source_defect_compact u v (u₁.transportMap v₁ T)
      (rectangularTransport_source_defect_compact u₁ v₁ T hs))
    (rectangularTransport_target_defect_compact u v (u₁.transportMap v₁ T)
      (rectangularTransport_target_defect_compact u₁ v₁ T ht))
  simpa only [hT] using hIndex.symm

/-- The actual constructed frame stabilization defines an index for every
countably generated rectangular Fredholm map over possibly nonunital B. -/
def rectangularFredholmIndex (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1)) : OperatorK0 B :=
  rectangularFredholmIndexWith (augmentedRectangularFredholm T)
    (augmentedRectangularFredholm_source_defect T hs)
    (augmentedRectangularFredholm_target_defect T ht)
    (standardModuleStabilization hE) (standardModuleStabilization hF)

/-- Any actual pair of absorption maps may be used for the same index. -/
theorem rectangularFredholmIndex_absorption_independent (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1))
    (u : HilbertModuleEquiv B (HilbertModuleSum B E Std) Std)
    (v : HilbertModuleEquiv B (HilbertModuleSum B F Std) Std) :
    rectangularFredholmIndex T hE hF hs ht =
      rectangularFredholmIndexWith (augmentedRectangularFredholm T)
        (augmentedRectangularFredholm_source_defect T hs)
        (augmentedRectangularFredholm_target_defect T ht) u v :=
  rectangularFredholmIndexWith_independent _ _ _ _ u _ v


variable {E' F' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℂ F'] [SMul Bᵐᵒᵖ F'] [CStarModule Bᵐᵒᵖ F'] [CompleteSpace F']

/-- Whole rectangular unitary transport preserves the selected actual index. -/
theorem rectangularFredholmIndex_transport (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F)
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hE' : IsCountablyGeneratedModule B E') (hF' : IsCountablyGeneratedModule B F')
    (hs : IsModuleCompact (1 - T.adjoint.comp T)) (ht : IsModuleCompact (T.comp T.adjoint - 1))
    (hs' : IsModuleCompact (1 - (u.transportMap v T).adjoint.comp (u.transportMap v T)))
    (ht' : IsModuleCompact ((u.transportMap v T).comp (u.transportMap v T).adjoint - 1)) :
    rectangularFredholmIndex T hE hF hs ht =
      rectangularFredholmIndex (u.transportMap v T) hE' hF' hs' ht' := by
  let uAug := u.sum (HilbertModuleEquiv.refl (B := B) (E := Std))
  let vAug := v.sum (HilbertModuleEquiv.refl (B := B) (E := Std))
  let a := uAug.trans (standardModuleStabilization hE')
  let b := vAug.trans (standardModuleStabilization hF')
  have hOperator : a.transportMap b (augmentedRectangularFredholm T) =
      standardStabilizedRectangularFredholm (u.transportMap v T) hE' hF' := by
    apply AdjointableMap.ext
    intro x
    simp only [a, b, uAug, vAug, standardStabilizedRectangularFredholm,
      HilbertModuleEquiv.transportMap_apply, augmentedRectangularFredholm,
      sumMap_apply, AdjointableMap.one_apply]
    rfl
  rw [rectangularFredholmIndex_absorption_independent T hE hF hs ht a b]
  unfold rectangularFredholmIndexWith
  simp only [hOperator, rectangularFredholmIndex, rectangularFredholmIndexWith,
    standardStabilizedRectangularFredholm]

end Arbitrary
end BC4lean.KKTheory
