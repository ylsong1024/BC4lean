import BC4lean.RectangularFredholmStandardStabilization

/-! # Exact cycle isomorphisms for homogeneous standard stabilization

The summands are reordered by an actual coefficient-inner-product unitary.
This identifies augmentation by the standard identity Fredholm map with the
direct sum of the original cycle and its proved degenerate identity cycle.
The two constructed stabilization unitaries then identify the augmented cycle
with the transported standard cycle, intertwining every part of the data.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F G H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- The actual exchange of the middle summands. -/
def fredholmHomogeneousShuffle :
    HilbertModuleEquiv B (HilbertModuleSum B (HilbertModuleSum B E F) (HilbertModuleSum B G H))
      (HilbertModuleSum B (HilbertModuleSum B E G) (HilbertModuleSum B F H)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)
          invFun := fun x => sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      norm_map' := fun x => by
        change ‖sumMk (B := B) (sumMk (B := B) x.fst.fst x.snd.fst) (sumMk (B := B) x.fst.snd x.snd.snd)‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
          (sumMk (B := B) (sumMk (B := B) x.fst.fst x.snd.fst) (sumMk (B := B) x.fst.snd x.snd.snd))]
        have hi : ⟪sumMk (B := B) (sumMk (B := B) x.fst.fst x.snd.fst) (sumMk (B := B) x.fst.snd x.snd.snd),
            sumMk (B := B) (sumMk (B := B) x.fst.fst x.snd.fst) (sumMk (B := B) x.fst.snd x.snd.snd)⟫_(Bᵐᵒᵖ) = ⟪x, x⟫_(Bᵐᵒᵖ) := by
          simp only [inner_sum, sumMk_fst, sumMk_snd]
          abel
        rw [hi]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := fun x y => by
    change ⟪sumMk (B := B) (sumMk (B := B) x.fst.fst x.snd.fst)
        (sumMk (B := B) x.fst.snd x.snd.snd),
      sumMk (B := B) (sumMk (B := B) y.fst.fst y.snd.fst)
        (sumMk (B := B) y.fst.snd y.snd.snd)⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
    simp only [inner_sum, sumMk_fst, sumMk_snd]
    abel

@[simp] theorem fredholmHomogeneousShuffle_apply
    (x : HilbertModuleSum B (HilbertModuleSum B E F) (HilbertModuleSum B G H)) :
    fredholmHomogeneousShuffle x =
      sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd) := rfl

variable [CompleteSpace E] [CompleteSpace F] [TopologicalSpace.SeparableSpace B]

-- Pin the same native coefficient-inner-product norm dictionaries already used
-- by HilbertModuleSum. No ordinary product norm or alternative cycle data is used.
local instance globalFredholmAugmentationSourceNorm :
    NormedAddCommGroup
      (HilbertModuleSum B (HilbertModuleSum B E F)
        (HilbertModuleSum B (StandardCountableHilbertModule B)
          (StandardCountableHilbertModule B))) :=
  WithCStarModule.instNormedAddCommGroupProd (A := Bᵐᵒᵖ)
    (E := HilbertModuleSum B E F)
    (F := HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B))

local instance globalFredholmAugmentationTargetNorm :
    NormedAddCommGroup
      (HilbertModuleSum B (HilbertModuleSum B E (StandardCountableHilbertModule B))
        (HilbertModuleSum B F (StandardCountableHilbertModule B))) :=
  WithCStarModule.instNormedAddCommGroupProd (A := Bᵐᵒᵖ)
    (E := HilbertModuleSum B E (StandardCountableHilbertModule B))
    (F := HilbertModuleSum B F (StandardCountableHilbertModule B))

/-- Augmentation by the standard identity map is exactly a direct sum with
the constructed degenerate standard identity cycle, after the actual shuffle. -/
def globalFredholmAugmentationCycleIso (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovCycleIso
      ((globalFredholmScalarCycle (Γ := PUnit) T hSource hTarget hE hF).directSum
        (standardIdentityFredholmCycle (B := B)))
      (globalFredholmScalarCycle (Γ := PUnit) (augmentedRectangularFredholm T)
        (augmentedRectangularFredholm_source_defect T hSource)
        (augmentedRectangularFredholm_target_defect T hTarget)
        (hE.sum standardCountableHilbertModule_isCountablyGenerated)
        (hF.sum standardCountableHilbertModule_isCountablyGenerated)) where
  moduleEquiv := fredholmHomogeneousShuffle
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine z x := by
    change fredholmHomogeneousShuffle
      (sumMap (scalarModuleRepresentation z) (scalarModuleRepresentation z) x) =
        scalarModuleRepresentation z (fredholmHomogeneousShuffle x)
    simp only [sumMap_apply, scalarModuleRepresentation_apply, fredholmHomogeneousShuffle_apply,
      sumMk_fst, sumMk_snd]
    rfl
  operator_intertwine x := by
    have hOne : (1 : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)).adjoint = 1 := rfl
    change fredholmHomogeneousShuffle
      (sumMap (offDiagonalAdjointable T) (offDiagonalAdjointable 1) x) =
        offDiagonalAdjointable (augmentedRectangularFredholm T) (fredholmHomogeneousShuffle x)
    simp only [sumMap_apply, offDiagonalAdjointable_apply, fredholmHomogeneousShuffle_apply,
      sumMk_fst, sumMk_snd, augmentedRectangularFredholm, sumMap_adjoint,
      hOne, AdjointableMap.one_apply]

/-- The actual constructed homogeneous stabilization unitaries intertwine
the augmented scalar cycle with its transported standard rectangular cycle. -/
def globalFredholmStandardStabilizationCycleIso (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovCycleIso
      (globalFredholmScalarCycle (Γ := PUnit) (augmentedRectangularFredholm T)
        (augmentedRectangularFredholm_source_defect T hSource)
        (augmentedRectangularFredholm_target_defect T hTarget)
        (hE.sum standardCountableHilbertModule_isCountablyGenerated)
        (hF.sum standardCountableHilbertModule_isCountablyGenerated))
      (globalFredholmScalarCycle (Γ := PUnit) (standardStabilizedRectangularFredholm T hE hF)
        (standardStabilizedRectangularFredholm_source_defect T hE hF hSource)
        (standardStabilizedRectangularFredholm_target_defect T hE hF hTarget)
        standardCountableHilbertModule_isCountablyGenerated standardCountableHilbertModule_isCountablyGenerated) where
  moduleEquiv := rectangularStandardGradedStabilization hE hF
  grading_intertwine := rectangularStandardGradedStabilization_grading_intertwine hE hF
  action_intertwine _ _ := rfl
  representation_intertwine z x := by
    change rectangularStandardGradedStabilization hE hF (z • x) =
      z • rectangularStandardGradedStabilization hE hF x
    exact HilbertModuleEquiv.map_smul _ z x
  operator_intertwine x := by
    change rectangularStandardGradedStabilization hE hF
      (offDiagonalAdjointable (augmentedRectangularFredholm T) x) =
        offDiagonalAdjointable (standardStabilizedRectangularFredholm T hE hF)
          (rectangularStandardGradedStabilization hE hF x)
    simp only [rectangularStandardGradedStabilization, HilbertModuleEquiv.sum_apply,
      offDiagonalAdjointable_apply, sumMk_fst, sumMk_snd, standardStabilizedRectangularFredholm,
      HilbertModuleEquiv.transportMap_apply, HilbertModuleEquiv.transportMap_adjoint,
      HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
