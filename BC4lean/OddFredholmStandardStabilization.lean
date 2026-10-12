import BC4lean.StandardModuleStabilization
import BC4lean.OddFredholmStandardIntervalIndex
import BC4lean.OddKTheoryMatrixUnitaryCycle
import BC4lean.OddFredholmFullNormalization
import BC4lean.GroupULiftRawCycles

/-! # Actual standard stabilization of arbitrary scalar odd Fredholm modules

Augmentation adds a genuine degenerate identity cycle on H_B. The proved
standard-module absorption unitary transports its actual selfadjoint Fredholm
operator to End(H_B), where the genuine finite exponential index is defined.
The whole odd cycle isomorphisms prove preservation of the actual full class.
Independence of the selected absorption unitary is a further index obligation.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

def oddFredholmStandardAugmentedOperator (F : selfAdjoint (AdjointableMap B E E)) :
    AdjointableMap B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (HilbertModuleSum B E (StandardCountableHilbertModule B)) :=
  sumMap (F : AdjointableMap B E E) 1

omit [CompleteSpace E] in
theorem oddFredholmStandardAugmentedOperator_isSelfAdjoint
    (F : selfAdjoint (AdjointableMap B E E)) :
    IsSelfAdjoint (oddFredholmStandardAugmentedOperator F) := by
  show star (sumMap (F : AdjointableMap B E E) 1) = sumMap (F : AdjointableMap B E E) 1
  rw [← sumMap_star, F.property.star_eq, star_one]

omit [CompleteSpace E] in
theorem oddFredholmStandardAugmentedOperator_square_compact
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    IsModuleCompact (oddFredholmStandardAugmentedOperator F *
      oddFredholmStandardAugmentedOperator F - 1) := by
  have h := hF.sumMap (IsModuleCompact.zero (B := B)
    (E := StandardCountableHilbertModule B) (F := StandardCountableHilbertModule B))
  simpa only [oddFredholmStandardAugmentedOperator, ← sumMap_mul, ← sumMap_one,
    ← sumMap_sub, one_mul, sub_self] using h

def oddFredholmStandardStabilizedOperator (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E)) : selfAdjoint (OddFredholmStandardOperator B) :=
  ⟨(standardModuleStabilization hE).transport (oddFredholmStandardAugmentedOperator F),
    (oddFredholmStandardAugmentedOperator_isSelfAdjoint F).map
      (standardModuleStabilization hE).transportStarAlgEquiv.toStarAlgHom⟩

theorem oddFredholmStandardStabilizedOperator_square_compact
    (hE : IsCountablyGeneratedModule B E) (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddFredholmStandardStabilizedOperator hE F : OddFredholmStandardOperator B) *
      (oddFredholmStandardStabilizedOperator hE F : OddFredholmStandardOperator B) - 1) := by
  have h := (standardModuleStabilization hE).transportMap_isModuleCompact
    (standardModuleStabilization hE) (oddFredholmStandardAugmentedOperator_square_compact F hF)
  change IsModuleCompact ((standardModuleStabilization hE).transport
    (oddFredholmStandardAugmentedOperator F * oddFredholmStandardAugmentedOperator F - 1)) at h
  simpa only [oddFredholmStandardStabilizedOperator,
    HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_one] using h

/-- A genuine actual OperatorK1 value for any complete countably generated
selfadjoint scalar Fredholm module, via the constructed absorption unitary. -/
def oddFredholmStabilizedIndex (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) : OperatorKTheory.OperatorK1 B :=
  oddFredholmStandardIndex (oddFredholmStandardStabilizedOperator hE F)
    (by simpa only [pow_two] using oddFredholmStandardStabilizedOperator_square_compact hE F hF)

variable [TopologicalSpace.SeparableSpace B]

def oddFredholmStandardIdentityCycle :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (StandardCountableHilbertModule B) :=
  oddKTheoryScalarFredholmCycle (Γ := Γ) (B := B)
    (E := StandardCountableHilbertModule B)
    standardCountableHilbertModule_isCountablyGenerated (1 : OddFredholmStandardOperator B)
    (by change star (1 : OddFredholmStandardOperator B) = 1; exact star_one (OddFredholmStandardOperator B))
    (by simpa only [one_mul, sub_self] using
      (IsModuleCompact.zero (B := B) (E := StandardCountableHilbertModule B)
        (F := StandardCountableHilbertModule B)))

theorem oddFredholmStandardIdentityCycle_degenerate :
    (oddFredholmStandardIdentityCycle (Γ := Γ) (B := B)).IsDegenerate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp only [oddFredholmStandardIdentityCycle, oddKTheoryScalarFredholmCycle,
      star_one, sub_self, zero_mul]
  · intro a
    simp only [oddFredholmStandardIdentityCycle, oddKTheoryScalarFredholmCycle,
      one_mul, sub_self, zero_mul]
  · intro a
    simp only [oddFredholmStandardIdentityCycle, oddKTheoryScalarFredholmCycle,
      one_mul, mul_one, sub_self]
  · intro g a
    change ((EquivariantHilbertModule.trivial.conjugateOperator g (1 : OddFredholmStandardOperator B)) - 1) * _ = 0
    have h : EquivariantHilbertModule.trivial.conjugateOperator g
        (1 : OddFredholmStandardOperator B) = 1 := by ext x; rfl
    rw [h, sub_self, zero_mul]

def oddFredholmStandardAugmentedCycle (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :=
  oddKTheoryScalarFredholmCycle (Γ := Γ) (hE.sum standardCountableHilbertModule_isCountablyGenerated)
    (oddFredholmStandardAugmentedOperator F) (oddFredholmStandardAugmentedOperator_isSelfAdjoint F)
    (oddFredholmStandardAugmentedOperator_square_compact F hF)

set_option maxHeartbeats 1200000 in
def oddFredholmStandardStabilizedCycle (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :=
  oddKTheoryScalarFredholmCycle (Γ := Γ) (B := B)
    (E := StandardCountableHilbertModule B)
    standardCountableHilbertModule_isCountablyGenerated
    (oddFredholmStandardStabilizedOperator hE F : OddFredholmStandardOperator B)
    (show IsSelfAdjoint (oddFredholmStandardStabilizedOperator hE F : OddFredholmStandardOperator B)
      from (oddFredholmStandardStabilizedOperator hE F).property)
    (oddFredholmStandardStabilizedOperator_square_compact hE F hF)

def oddFredholmStandardAugmentationCycleIso (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    OddKasparovCycleIso
      ((oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF).directSum
        (oddFredholmStandardIdentityCycle (Γ := Γ) (B := B)))
      (oddFredholmStandardAugmentedCycle hE F hF) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine g x := rfl
  representation_intertwine a x := by
    change sumMap
      (scalarModuleRepresentation (B := B) (E := E) a)
      (scalarModuleRepresentation (B := B) (E := StandardCountableHilbertModule B) a) x =
        scalarModuleRepresentation (B := B) a x
    simp only [sumMap_apply, scalarModuleRepresentation_apply]
    rfl
  operator_intertwine x := rfl

def oddFredholmStandardStabilizationCycleIso (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    OddKasparovCycleIso (oddFredholmStandardAugmentedCycle (Γ := Γ) hE F hF)
      (oddFredholmStandardStabilizedCycle hE F hF) where
  moduleEquiv := standardModuleStabilization hE
  action_intertwine _ _ := rfl
  representation_intertwine a x := (standardModuleStabilization hE).map_smul a x
  operator_intertwine x := by
    change standardModuleStabilization hE (oddFredholmStandardAugmentedOperator F x) =
      (standardModuleStabilization hE).transport (oddFredholmStandardAugmentedOperator F)
        (standardModuleStabilization hE x)
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]

/-- The complete stabilization class equality lives in the common carrier
universe. Each original cycle is transported along its actual ULift unitary;
the coefficient and original module universes remain independent. -/
theorem oddFredholmStandardStabilizedCycle_class (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    OddKK.mk (BundledOddKasparovCycle.of
      ((oddFredholmStandardStabilizedCycle (Γ := Γ) hE F hF).ulift :
        OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
          (ULift.{uE} (StandardCountableHilbertModule B)))) =
      OddKK.mk (BundledOddKasparovCycle.of
        ((oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF).ulift :
          OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (ULift.{uB} E))) := by
  let c := oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF
  let d := oddFredholmStandardIdentityCycle (Γ := Γ) (B := B)
  let cu : OddKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (ULift.{uB} E) := c.ulift
  let du : OddKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
      (ULift.{uE} (StandardCountableHilbertModule B)) := d.ulift
  let su : OddKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
      (ULift.{uE} (StandardCountableHilbertModule B)) :=
    (oddFredholmStandardStabilizedCycle (Γ := Γ) hE F hF).ulift
  have hIso : OddKasparovCycleIso (cu.directSum du) su :=
    ((c.uliftIso : OddKasparovCycleIso c cu).symm.directSum
      (d.uliftIso : OddKasparovCycleIso d du).symm).trans
        ((oddFredholmStandardAugmentationCycleIso (Γ := Γ) hE F hF).trans
          ((oddFredholmStandardStabilizationCycleIso (Γ := Γ) hE F hF).trans
            ((oddFredholmStandardStabilizedCycle (Γ := Γ) hE F hF).uliftIso :
              OddKasparovCycleIso (oddFredholmStandardStabilizedCycle (Γ := Γ) hE F hF) su)))
  have hdu : du.IsDegenerate := d.ulift_isDegenerate
    (oddFredholmStandardIdentityCycle_degenerate (Γ := Γ) (B := B))
  change OddKK.mk (BundledOddKasparovCycle.of su) =
    OddKK.mk (BundledOddKasparovCycle.of cu)
  calc
    _ = OddKK.mk ((BundledOddKasparovCycle.of cu).directSum
        (BundledOddKasparovCycle.of du)) := OddKK.mk_eq_of_iso hIso.symm
    _ = _ := by
      rw [OddKK.mk_directSum,
        OddKK.mk_eq_zero_of_degenerate (BundledOddKasparovCycle.of du) hdu, add_zero]

end BC4lean.KKTheory
