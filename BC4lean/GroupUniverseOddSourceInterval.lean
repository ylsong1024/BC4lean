import BC4lean.CliffordOddSourceCycleIso
import BC4lean.FullCliffordParityHomotopy
import BC4lean.HilbertModuleFibreSum
import BC4lean.GroupUniverseEvenBase

/-! # Independent-universe actual odd source full interval construction

The module is the genuine sum of the original arbitrary interval module
with itself. Its completed evaluated fibre is identified with the sum of
the two actual fibres by the full coefficient-valued sum-fibre unitary.
-/

noncomputable section
universe uΓ uB uC uE uM
namespace BC4lean.KKTheory
namespace GroupUniverseOddSourceCycle
open CliffordOddSourceCycle
open scoped InnerProductSpace

variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} {M : Type uM} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, C)ᵐᵒᵖ M] [CStarModule C(unitInterval, C)ᵐᵒᵖ M] [CompleteSpace M]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

local instance groupUniverseOddSourceIntervalLocalInstance1 : CompleteSpace (HilbertModuleSum C(unitInterval, C) M M) :=
  hilbertModuleSum_complete

/-- The same actual cycle, with the pointwise trivial coefficient grading. -/
def intervalCycle (c : OddKasparovCycle β (γ.continuousSections (X := unitInterval)) M) :
    GradedKasparovCycle (cliffordCoefficientAction β) (γ.continuousSections (X := unitInterval))
      cliffordCoefficientGrading
      (CStarGrading.trivial : CStarGrading C).continuousSections
      (HilbertModuleSum C(unitInterval, C) M M) where
  sourceAction_preservesGrading := (cycle c).sourceAction_preservesGrading
  coefficientAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_continuousSections γ.preservesGrading_trivial
  countablyGenerated := (cycle c).countablyGenerated
  grading :=
    { grading := (cycle c).grading.grading
      involutive := (cycle c).grading.involutive
      inner_grading x y := by
        change ⟪(cycle c).grading.grading x, (cycle c).grading.grading y⟫_(C(unitInterval, C)ᵐᵒᵖ) =
          MulOpposite.op ((CStarGrading.trivial : CStarGrading C).continuousSections.automorphism
            (MulOpposite.unop ⟪x, y⟫_(C(unitInterval, C)ᵐᵒᵖ)))
        rw [GroupUniverseEvenBase.trivialSectionAutomorphism, MulOpposite.op_unop]
        exact (cycle c).grading.inner_grading x y }
  groupAction := (cycle c).groupAction
  grading_preserved := (cycle c).grading_preserved
  representation := (cycle c).representation
  representation_graded := (cycle c).representation_graded
  representation_equivariant := (cycle c).representation_equivariant
  operator := (cycle c).operator
  operator_odd := (cycle c).operator_odd
  selfadjoint_mod_compact := (cycle c).selfadjoint_mod_compact
  square_mod_compact := (cycle c).square_mod_compact
  commutator_compact := (cycle c).commutator_compact
  equivariance_mod_compact := (cycle c).equivariance_mod_compact

/- Prove each original whole-cycle field separately with the full native fibre
and independent Γ/B/C/M universes. Each field retains its original proof and
the default finite elaboration budget; the final structure only assembles them. -/

private theorem groupUniverseOddSourceIntervalFibre_grading_intertwine
    (c : OddKasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval)
    (z : HilbertModuleFibre C (HilbertModuleSum C(unitInterval, C) M M) t) :
    hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t (((intervalCycle c).fibre t).grading.grading z) =
      (cycle (c.fibre t)).grading.grading (hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := HilbertModuleSum C(unitInterval, C) M M) t z
  rw [GradedKasparovCycle.fibre_grading_mk]
  change hilbertModuleFibreSumEquiv t
    (hilbertModuleFibreMk (B := C) t (sumMk x.snd x.fst)) = _
  rw [hilbertModuleFibreSumEquiv_mk, hilbertModuleFibreSumEquiv_mk]
  rfl

private theorem groupUniverseOddSourceIntervalFibre_action_intertwine
    (c : OddKasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) (g : Γ)
    (z : HilbertModuleFibre C (HilbertModuleSum C(unitInterval, C) M M) t) :
    hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t (((intervalCycle c).fibre t).groupAction.action g z) =
      (cycle (c.fibre t)).groupAction.action g (hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := HilbertModuleSum C(unitInterval, C) M M) t z
  rw [GradedKasparovCycle.fibre_action_mk]
  change hilbertModuleFibreSumEquiv t
    (hilbertModuleFibreMk (B := C) t
      (sumMk (c.groupAction.action g x.fst) (c.groupAction.action g x.snd))) = _
  rw [hilbertModuleFibreSumEquiv_mk, hilbertModuleFibreSumEquiv_mk]
  apply Prod.ext <;> exact (c.fibre_action_mk t g _).symm

private theorem groupUniverseOddSourceIntervalFibre_representation_intertwine
    (c : OddKasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) (b : B × B)
    (z : HilbertModuleFibre C (HilbertModuleSum C(unitInterval, C) M M) t) :
    hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t (((intervalCycle c).fibre t).representation b z) =
      (cycle (c.fibre t)).representation b (hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := HilbertModuleSum C(unitInterval, C) M M) t z
  rw [GradedKasparovCycle.fibre_representation_mk]
  change hilbertModuleFibreSumEquiv t
    (hilbertModuleFibreMk (B := C) t
      (sumMap (c.representation b.1) (c.representation b.2) x)) =
    sumMap ((c.fibre t).representation b.1) ((c.fibre t).representation b.2)
      (hilbertModuleFibreSumEquiv t (hilbertModuleFibreMk (B := C) t x))
  rw [sumMap_apply, hilbertModuleFibreSumEquiv_mk,
    hilbertModuleFibreSumEquiv_mk, sumMap_apply]
  apply Prod.ext
  · exact (c.fibre_representation_mk t b.1 x.fst).symm
  · exact (c.fibre_representation_mk t b.2 x.snd).symm

private theorem groupUniverseOddSourceIntervalFibre_operator_intertwine
    (c : OddKasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval)
    (z : HilbertModuleFibre C (HilbertModuleSum C(unitInterval, C) M M) t) :
    hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t (((intervalCycle c).fibre t).operator z) =
      (cycle (c.fibre t)).operator (hilbertModuleFibreSumEquiv (B := C) (M := M) (N := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := HilbertModuleSum C(unitInterval, C) M M) t z
  rw [GradedKasparovCycle.fibre_operator_mk]
  change hilbertModuleFibreSumEquiv t
    (hilbertModuleFibreMk (B := C) t
      (operator c.operator x)) =
    operator (c.fibre t).operator
      (hilbertModuleFibreSumEquiv t (hilbertModuleFibreMk (B := C) t x))
  rw [operator_apply, hilbertModuleFibreSumEquiv_mk,
    hilbertModuleFibreSumEquiv_mk, operator_apply]
  apply Prod.ext <;>
    simp only [sumMk_fst, sumMk_snd, map_smul,
      OddKasparovCycle.fibre_operator_mk]

/-- The genuine completed sum-fibre unitary intertwines the full signed cycle. -/
def intervalFibreIso
    (c : OddKasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) :
    GradedKasparovCycleIso ((intervalCycle c).fibre t) (cycle (c.fibre t)) where
  moduleEquiv := hilbertModuleFibreSumEquiv t
  grading_intertwine := groupUniverseOddSourceIntervalFibre_grading_intertwine c t
  action_intertwine := groupUniverseOddSourceIntervalFibre_action_intertwine c t
  representation_intertwine := groupUniverseOddSourceIntervalFibre_representation_intertwine c t
  operator_intertwine := groupUniverseOddSourceIntervalFibre_operator_intertwine c t

end GroupUniverseOddSourceCycle

namespace GroupUniverseOddSourceCycle

variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {c d : BundledOddKasparovCycle.{uΓ,uB,uC,uE} β γ}

/-- Construct a genuine full signed Clifford-source witness from the same
arbitrary odd interval witness and its actual whole-cycle endpoint unitaries. -/
def full (h : FullOddKasparovHomotopy c d) :
    FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (CliffordOddSourceCycle.cycle c.cycle))
      (BundledGradedKasparovCycle.of (CliffordOddSourceCycle.cycle d.cycle)) where
  intervalCycle := BundledGradedKasparovCycle.of
    (GroupUniverseOddSourceCycle.intervalCycle h.intervalCycle.cycle)
  sourceIso := (GroupUniverseOddSourceCycle.intervalFibreIso h.intervalCycle.cycle 0).trans
    (CliffordOddSourceCycle.iso h.sourceIso)
  targetIso := (GroupUniverseOddSourceCycle.intervalFibreIso h.intervalCycle.cycle 1).trans
    (CliffordOddSourceCycle.iso h.targetIso)

end GroupUniverseOddSourceCycle
end BC4lean.KKTheory
