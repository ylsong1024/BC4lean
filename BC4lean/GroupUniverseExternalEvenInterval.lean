import BC4lean.CliffordExternalEvenCycleIso
import BC4lean.CliffordIntervalExpansionFibre
import BC4lean.GroupUniverseEvenBase

/-! # Independent-universe external even Clifford full interval transport

The interval carrier is the pair of the original arbitrary interval
module, transported along the actual continuous-product coefficient
equivalence. The completed fibre unitary is obtained from its full evaluated
inner product and genuine onto coordinate evaluation. No section-module or
fixed-module assumption is imposed on the original homotopy.
-/

noncomputable section
universe uΓ uB uC uE uM
namespace BC4lean.KKTheory
namespace GroupUniverseExternalEvenCycle
open CliffordExternalEvenCycle

variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} {M : Type uM} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, C)ᵐᵒᵖ M] [CStarModule C(unitInterval, C)ᵐᵒᵖ M] [CompleteSpace M]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

/-- The actual external interval cycle on the original arbitrary module. -/
def intervalCycle (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M) :
    GradedKasparovCycle (cliffordCoefficientAction β)
      ((cliffordCoefficientAction γ).continuousSections (X := unitInterval))
      cliffordCoefficientGrading
      (cliffordCoefficientGrading : CStarGrading (C × C)).continuousSections
      (CliffordExpandedIntervalModule (X := unitInterval) C M) :=
  (cycle (GradedKasparovCycle.ofKasparovCycle c)).coefficientChanged
    continuousProductCoefficientEquiv.symm
    ((cliffordCoefficientAction γ).continuousSections (X := unitInterval))
    cliffordCoefficientGrading.continuousSections
    (continuousProductCoefficientEquiv_symm_action γ)
    continuousProductCoefficientEquiv_symm_grading

theorem half_evaluation
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) (b : B × B) (x : M) :
    hilbertModuleFibreMk (B := C) t
      (half (GradedKasparovCycle.ofKasparovCycle c) b x) =
      half (GradedKasparovCycle.ofKasparovCycle (c.fibre t)) b
        (hilbertModuleFibreMk (B := C) t x) := by
  simp only [half, CliffordExternalEvenRepresentation.halfRepresentation_eq,
    CliffordOne.plusProjection, CliffordOne.minusProjection,
    AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    AdjointableMap.coe_sub_apply, GradedHilbertModule.toAdjointable_apply,
    GradedKasparovCycle.ofKasparovCycle, map_add, map_sub, map_smul,
    KasparovCycle.fibre_representation_mk, KasparovCycle.fibre_grading_mk]

/- Each original whole-fibre equality is proved with its full native domain
and independent group/coefficient/module universes in a separate declaration.
The four genuine proofs use finite elaboration budgets; only the representation
law needs a larger local budget after separation from the other fields. -/

private theorem groupUniverseExternalEvenIntervalFibre_grading_intertwine
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval)
    (z : HilbertModuleFibre (C × C)
      (CliffordExpandedIntervalModule (X := unitInterval) C M) t) :
    cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t (((intervalCycle c).fibre t).grading.grading z) =
      (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).grading.grading (cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t z) := by
  let u : HilbertModuleEquiv (C × C)
      (HilbertModuleFibre (C × C)
        (CliffordExpandedIntervalModule (X := unitInterval) C M) t)
      (CliffordPairModule C (HilbertModuleFibre C M t)) :=
    cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t
  have hu (x : CliffordExpandedIntervalModule (X := unitInterval) C M) :
      u (hilbertModuleFibreMk (B := C × C) t x) = cliffordIntervalPairEvaluation t x :=
    cliffordIntervalPairFibreEquiv_mk (B := C) (X := unitInterval) (M := M) t x
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C × C)
    (M := CliffordExpandedIntervalModule (X := unitInterval) C M) t z
  calc
    u (((intervalCycle c).fibre t).grading.grading
        (hilbertModuleFibreMk (B := C × C) t x)) =
      u (hilbertModuleFibreMk (B := C × C) t
        ((intervalCycle c).grading.grading x)) :=
      congrArg (fun y => u y) ((intervalCycle c).fibre_grading_mk t x)
    _ = cliffordIntervalPairEvaluation t ((intervalCycle c).grading.grading x) := hu _
    _ = (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).grading.grading
        (cliffordIntervalPairEvaluation t x) := by
      change cliffordPairMk
          (hilbertModuleFibreMk (B := C) t (c.grading.grading x.2))
          (hilbertModuleFibreMk (B := C) t (c.grading.grading x.1)) =
        cliffordPairMk
          ((c.fibre t).grading.grading (hilbertModuleFibreMk (B := C) t x.2))
          ((c.fibre t).grading.grading (hilbertModuleFibreMk (B := C) t x.1))
      apply Prod.ext
      · exact (c.fibre_grading_mk t x.2).symm
      · exact (c.fibre_grading_mk t x.1).symm
    _ = (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).grading.grading
        (u (hilbertModuleFibreMk (B := C × C) t x)) :=
      congrArg (fun y =>
        (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).grading.grading y)
        (hu x).symm

private theorem groupUniverseExternalEvenIntervalFibre_action_intertwine
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) (g : Γ)
    (z : HilbertModuleFibre (C × C)
      (CliffordExpandedIntervalModule (X := unitInterval) C M) t) :
    cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t (((intervalCycle c).fibre t).groupAction.action g z) =
      (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).groupAction.action g (cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C × C)
    (M := CliffordExpandedIntervalModule (X := unitInterval) C M) t z
  rw [GradedKasparovCycle.fibre_action_mk,
    cliffordIntervalPairFibreEquiv_mk, cliffordIntervalPairFibreEquiv_mk]
  apply Prod.ext <;> exact (c.fibre_action_mk t g _).symm

set_option maxHeartbeats 800000 in
private theorem groupUniverseExternalEvenIntervalFibre_representation_intertwine
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) (b : B × B)
    (z : HilbertModuleFibre (C × C)
      (CliffordExpandedIntervalModule (X := unitInterval) C M) t) :
    cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t (((intervalCycle c).fibre t).representation b z) =
      (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).representation b (cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C × C)
    (M := CliffordExpandedIntervalModule (X := unitInterval) C M) t z
  rw [GradedKasparovCycle.fibre_representation_mk,
    cliffordIntervalPairFibreEquiv_mk, cliffordIntervalPairFibreEquiv_mk]
  apply Prod.ext
  · exact half_evaluation c t b x.1
  · exact half_evaluation c t (cliffordCoefficientGrading.automorphism b) x.2

private theorem groupUniverseExternalEvenIntervalFibre_operator_intertwine
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval)
    (z : HilbertModuleFibre (C × C)
      (CliffordExpandedIntervalModule (X := unitInterval) C M) t) :
    cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t (((intervalCycle c).fibre t).operator z) =
      (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).operator (cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C × C)
    (M := CliffordExpandedIntervalModule (X := unitInterval) C M) t z
  rw [GradedKasparovCycle.fibre_operator_mk,
    cliffordIntervalPairFibreEquiv_mk, cliffordIntervalPairFibreEquiv_mk]
  apply Prod.ext <;> exact (c.fibre_operator_mk t _).symm

/-- The actual completed fibre unitary intertwines all external cycle data. -/
def intervalFibreIso
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) :
    GradedKasparovCycleIso ((intervalCycle c).fibre t)
      (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))) where
  moduleEquiv := cliffordIntervalPairFibreEquiv t
  grading_intertwine := groupUniverseExternalEvenIntervalFibre_grading_intertwine c t
  action_intertwine := groupUniverseExternalEvenIntervalFibre_action_intertwine c t
  representation_intertwine := groupUniverseExternalEvenIntervalFibre_representation_intertwine c t
  operator_intertwine := groupUniverseExternalEvenIntervalFibre_operator_intertwine c t

end GroupUniverseExternalEvenCycle

namespace GroupUniverseExternalEvenCycle

variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {c d : BundledKasparovCycle.{uΓ,uB,uC,uE} β γ}

/-- Extend the same genuine arbitrary-module full interval witness. -/
def full (h : FullKasparovHomotopy c d) :
    FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c.cycle)))
      (BundledGradedKasparovCycle.of
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle d.cycle))) where
  intervalCycle := BundledGradedKasparovCycle.of
    (GroupUniverseExternalEvenCycle.intervalCycle h.intervalCycle.cycle)
  sourceIso := (GroupUniverseExternalEvenCycle.intervalFibreIso h.intervalCycle.cycle 0).trans
    (CliffordExternalEvenCycle.iso (GroupUniverseEvenBase.isoOfEven h.sourceIso))
  targetIso := (GroupUniverseExternalEvenCycle.intervalFibreIso h.intervalCycle.cycle 1).trans
    (CliffordExternalEvenCycle.iso (GroupUniverseEvenBase.isoOfEven h.targetIso))

end GroupUniverseExternalEvenCycle
end BC4lean.KKTheory
