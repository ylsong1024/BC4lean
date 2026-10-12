import BC4lean.CliffordExternalEvenCycleIso
import BC4lean.CliffordIntervalExpansionFibre
import BC4lean.GradedMatrixMoritaEvenBase

/-! # External even Clifford extension preserves genuine full homotopies

The interval carrier is the pair of the original arbitrary interval
module, transported along the actual continuous-product coefficient
equivalence. The completed fibre unitary is obtained from its full evaluated
inner product and genuine onto coordinate evaluation. No section-module or
fixed-module assumption is imposed on the original homotopy.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
namespace CliffordExternalEvenCycle

variable {Γ B C M : Type u} [Group Γ] [NonUnitalCStarAlgebra B]
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

/- Each whole-cycle fibre law is proved separately with its full native
domain and data, so the original declaration budget is not shared by four
independent operator/evaluation calculations. -/

private theorem cliffordExternalEvenIntervalFibre_grading_intertwine
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) (z : HilbertModuleFibre (C × C)
      (CliffordExpandedIntervalModule (X := unitInterval) C M) t) :
    cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t (((intervalCycle c).fibre t).grading.grading z) =
      (cycle (GradedKasparovCycle.ofKasparovCycle (c.fibre t))).grading.grading (cliffordIntervalPairFibreEquiv (B := C) (X := unitInterval) (M := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := C × C)
    (M := CliffordExpandedIntervalModule (X := unitInterval) C M) t z
  rw [GradedKasparovCycle.fibre_grading_mk,
    cliffordIntervalPairFibreEquiv_mk, cliffordIntervalPairFibreEquiv_mk]
  apply Prod.ext <;> exact (c.fibre_grading_mk t _).symm

private theorem cliffordExternalEvenIntervalFibre_action_intertwine
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
private theorem cliffordExternalEvenIntervalFibre_representation_intertwine
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

private theorem cliffordExternalEvenIntervalFibre_operator_intertwine
    (c : KasparovCycle β (γ.continuousSections (X := unitInterval)) M)
    (t : unitInterval) (z : HilbertModuleFibre (C × C)
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
  grading_intertwine := cliffordExternalEvenIntervalFibre_grading_intertwine c t
  action_intertwine := cliffordExternalEvenIntervalFibre_action_intertwine c t
  representation_intertwine := cliffordExternalEvenIntervalFibre_representation_intertwine c t
  operator_intertwine := cliffordExternalEvenIntervalFibre_operator_intertwine c t

end CliffordExternalEvenCycle

namespace FullKasparovHomotopy

variable {Γ B C : Type u} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {c d : BundledKasparovCycle.{u,u,u,u} β γ}

/-- Extend the same genuine arbitrary-module full interval witness. -/
def externalEvenClifford (h : FullKasparovHomotopy c d) :
    FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c.cycle)))
      (BundledGradedKasparovCycle.of
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle d.cycle))) where
  intervalCycle := BundledGradedKasparovCycle.of
    (CliffordExternalEvenCycle.intervalCycle h.intervalCycle.cycle)
  sourceIso := (CliffordExternalEvenCycle.intervalFibreIso h.intervalCycle.cycle 0).trans
    (CliffordExternalEvenCycle.iso (GradedMatrixMoritaEvenBase.isoOfEven h.sourceIso))
  targetIso := (CliffordExternalEvenCycle.intervalFibreIso h.intervalCycle.cycle 1).trans
    (CliffordExternalEvenCycle.iso (GradedMatrixMoritaEvenBase.isoOfEven h.targetIso))

end FullKasparovHomotopy
end BC4lean.KKTheory
