import BC4lean.CliffordExternalEvenInterval
import BC4lean.CliffordDirectSumIso
import BC4lean.GradedKasparovSourcePullbackClass

/-! # External even Clifford extension on genuine full homotopy classes

The map transports the same actual arbitrary interval witness. Its sum
law is proved by the whole pair/sum permutation unitary and the true
Koszul half-representation formula, rather than by an assumed exterior
product law.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory

namespace CliffordExternalEvenCycle
open CliffordExternalEvenRepresentation

variable {Γ B C F G : Type*} [Group Γ] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Cᵐᵒᵖ G] [CStarModule Cᵐᵒᵖ G] [CompleteSpace G]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F)
  (e : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial G)

theorem half_directSum (b : B × B) :
    half (d.directSum e) b = sumMap (half d b) (half e b) := by
  apply AdjointableMap.ext
  intro x
  simp only [half, halfRepresentation_eq, CliffordOne.plusProjection,
    CliffordOne.minusProjection, AdjointableMap.mul_apply, AdjointableMap.coe_add_apply,
    AdjointableMap.coe_sub_apply, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    GradedHilbertModule.toAdjointable_apply, sumMap_apply]
  change sumMap (d.representation b.1) (e.representation b.1)
        ((2 : ℂ)⁻¹ • (x + (d.grading.sum e.grading).grading x)) +
      sumMap (d.representation b.2) (e.representation b.2)
        ((2 : ℂ)⁻¹ • (x - (d.grading.sum e.grading).grading x)) =
    sumMk
      (d.representation b.1 ((2 : ℂ)⁻¹ • (x.fst + d.grading.grading x.fst)) +
        d.representation b.2 ((2 : ℂ)⁻¹ • (x.fst - d.grading.grading x.fst)))
      (e.representation b.1 ((2 : ℂ)⁻¹ • (x.snd + e.grading.grading x.snd)) +
        e.representation b.2 ((2 : ℂ)⁻¹ • (x.snd - e.grading.grading x.snd)))
  simp only [GradedHilbertModule.sum_grading_apply, sumMap_apply,
    WithCStarModule.smul_fst, WithCStarModule.smul_snd,
    WithCStarModule.add_fst, WithCStarModule.add_snd,
    WithCStarModule.sub_fst, WithCStarModule.sub_snd,
    sumMk_fst, sumMk_snd, sumMk_add]

def directSumIso : GradedKasparovCycleIso ((cycle d).directSum (cycle e)) (cycle (d.directSum e)) where
  moduleEquiv := cliffordPairSumEquiv
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine b x := by
    change cliffordPairSumEquiv
      (sumMap (cliffordPairMap (half d b) (half d (cliffordCoefficientGrading.automorphism b)))
        (cliffordPairMap (half e b) (half e (cliffordCoefficientGrading.automorphism b))) x) =
      cliffordPairMap (half (d.directSum e) b)
        (half (d.directSum e) (cliffordCoefficientGrading.automorphism b)) (cliffordPairSumEquiv x)
    rw [half_directSum, half_directSum]
    simp only [sumMap_apply, cliffordPairMap_apply, cliffordPairSumEquiv_apply,
      sumMk_fst, sumMk_snd]
    rfl
  operator_intertwine x := by
    change cliffordPairSumEquiv (sumMap (cliffordPairMap d.operator d.operator)
      (cliffordPairMap e.operator e.operator) x) =
      cliffordPairMap (sumMap d.operator e.operator) (sumMap d.operator e.operator)
        (cliffordPairSumEquiv x)
    simp only [sumMap_apply, cliffordPairMap_apply, cliffordPairSumEquiv_apply,
      sumMk_fst, sumMk_snd]
    rfl

end CliffordExternalEvenCycle

variable {Γ B C : Type u} [Group Γ] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C] [TopologicalSpace.SeparableSpace C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

def cliffordExternalEvenClass (x : KasparovHomotopyClass.{u,u,u,u} β γ) :
    GradedKasparovHomotopyClass.{u,u,u,u} (cliffordCoefficientAction β)
      (cliffordCoefficientAction γ) cliffordCoefficientGrading cliffordCoefficientGrading :=
  Quotient.lift (fun c => GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
    (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c.cycle)))) (by
      intro c d h
      obtain ⟨h⟩ := BundledKasparovCycle.homotopic_iff_full.mp h
      exact GradedKasparovHomotopyClass.mk_eq_of_full h.externalEvenClifford) x

@[simp] theorem cliffordExternalEvenClass_mk (c : BundledKasparovCycle.{u,u,u,u} β γ) :
    cliffordExternalEvenClass (KasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c.cycle))) := rfl

theorem cliffordExternalEvenClass_add (x y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    cliffordExternalEvenClass (x + y) = cliffordExternalEvenClass x + cliffordExternalEvenClass y := by
  refine Quotient.inductionOn₂' x y ?_
  intro c d
  change cliffordExternalEvenClass (KasparovHomotopyClass.mk c + KasparovHomotopyClass.mk d) =
    cliffordExternalEvenClass (KasparovHomotopyClass.mk c) +
      cliffordExternalEvenClass (KasparovHomotopyClass.mk d)
  rw [← KasparovHomotopyClass.mk_directSum]
  simp only [cliffordExternalEvenClass_mk, ← GradedKasparovHomotopyClass.mk_directSum]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    (CliffordExternalEvenCycle.directSumIso
      (GradedKasparovCycle.ofKasparovCycle c.cycle)
      (GradedKasparovCycle.ofKasparovCycle d.cycle)).symm

end BC4lean.KKTheory
