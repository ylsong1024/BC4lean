import BC4lean.CliffordExternalEvenCycle
import BC4lean.CliffordCycleIso

/-! # Whole-cycle unitaries for genuine external even Clifford extension

The original whole module unitary acts on both actual tensor coordinates.
Its original grading and representation intertwinings imply the genuine
Koszul representation intertwining, including both grading projections.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenCycle

variable {Γ B C E F : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Cᵐᵒᵖ E] [CStarModule Cᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {c : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial E}
  {d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F}

theorem half_intertwine (e : GradedKasparovCycleIso c d) (b : B × B) (x : E) :
    e.moduleEquiv (half c b x) = half d b (e.moduleEquiv x) := by
  simp only [half, CliffordExternalEvenRepresentation.halfRepresentation_eq,
    CliffordOne.plusProjection, CliffordOne.minusProjection,
    AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    AdjointableMap.coe_sub_apply, GradedHilbertModule.toAdjointable_apply,
    map_add, map_sub, map_smul, e.representation_intertwine, e.grading_intertwine]

/-- A genuine endpoint whole-cycle unitary induces the actual external
tensor whole-cycle unitary. -/
def iso (e : GradedKasparovCycleIso c d) :
    GradedKasparovCycleIso (cycle c) (cycle d) where
  moduleEquiv := e.moduleEquiv.cliffordPair
  grading_intertwine x := by
    apply Prod.ext <;> exact e.grading_intertwine _
  action_intertwine g x := by
    apply Prod.ext <;> exact e.action_intertwine g _
  representation_intertwine b x := by
    apply Prod.ext
    · exact half_intertwine e b x.1
    · exact half_intertwine e (cliffordCoefficientGrading.automorphism b) x.2
  operator_intertwine x := by
    apply Prod.ext <;> exact e.operator_intertwine _

end BC4lean.KKTheory.CliffordExternalEvenCycle
