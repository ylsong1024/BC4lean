import BC4lean.GradedKasparovDirectSum
import BC4lean.GradedCycleCoefficientEquiv

/-! # Whole graded-cycle coefficient changes commute with the actual sum -/

noncomputable section
namespace BC4lean.KKTheory
variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {η : CStarAlgebraAction Γ C} {δA : CStarGrading A}
  {δB : CStarGrading B} {δC : CStarGrading C}

def GradedKasparovCycle.changeCoefficientsDirectSumIso
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle α β δA δB F)
    (e : GradedCoefficientEquiv β δB η δC) :
    GradedKasparovCycleIso ((c.directSum d).changeCoefficients e)
      ((c.changeCoefficients e).directSum (d.changeCoefficients e)) where
  moduleEquiv := coefficientChangedSumEquiv e.starAlgEquiv
  grading_intertwine x := rfl
  action_intertwine g x := rfl
  representation_intertwine a x := by
    let y : HilbertModuleSum B E F :=
      coefficientChangedToOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv x
    change coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv
      (coefficientChangedOfOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv
        (sumMap (c.representation a) (d.representation a) y)) =
      sumMap (coefficientChangedOperator e.starAlgEquiv (c.representation a))
        (coefficientChangedOperator e.starAlgEquiv (d.representation a))
        (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x)
    calc
      _ = coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv
          (coefficientChangedOfOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv
            (sumMk (B := B) (c.representation a y.fst) (d.representation a y.snd))) :=
        congrArg (fun v : HilbertModuleSum B E F =>
          coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv
            (coefficientChangedOfOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv v))
          (sumMap_apply (B := B) (c.representation a) (d.representation a) y)
      _ = sumMk (B := C)
          (coefficientChangedOperator e.starAlgEquiv (c.representation a)
            (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x).fst)
          (coefficientChangedOperator e.starAlgEquiv (d.representation a)
            (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x).snd) := rfl
      _ = _ := (sumMap_apply (B := C)
        (coefficientChangedOperator e.starAlgEquiv (c.representation a))
        (coefficientChangedOperator e.starAlgEquiv (d.representation a))
        (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x)).symm
  operator_intertwine x := by
    let y : HilbertModuleSum B E F :=
      coefficientChangedToOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv x
    change coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv
      (coefficientChangedOfOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv
        (sumMap c.operator d.operator y)) =
      sumMap (coefficientChangedOperator e.starAlgEquiv c.operator)
        (coefficientChangedOperator e.starAlgEquiv d.operator)
        (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x)
    calc
      _ = coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv
          (coefficientChangedOfOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv
            (sumMk (B := B) (c.operator y.fst) (d.operator y.snd))) :=
        congrArg (fun v : HilbertModuleSum B E F =>
          coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv
            (coefficientChangedOfOriginal (M := HilbertModuleSum B E F) e.starAlgEquiv v))
          (sumMap_apply (B := B) c.operator d.operator y)
      _ = sumMk (B := C)
          (coefficientChangedOperator e.starAlgEquiv c.operator
            (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x).fst)
          (coefficientChangedOperator e.starAlgEquiv d.operator
            (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x).snd) := rfl
      _ = _ := (sumMap_apply (B := C)
        (coefficientChangedOperator e.starAlgEquiv c.operator)
        (coefficientChangedOperator e.starAlgEquiv d.operator)
        (coefficientChangedSumEquiv (E := E) (F := F) e.starAlgEquiv x)).symm

end BC4lean.KKTheory
