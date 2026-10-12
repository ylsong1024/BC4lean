import BC4lean.FiniteProjectionModule
import Mathlib.Analysis.CStarAlgebra.Unitization

/-! # Unitization matrices acting on the actual finite right B-module

The universal property of the unitization extends left multiplication to
lambda times identity plus left multiplication by the coefficient part.
Finite coordinate adjoint pairs assemble its matrix action on B^n. When two
matrices have equal scalar entries, their operator difference is compact over
B, even though either individual unitized action need not be compact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BC4lean.KKTheory
open scoped Matrix

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- The genuine unitization action on the standard right B-module. -/
def unitizedStandardLeftMul : Unitization ℂ B →⋆ₐ[ℂ] AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ :=
  Unitization.starLift standardLeftMul

@[simp] theorem unitizedStandardLeftMul_apply (a : Unitization ℂ B) (x : Bᵐᵒᵖ) :
    unitizedStandardLeftMul a x = a.fst • x + standardLeftMul a.snd x := by
  change (algebraMap ℂ (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) a.fst + standardLeftMul a.snd) x = _
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

theorem unitizedStandardLeftMul_sub_of_fst_eq (a b : Unitization ℂ B) (h : a.fst = b.fst) :
    unitizedStandardLeftMul a - unitizedStandardLeftMul b = standardLeftMul (a.snd - b.snd) := by
  change (algebraMap ℂ (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) a.fst + standardLeftMul a.snd) -
    (algebraMap ℂ (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) b.fst + standardLeftMul b.snd) = _
  rw [h, map_sub]
  abel

/-- A finite matrix of standard-module operators acts by its coordinate blocks. -/
def coordinateOperatorMatrix (T : Matrix ι ι (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ)) :
    AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) :=
  ∑ i, ∑ j, ((finiteStandardInclusion i).comp (T i j)).comp (finiteStandardEvaluation j)

@[simp] theorem coordinateOperatorMatrix_apply
    (T : Matrix ι ι (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ)) (x : FiniteStandardModule B ι) (i : ι) :
    coordinateOperatorMatrix T x i = ∑ j, T i j (x j) := by
  simp only [coordinateOperatorMatrix, finiteAdjointable_sum_apply, AdjointableMap.comp_apply,
    finiteStandardInclusion_apply, finiteStandardEvaluation_apply]
  change (∑ i' : ι, ∑ j : ι,
    (Pi.single i' (T i' j (x j)) : ι → Bᵐᵒᵖ)) i = ∑ j, T i j (x j)
  simp [Finset.sum_apply, Pi.single_apply]

omit [StarOrderedRing B] in
theorem adjointable_finset_sum {E F α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    (T : AdjointableMap B E F) (s : Finset α) (x : α → E) :
    T (∑ i ∈ s, x i) = ∑ i ∈ s, T (x i) := map_sum T.toCLM x s

omit [StarOrderedRing B] in
theorem finiteAdjointable_sum_adjoint {E F α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    (s : Finset α) (T : α → AdjointableMap B E F) :
    (∑ i ∈ s, T i).adjoint = ∑ i ∈ s, (T i).adjoint := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have ha : (T i + ∑ x ∈ s, T x).adjoint =
        (T i).adjoint + (∑ x ∈ s, T x).adjoint := by
      apply AdjointableMap.toCLM_injective
      rfl
    rw [ha, ih]

theorem coordinateOperatorMatrix_adjoint (T : Matrix ι ι (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ)) :
    (coordinateOperatorMatrix T).adjoint = coordinateOperatorMatrix (fun i j => (T j i).adjoint) := by
  have hb (i j : ι) :
      (((finiteStandardInclusion i).comp (T i j)).comp (finiteStandardEvaluation j)).adjoint =
        ((finiteStandardInclusion j).comp (T i j).adjoint).comp (finiteStandardEvaluation i) := by
    ext x
    rfl
  simp only [coordinateOperatorMatrix, finiteAdjointable_sum_adjoint, hb]
  rw [Finset.sum_comm]

theorem coordinateOperatorMatrix_sub
    (S T : Matrix ι ι (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ)) :
    coordinateOperatorMatrix (S - T) = coordinateOperatorMatrix S - coordinateOperatorMatrix T := by
  ext x i
  simp only [coordinateOperatorMatrix_apply, AdjointableMap.coe_sub_apply, WithCStarModule.sub_apply]
  change (∑ j, (S i j - T i j) (x j)) = _
  simp only [AdjointableMap.coe_sub_apply, Finset.sum_sub_distrib]

theorem coordinateOperatorMatrix_isModuleCompact
    (T : Matrix ι ι (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ)) (h : ∀ i j, IsModuleCompact (T i j)) :
    IsModuleCompact (coordinateOperatorMatrix T) := by
  apply (moduleCompact B (FiniteStandardModule B ι) (FiniteStandardModule B ι)).sum_mem
  intro i _
  apply (moduleCompact B (FiniteStandardModule B ι) (FiniteStandardModule B ι)).sum_mem
  intro j _
  exact ((h i j).comp_left (finiteStandardInclusion i)).comp_right (finiteStandardEvaluation j)

/-- The finite unitization matrix representation on B^n, with its genuine Hilbert norm. -/
def unitizedModuleMatrixRepresentation : CStarMatrix ι ι (Unitization ℂ B) →⋆ₙₐ[ℂ]
    AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) where
  toFun M := coordinateOperatorMatrix fun i j => unitizedStandardLeftMul (M i j)
  map_zero' := by
    ext x i
    simp only [coordinateOperatorMatrix_apply, CStarMatrix.zero_apply, map_zero,
      AdjointableMap.coe_zero_apply, Finset.sum_const_zero, WithCStarModule.zero_apply]
  map_add' M N := by
    ext x i
    simp only [coordinateOperatorMatrix_apply, CStarMatrix.add_apply, map_add,
      AdjointableMap.coe_add_apply, Finset.sum_add_distrib, WithCStarModule.add_apply]
  map_smul' c M := by
    ext x i
    simp only [coordinateOperatorMatrix_apply, CStarMatrix.smul_apply, map_smul,
      AdjointableMap.coe_smul_apply, Finset.smul_sum, WithCStarModule.smul_apply, MonoidHom.id_apply]
  map_mul' M N := by
    ext x i
    simp only [coordinateOperatorMatrix_apply, CStarMatrix.mul_apply, map_sum, map_mul,
      finiteAdjointable_sum_apply, AdjointableMap.mul_apply]
    rw [Finset.sum_comm]
  map_star' M := by
    change coordinateOperatorMatrix (fun i j => unitizedStandardLeftMul ((star M) i j)) =
      (coordinateOperatorMatrix (fun i j => unitizedStandardLeftMul (M i j))).adjoint
    rw [coordinateOperatorMatrix_adjoint]
    congr 1
    funext i j
    simp only [CStarMatrix.star_apply, map_star, AdjointableMap.star_eq_adjoint]

@[simp] theorem unitizedModuleMatrixRepresentation_apply (M : CStarMatrix ι ι (Unitization ℂ B))
    (x : FiniteStandardModule B ι) (i : ι) :
    unitizedModuleMatrixRepresentation M x i = ∑ j, unitizedStandardLeftMul (M i j) (x j) :=
  coordinateOperatorMatrix_apply _ _ _

/-- Equality of scalar matrix entries makes the difference a compact B-module operator. -/
theorem unitizedModuleMatrixRepresentation_sub_isModuleCompact
    (M N : CStarMatrix ι ι (Unitization ℂ B)) (h : ∀ i j, (M i j).fst = (N i j).fst) :
    IsModuleCompact (unitizedModuleMatrixRepresentation M - unitizedModuleMatrixRepresentation N) := by
  change IsModuleCompact (coordinateOperatorMatrix (fun i j => unitizedStandardLeftMul (M i j)) -
    coordinateOperatorMatrix (fun i j => unitizedStandardLeftMul (N i j)))
  rw [← coordinateOperatorMatrix_sub]
  apply coordinateOperatorMatrix_isModuleCompact
  intro i j
  change IsModuleCompact (unitizedStandardLeftMul (M i j) - unitizedStandardLeftMul (N i j))
  rw [unitizedStandardLeftMul_sub_of_fst_eq _ _ (h i j)]
  exact standardLeftMul_mem_moduleCompact _

end BC4lean.KKTheory
