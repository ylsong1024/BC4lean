import BC4lean.UnitizedFiniteModuleOperator
import BC4lean.HilbertModuleCountableGenerationSeparable

/-! # Genuine finite sums of arbitrary Hilbert modules and operator matrices

The norm and coefficient form are Mathlib's actual finite module sum.
Coordinate inclusions and evaluations are genuine adjoint pairs. A finite
matrix of actual module endomorphisms acts by its finite coordinate blocks;
compact entries give a compact whole operator.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BC4lean.KKTheory
open scoped InnerProductSpace CStarAlgebra

variable {B E ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [Fintype ι] [DecidableEq ι]

abbrev FiniteHilbertModuleSum (B E ι : Type*) := WithCStarModule Bᵐᵒᵖ (ι → E)

def finiteHilbertModuleSingle (i : ι) (x : E) : FiniteHilbertModuleSum B E ι :=
  (WithCStarModule.equiv _ _).symm (Pi.single i x)

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [Fintype ι] in
@[simp] theorem finiteHilbertModuleSingle_apply (i j : ι) (x : E) :
    finiteHilbertModuleSingle (B := B) i x j = (Pi.single i x : ι → E) j := rfl

theorem finiteHilbertModuleSingle_norm (i : ι) (x : E) :
    ‖finiteHilbertModuleSingle (B := B) i x‖ = ‖x‖ :=
  WithCStarModule.norm_single (A := Bᵐᵒᵖ) (E := fun _ : ι => E) i x

def finiteHilbertModuleInclusionCLM (i : ι) : E →L[ℂ] FiniteHilbertModuleSum B E ι :=
  LinearMap.mkContinuous
    { toFun := finiteHilbertModuleSingle i
      map_add' x y := by ext j; simp [finiteHilbertModuleSingle, Pi.single_add]
      map_smul' c x := by ext j; simp [finiteHilbertModuleSingle, Pi.single_smul] }
    1 (fun x => by
      change ‖finiteHilbertModuleSingle i x‖ ≤ 1 * ‖x‖
      rw [finiteHilbertModuleSingle_norm, one_mul])

def finiteHilbertModuleEvaluationCLM (i : ι) : FiniteHilbertModuleSum B E ι →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun x := x i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    1 (fun x => by
      change ‖x i‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact WithCStarModule.norm_apply_le_norm x i)

def finiteHilbertModuleInclusion (i : ι) : AdjointableMap B E (FiniteHilbertModuleSum B E ι) where
  toCLM := finiteHilbertModuleInclusionCLM i
  adjointCLM := finiteHilbertModuleEvaluationCLM i
  adjoint_identity x y := WithCStarModule.inner_single_left y x

def finiteHilbertModuleEvaluation (i : ι) : AdjointableMap B (FiniteHilbertModuleSum B E ι) E :=
  (finiteHilbertModuleInclusion i).adjoint

@[simp] theorem finiteHilbertModuleInclusion_apply (i : ι) (x : E) :
    finiteHilbertModuleInclusion (B := B) (E := E) i x = finiteHilbertModuleSingle i x := rfl
@[simp] theorem finiteHilbertModuleEvaluation_apply (i : ι) (x : FiniteHilbertModuleSum B E ι) :
    finiteHilbertModuleEvaluation (B := B) (E := E) i x = x i := rfl

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [Fintype ι] [DecidableEq ι] in
theorem finiteHilbertModuleSum_complete [CompleteSpace E] :
    CompleteSpace (FiniteHilbertModuleSum B E ι) :=
  (WithCStarModule.uniformEquiv (A := Bᵐᵒᵖ) (E := ι → E)).completeSpace_iff.mpr inferInstance

omit [DecidableEq ι] in
theorem finiteHilbertModuleSum_countablyGenerated [TopologicalSpace.SeparableSpace B]
    (hE : IsCountablyGeneratedModule B E) : IsCountablyGeneratedModule B (FiniteHilbertModuleSum B E ι) := by
  let : TopologicalSpace.SeparableSpace E := hE.separableSpace
  let : TopologicalSpace.SeparableSpace (FiniteHilbertModuleSum B E ι) :=
    (WithCStarModule.uniformEquiv (A := Bᵐᵒᵖ) (E := ι → E)).symm.surjective.denseRange.separableSpace
      (WithCStarModule.uniformEquiv (A := Bᵐᵒᵖ) (E := ι → E)).symm.toHomeomorph.continuous
  exact isCountablyGeneratedModule_of_separableSpace

def finiteHilbertModuleOperatorMatrix (T : Matrix ι ι (AdjointableMap B E E)) :
    AdjointableMap B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B E ι) :=
  ∑ i, ∑ j, ((finiteHilbertModuleInclusion i).comp (T i j)).comp (finiteHilbertModuleEvaluation j)

@[simp] theorem finiteHilbertModuleOperatorMatrix_apply
    (T : Matrix ι ι (AdjointableMap B E E)) (x : FiniteHilbertModuleSum B E ι) (i : ι) :
    finiteHilbertModuleOperatorMatrix T x i = ∑ j, T i j (x j) := by
  simp only [finiteHilbertModuleOperatorMatrix, finiteAdjointable_sum_apply, AdjointableMap.comp_apply,
    finiteHilbertModuleInclusion_apply, finiteHilbertModuleEvaluation_apply]
  change (∑ i' : ι, ∑ j : ι,
    (Pi.single i' (T i' j (x j)) : ι → E)) i = ∑ j, T i j (x j)
  simp [Finset.sum_apply, Pi.single_apply]

theorem finiteHilbertModuleOperatorMatrix_adjoint (T : Matrix ι ι (AdjointableMap B E E)) :
    (finiteHilbertModuleOperatorMatrix T).adjoint =
      finiteHilbertModuleOperatorMatrix (fun i j => (T j i).adjoint) := by
  have hb (i j : ι) :
      (((finiteHilbertModuleInclusion i).comp (T i j)).comp (finiteHilbertModuleEvaluation j)).adjoint =
        ((finiteHilbertModuleInclusion j).comp (T i j).adjoint).comp (finiteHilbertModuleEvaluation i) := by
    ext x
    rfl
  simp only [finiteHilbertModuleOperatorMatrix, finiteAdjointable_sum_adjoint, hb]
  rw [Finset.sum_comm]

theorem finiteHilbertModuleOperatorMatrix_compact (T : Matrix ι ι (AdjointableMap B E E))
    (hT : ∀ i j, IsModuleCompact (T i j)) : IsModuleCompact (finiteHilbertModuleOperatorMatrix T) := by
  apply (moduleCompact B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B E ι)).sum_mem
  intro i _
  apply (moduleCompact B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B E ι)).sum_mem
  intro j _
  exact ((hT i j).comp_left (finiteHilbertModuleInclusion i)).comp_right (finiteHilbertModuleEvaluation j)

variable [CompleteSpace E]
local instance : CompleteSpace (FiniteHilbertModuleSum B E ι) := finiteHilbertModuleSum_complete

def finiteHilbertModuleMatrixHom : CStarMatrix ι ι (AdjointableMap B E E) →⋆ₐ[ℂ]
    AdjointableMap B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B E ι) where
  toFun M := finiteHilbertModuleOperatorMatrix (fun i j => M i j)
  map_zero' := by ext x i; simp only [finiteHilbertModuleOperatorMatrix_apply,
    CStarMatrix.zero_apply, AdjointableMap.coe_zero_apply, Finset.sum_const_zero,
    WithCStarModule.zero_apply]
  map_add' M N := by ext x i; simp only [finiteHilbertModuleOperatorMatrix_apply,
    CStarMatrix.add_apply, AdjointableMap.coe_add_apply, Finset.sum_add_distrib,
    WithCStarModule.add_apply]
  map_one' := by
    ext x i
    rw [finiteHilbertModuleOperatorMatrix_apply]
    change (∑ j, (if i = j then (1 : AdjointableMap B E E) else 0) (x j)) = x i
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, AdjointableMap.one_apply]
    · intro j _ hji
      rw [if_neg (Ne.symm hji), AdjointableMap.coe_zero_apply]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  map_mul' M N := by
    ext x i
    simp only [finiteHilbertModuleOperatorMatrix_apply, CStarMatrix.mul_apply,
      finiteAdjointable_sum_apply, AdjointableMap.mul_apply, adjointable_finset_sum]
    rw [Finset.sum_comm]
  map_star' M := by
    change finiteHilbertModuleOperatorMatrix (fun i j => (star M) i j) =
      (finiteHilbertModuleOperatorMatrix (fun i j => M i j)).adjoint
    rw [finiteHilbertModuleOperatorMatrix_adjoint]
    congr 1
  commutes' z := by
    ext x i
    rw [finiteHilbertModuleOperatorMatrix_apply]
    change (∑ j, ((algebraMap ℂ (CStarMatrix ι ι (AdjointableMap B E E)) z) i j) (x j)) =
      ((algebraMap ℂ (AdjointableMap B (FiniteHilbertModuleSum B E ι)
        (FiniteHilbertModuleSum B E ι)) z) x) i
    simp only [Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply, CStarMatrix.one_apply,
      AdjointableMap.coe_smul_apply, AdjointableMap.one_apply, WithCStarModule.smul_apply]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, AdjointableMap.one_apply]
    · intro j _ hji
      rw [if_neg (Ne.symm hji), AdjointableMap.coe_zero_apply, smul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim

end BC4lean.KKTheory
