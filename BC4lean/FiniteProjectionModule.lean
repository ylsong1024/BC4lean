import BC4lean.ModuleGramMatrix
import BC4lean.ProjectionHilbertModule
import BC4lean.StandardModuleOperator
import BC4lean.RectangularEquivalence

/-! # Finite projection range modules

Finite standard modules and their matrix norm/action are those of
`ModuleGramMatrix`. Coordinate maps are genuine adjoint pairs, so a finite
coefficient matrix acts compactly. Finite projections over a unital algebra
have complete, finitely generated range modules. Rectangular Murray--von
Neumann witnesses give unitary maps between the ranges, with no assertion that
the ambient partial isometry is unitary.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace Matrix

variable {B ι κ τ : Type*}

section NonUnital
variable [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

/-- One coordinate of the actual finite standard Hilbert module. -/
def finiteStandardSingle (i : ι) (b : Bᵐᵒᵖ) : FiniteStandardModule B ι :=
  (WithCStarModule.equiv _ _).symm (Pi.single i b)

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] in
@[simp] theorem finiteStandardSingle_apply (i j : ι) (b : Bᵐᵒᵖ) :
    finiteStandardSingle i b j = (Pi.single i b : ι → Bᵐᵒᵖ) j := rfl

theorem finiteStandardSingle_norm (i : ι) (b : Bᵐᵒᵖ) : ‖finiteStandardSingle i b‖ = ‖b‖ :=
  WithCStarModule.norm_single (A := Bᵐᵒᵖ) (E := fun _ : ι => Bᵐᵒᵖ) i b

/-- The bounded coordinate inclusion for the genuine finite-module norm. -/
def finiteStandardInclusionCLM (i : ι) : Bᵐᵒᵖ →L[ℂ] FiniteStandardModule B ι :=
  LinearMap.mkContinuous
    { toFun := finiteStandardSingle i
      map_add' := fun x y => by ext j; simp [finiteStandardSingle, Pi.single_add]
      map_smul' := fun c x => by ext j; simp [finiteStandardSingle, Pi.single_smul] }
    1 (fun b => by
      change ‖finiteStandardSingle i b‖ ≤ 1 * ‖b‖
      rw [finiteStandardSingle_norm, one_mul])

/-- Coordinate evaluation is bounded by the actual Hilbert-module norm. -/
def finiteStandardEvaluationCLM (i : ι) : FiniteStandardModule B ι →L[ℂ] Bᵐᵒᵖ :=
  LinearMap.mkContinuous
    { toFun := fun v => v i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun v => by
      change ‖v i‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact WithCStarModule.norm_apply_le_norm v i)

/-- Coordinate inclusion and evaluation form an actual adjoint pair. -/
def finiteStandardInclusion (i : ι) : AdjointableMap B Bᵐᵒᵖ (FiniteStandardModule B ι) where
  toCLM := finiteStandardInclusionCLM i
  adjointCLM := finiteStandardEvaluationCLM i
  adjoint_identity b v := WithCStarModule.inner_single_left v b

/-- Coordinate evaluation as an adjointable module map. -/
def finiteStandardEvaluation (i : ι) : AdjointableMap B (FiniteStandardModule B ι) Bᵐᵒᵖ :=
  (finiteStandardInclusion i).adjoint

@[simp] theorem finiteStandardInclusion_apply (i : ι) (b : Bᵐᵒᵖ) :
    finiteStandardInclusion i b = finiteStandardSingle i b := rfl
@[simp] theorem finiteStandardEvaluation_apply (i : ι) (v : FiniteStandardModule B ι) :
    finiteStandardEvaluation i v = v i := rfl

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
theorem finiteStandardModule_complete : CompleteSpace (FiniteStandardModule B ι) :=
  (WithCStarModule.uniformEquiv (A := Bᵐᵒᵖ) (E := ι → Bᵐᵒᵖ)).completeSpace_iff.mpr inferInstance

/-- Rectangular transpose/op conversion implements the ordinary column action. -/
def rectangularModuleOpposite (v : Matrix ι κ B) : CStarMatrix κ ι Bᵐᵒᵖ :=
  CStarMatrix.ofMatrix fun j i => MulOpposite.op (v i j)

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem rectangularModuleOpposite_apply (v : Matrix ι κ B) (j : κ) (i : ι) :
    rectangularModuleOpposite v j i = MulOpposite.op (v i j) := rfl

/-- A rectangular coefficient matrix is a genuine adjointable column map. -/
def rectangularModuleOperator (v : Matrix ι κ B) :
    AdjointableMap B (FiniteStandardModule B κ) (FiniteStandardModule B ι) where
  toCLM := CStarMatrix.toCLM (rectangularModuleOpposite v)
  adjointCLM := CStarMatrix.toCLM (rectangularModuleOpposite v)ᴴ
  adjoint_identity _x _y := CStarMatrix.inner_toCLM_conjTranspose_right.symm

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem rectangularModuleOperator_apply (v : Matrix ι κ B)
    (x : FiniteStandardModule B κ) (i : ι) :
    rectangularModuleOperator v x i = ∑ j, x j * MulOpposite.op (v i j) := by
  change CStarMatrix.toCLM (rectangularModuleOpposite v) x i = _
  rw [CStarMatrix.toCLM_apply_eq_sum]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem rectangularModuleOperator_adjoint (v : Matrix ι κ B) :
    (rectangularModuleOperator v).adjoint = rectangularModuleOperator vᴴ := by
  have hop : rectangularModuleOpposite vᴴ = (rectangularModuleOpposite v)ᴴ := by
    ext i j
    change MulOpposite.op (star (v i j)) = star (MulOpposite.op (v i j))
    exact MulOpposite.op_star _
  apply AdjointableMap.ext
  intro x
  change CStarMatrix.toCLM (rectangularModuleOpposite v)ᴴ x =
    CStarMatrix.toCLM (rectangularModuleOpposite vᴴ) x
  rw [hop]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] in
theorem rectangularModuleOperator_comp (v : Matrix ι κ B) (w : Matrix κ τ B) :
    (rectangularModuleOperator v).comp (rectangularModuleOperator w) = rectangularModuleOperator (v * w) := by
  ext x i
  simp only [AdjointableMap.comp_apply, rectangularModuleOperator_apply, Matrix.mul_apply,
    Finset.op_sum, MulOpposite.op_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
/-- The rectangular API specializes to the existing faithful square-matrix representation. -/
theorem rectangularModuleOperator_square (M : CStarMatrix ι ι B) :
    rectangularModuleOperator (CStarMatrix.ofMatrix.symm M) = moduleMatrixRepresentation M := by
  ext x
  rfl

omit [StarOrderedRing B] in
/-- Finite sums of adjointable maps evaluate as finite sums of their values. -/
theorem finiteAdjointable_sum_apply {E F α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    (s : Finset α) (T : α → AdjointableMap B E F) (x : E) :
    (∑ i ∈ s, T i) x = ∑ i ∈ s, T i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, AdjointableMap.coe_add_apply, ih]

/-- A matrix action is its actual finite sum of coordinate coefficient blocks. -/
theorem moduleMatrixRepresentation_coordinate_sum (M : CStarMatrix ι ι B) :
    moduleMatrixRepresentation M = ∑ i : ι, ∑ j : ι,
      ((finiteStandardInclusion i).comp (standardLeftMul (M i j))).comp (finiteStandardEvaluation j) := by
  ext x k
  rw [← rectangularModuleOperator_square]
  simp only [rectangularModuleOperator_apply, finiteAdjointable_sum_apply,
    AdjointableMap.comp_apply, finiteStandardInclusion_apply, finiteStandardEvaluation_apply,
    standardLeftMul_apply]
  change (∑ j, x j * MulOpposite.op (M k j)) =
    (∑ i : ι, ∑ j : ι, (Pi.single i (x j * MulOpposite.op (M i j)) : ι → Bᵐᵒᵖ)) k
  simp [Finset.sum_apply, Pi.single_apply]

/-- Every finite coefficient matrix acts compactly, even for nonunital coefficients. -/
theorem moduleMatrixRepresentation_isModuleCompact (M : CStarMatrix ι ι B) :
    IsModuleCompact (moduleMatrixRepresentation M) := by
  rw [moduleMatrixRepresentation_coordinate_sum]
  apply (moduleCompact B (FiniteStandardModule B ι) (FiniteStandardModule B ι)).sum_mem
  intro i _
  apply (moduleCompact B (FiniteStandardModule B ι) (FiniteStandardModule B ι)).sum_mem
  intro j _
  have hc : IsModuleCompact (standardLeftMul (M i j)) := standardLeftMul_mem_moduleCompact (M i j)
  exact (hc.comp_left (finiteStandardInclusion i)).comp_right (finiteStandardEvaluation j)

end NonUnital

section Unital
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A sequence containing every finite module basis vector. -/
def finiteStandardBasisSequence : ℕ → FiniteStandardModule B ι := fun n =>
  if h : n < Fintype.card ι then finiteStandardSingle ((Fintype.equivFin ι).symm ⟨n, h⟩) 1 else 0

omit [PartialOrder B] [StarOrderedRing B] in
theorem finiteStandardBasisSequence_at (i : ι) :
    finiteStandardBasisSequence (B := B) ((Fintype.equivFin ι i).val) = finiteStandardSingle i 1 := by
  simp [finiteStandardBasisSequence, (Fintype.equivFin ι i).isLt]

/-- Finite standard modules are countably generated by their actual coefficient basis.
No separability of the unital coefficient algebra is needed. -/
theorem finiteStandardModule_isCountablyGenerated : IsCountablyGeneratedModule B (FiniteStandardModule B ι) := by
  refine ⟨finiteStandardBasisSequence, ?_⟩
  have hspan : moduleGeneratingSpan (B := B) (finiteStandardBasisSequence (B := B) (ι := ι)) = ⊤ := by
    apply top_unique
    intro v _
    have hv : v = ∑ i : ι, v i • finiteStandardSingle i (1 : Bᵐᵒᵖ) := by
      ext j
      change v j = (∑ i : ι, v i • (Pi.single i (1 : Bᵐᵒᵖ) : ι → Bᵐᵒᵖ)) j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      exact (Fintype.sum_ite_eq j (fun i => v i)).symm
    rw [hv]
    apply (moduleGeneratingSpan (B := B) (finiteStandardBasisSequence (B := B) (ι := ι))).sum_mem
    intro i _
    simpa only [finiteStandardBasisSequence_at] using
      smul_mem_moduleGeneratingSpan (finiteStandardBasisSequence (B := B) (ι := ι))
        ((Fintype.equivFin ι i).val) (v i)
  rw [hspan]
  exact dense_univ

/-- A projection acts on the actual finite standard right module. -/
def matrixProjectionOperator (p : BC4lean.OperatorKTheory.MatrixProjection B ι) :
    AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) :=
  moduleMatrixRepresentation p.val

theorem matrixProjectionOperator_isStarProjection (p : BC4lean.OperatorKTheory.MatrixProjection B ι) :
    IsStarProjection (matrixProjectionOperator p) := p.property.map moduleMatrixRepresentation

/-- The genuine finite projective right Hilbert-module range. -/
abbrev FiniteProjectionModule (p : BC4lean.OperatorKTheory.MatrixProjection B ι) :=
  ProjectionModule (matrixProjectionOperator p)

theorem finiteProjectionModule_isCountablyGenerated (p : BC4lean.OperatorKTheory.MatrixProjection B ι) :
    IsCountablyGeneratedModule B (FiniteProjectionModule p) :=
  projectionModule_isCountablyGenerated _ (matrixProjectionOperator_isStarProjection p)
    finiteStandardModule_isCountablyGenerated

theorem finiteProjectionModule_identity_isModuleCompact (p : BC4lean.OperatorKTheory.MatrixProjection B ι) :
    IsModuleCompact (1 : AdjointableMap B (FiniteProjectionModule p) (FiniteProjectionModule p)) :=
  projectionModule_identity_isModuleCompact _ (matrixProjectionOperator_isStarProjection p)
    (moduleMatrixRepresentation_isModuleCompact p.val)

/-- A Murray--von Neumann rectangular witness restricts to a genuine range unitary. -/
def finiteProjectionRangeEquiv (p : BC4lean.OperatorKTheory.MatrixProjection B ι)
    (q : BC4lean.OperatorKTheory.MatrixProjection B κ) (v : Matrix ι κ B)
    (hp : v * vᴴ = BC4lean.OperatorKTheory.projectionMatrix p)
    (hq : vᴴ * v = BC4lean.OperatorKTheory.projectionMatrix q) :
    HilbertModuleEquiv B (FiniteProjectionModule p) (FiniteProjectionModule q) :=
  projectionRangeEquiv (matrixProjectionOperator p) (matrixProjectionOperator q)
    (rectangularModuleOperator vᴴ)
    (by rw [rectangularModuleOperator_adjoint, Matrix.conjTranspose_conjTranspose,
      rectangularModuleOperator_comp, hp, rectangularModuleOperator_square]; rfl)
    (by rw [rectangularModuleOperator_adjoint, Matrix.conjTranspose_conjTranspose,
      rectangularModuleOperator_comp, hq, rectangularModuleOperator_square]; rfl)

end Unital
end BC4lean.KKTheory
