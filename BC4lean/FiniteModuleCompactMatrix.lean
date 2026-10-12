import BC4lean.UnitizedFiniteModuleOperator

/-! # Genuine finite compact matrices and scalar-controlled unitization reflection

Every compact operator on the actual finite standard B-module is reconstructed
from its actual coordinate compact maps B_B→B_B, each of which is uniquely left
multiplication by a coefficient in B. For unitization matrices, the represented
operator and the scalar matrix part together are faithful. This reflects actual
projections without asserting faithfulness of the unitization action alone,
including when B is unital, zero, or the coordinate type is empty.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BC4lean.KKTheory

open scoped Matrix

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- The genuine finite module is the sum of its actual coordinate inclusions. -/
theorem finiteStandardCoordinateResolution (x : FiniteStandardModule B ι) :
    ∑ i : ι, finiteStandardInclusion i (x i) = x := by
  ext j
  change (finiteStandardEvaluation (B := B) j) (∑ i : ι, finiteStandardInclusion i (x i)) = x j
  rw [map_sum (finiteStandardEvaluation (B := B) j).toCLM]
  simp only [finiteStandardEvaluation_apply, finiteStandardInclusion_apply,
    finiteStandardSingle_apply]
  simp [Pi.single_apply]

/-- Actual coordinate blocks reconstruct every finite-module operator. -/
theorem coordinateOperatorMatrix_reconstruct
    (T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :
    coordinateOperatorMatrix (fun i j =>
      ((finiteStandardEvaluation i).comp T).comp (finiteStandardInclusion j)) = T := by
  ext x i
  rw [coordinateOperatorMatrix_apply]
  change (∑ j : ι, finiteStandardEvaluation i (T (finiteStandardInclusion j (x j)))) = T x i
  rw [← map_sum (finiteStandardEvaluation i).toCLM, ← map_sum T.toCLM,
    finiteStandardCoordinateResolution]
  rfl

/-- Compact coordinate blocks have actual coefficients in B. -/
theorem finiteModuleCompact_coordinate_exists
    {T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)}
    (hT : IsModuleCompact T) (i j : ι) :
    ∃ b : B, standardLeftMul b =
      ((finiteStandardEvaluation i).comp T).comp (finiteStandardInclusion j) :=
  (mem_moduleCompact_standard_iff _).mp
    ((hT.comp_left (finiteStandardEvaluation i)).comp_right (finiteStandardInclusion j))

/-- Every actual finite compact operator is represented by a genuine coefficient
matrix. The matrix entries are extracted from its actual compact coordinate maps. -/
theorem finiteModuleCompact_exists_matrix
    {T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)}
    (hT : IsModuleCompact T) :
    ∃ M : CStarMatrix ι ι B, moduleMatrixRepresentation M = T := by
  let M : CStarMatrix ι ι B := CStarMatrix.ofMatrix fun i j =>
    Classical.choose (finiteModuleCompact_coordinate_exists hT i j)
  refine ⟨M, ?_⟩
  calc
    moduleMatrixRepresentation M = coordinateOperatorMatrix (fun i j => standardLeftMul (M i j)) :=
      moduleMatrixRepresentation_coordinate_sum M
    _ = coordinateOperatorMatrix (fun i j =>
        ((finiteStandardEvaluation i).comp T).comp (finiteStandardInclusion j)) := by
      congr 1
      funext i j
      exact Classical.choose_spec (finiteModuleCompact_coordinate_exists hT i j)
    _ = T := coordinateOperatorMatrix_reconstruct T

/-- The exact finite coefficient characterization of actual compact operators. -/
theorem finiteModule_isModuleCompact_iff_matrix
    (T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :
    IsModuleCompact T ↔ ∃ M : CStarMatrix ι ι B, moduleMatrixRepresentation M = T := by
  constructor
  · exact finiteModuleCompact_exists_matrix
  · rintro ⟨M, rfl⟩
    exact moduleMatrixRepresentation_isModuleCompact M

/-- The actual coefficient matrix of a finite compact map, extracted from its
genuine compact coordinate maps. -/
def finiteModuleCompactMatrix
    (T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
    (hT : IsModuleCompact T) : CStarMatrix ι ι B :=
  Classical.choose (finiteModuleCompact_exists_matrix hT)

@[simp] theorem moduleMatrixRepresentation_finiteModuleCompactMatrix
    (T : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
    (hT : IsModuleCompact T) : moduleMatrixRepresentation (finiteModuleCompactMatrix T hT) = T :=
  Classical.choose_spec (finiteModuleCompact_exists_matrix hT)

omit [DecidableEq ι] in
/-- Faithfulness of the actual coefficient representation is an isometry for
the genuine C*-matrix and finite Hilbert-module operator norms. -/
theorem moduleMatrixRepresentation_isometry :
    Isometry (moduleMatrixRepresentation (B := B) (n := ι)) :=
  NonUnitalStarAlgHom.isometry _ moduleMatrixRepresentation_injective

/-- A norm-continuous family of genuine finite compact operators has a
norm-continuous family of its actual B-matrix coefficients. No continuity of
an arbitrary choice or faithfulness of the unitization action is assumed. -/
theorem continuous_finiteModuleCompactMatrix {X : Type*} [TopologicalSpace X]
    (T : X → AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
    (hT : ∀ x, IsModuleCompact (T x)) (hContinuous : Continuous T) :
    Continuous (fun x => finiteModuleCompactMatrix (T x) (hT x)) := by
  apply moduleMatrixRepresentation_isometry.comp_continuous_iff.mp
  simpa only [Function.comp_def, moduleMatrixRepresentation_finiteModuleCompactMatrix] using hContinuous

/-- Preserve the complete scalar matrix part of a unitization matrix. -/
def unitizationScalarMatrix (M : CStarMatrix ι ι (Unitization ℂ B)) : CStarMatrix ι ι ℂ :=
  M.map fun a => a.fst

/-- Embed a genuine coefficient matrix into the unitization entrywise. -/
def unitizationCoefficientMatrix (M : CStarMatrix ι ι B) : CStarMatrix ι ι (Unitization ℂ B) :=
  M.map fun a => (a : Unitization ℂ B)

omit [DecidableEq ι] in
/-- The actual coefficient inclusion on finite matrices is norm-continuous. -/
theorem continuous_unitizationCoefficientMatrix :
    Continuous (unitizationCoefficientMatrix (B := B) (ι := ι)) := by
  let φ : CStarMatrix ι ι B →⋆ₙₐ[ℂ] CStarMatrix ι ι (Unitization ℂ B) :=
    CStarMatrix.mapₙₐ (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hφ : Function.Injective φ := by
    intro M N h
    apply CStarMatrix.ext
    intro i j
    apply Unitization.inr_injective (R := ℂ)
    exact congrArg (fun K : CStarMatrix ι ι (Unitization ℂ B) => K i j) h
  change Continuous φ
  exact (NonUnitalStarAlgHom.isometry φ hφ).continuous

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
@[simp] theorem unitizationScalarMatrix_apply
    (M : CStarMatrix ι ι (Unitization ℂ B)) (i j : ι) :
    unitizationScalarMatrix M i j = (M i j).fst := rfl

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
@[simp] theorem unitizationCoefficientMatrix_apply (M : CStarMatrix ι ι B) (i j : ι) :
    unitizationCoefficientMatrix M i j = (M i j : Unitization ℂ B) := rfl

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
theorem unitizationScalarMatrix_add (M N : CStarMatrix ι ι (Unitization ℂ B)) :
    unitizationScalarMatrix (M + N) = unitizationScalarMatrix M + unitizationScalarMatrix N := by
  ext i j
  simp only [unitizationScalarMatrix_apply, CStarMatrix.add_apply, Unitization.fst_add]

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
@[simp] theorem unitizationScalarMatrix_coefficient (M : CStarMatrix ι ι B) :
    unitizationScalarMatrix (unitizationCoefficientMatrix M) = 0 := by
  ext i j
  simp only [unitizationScalarMatrix_apply, unitizationCoefficientMatrix_apply,
    Unitization.fst_inr, CStarMatrix.zero_apply]

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
theorem unitizationScalarMatrix_sub (M N : CStarMatrix ι ι (Unitization ℂ B)) :
    unitizationScalarMatrix (M - N) = unitizationScalarMatrix M - unitizationScalarMatrix N := by
  ext i j
  change (Unitization.fstHom ℂ B) (M i j - N i j) =
    (Unitization.fstHom ℂ B) (M i j) - (Unitization.fstHom ℂ B) (N i j)
  exact map_sub _ _ _

omit [PartialOrder B] [StarOrderedRing B] [DecidableEq ι] in
theorem unitizationScalarMatrix_mul (M N : CStarMatrix ι ι (Unitization ℂ B)) :
    unitizationScalarMatrix (M * N) = unitizationScalarMatrix M * unitizationScalarMatrix N := by
  ext i j
  change (Unitization.fstHom ℂ B) (∑ k, M i k * N k j) =
    ∑ k, (Unitization.fstHom ℂ B) (M i k) * (Unitization.fstHom ℂ B) (N k j)
  simp only [map_sum, map_mul]

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
theorem unitizationScalarMatrix_star (M : CStarMatrix ι ι (Unitization ℂ B)) :
    unitizationScalarMatrix (star M) = star (unitizationScalarMatrix M) := by
  ext i j
  simp only [unitizationScalarMatrix_apply, CStarMatrix.star_apply, Unitization.fst_star]

/-- The genuine coefficient inclusion agrees with the faithful B-matrix action. -/
theorem unitizedModuleMatrixRepresentation_coefficient (M : CStarMatrix ι ι B) :
    unitizedModuleMatrixRepresentation (unitizationCoefficientMatrix M) = moduleMatrixRepresentation M := by
  change coordinateOperatorMatrix (fun i j => unitizedStandardLeftMul (M i j : Unitization ℂ B)) = _
  calc
    _ = coordinateOperatorMatrix (fun i j => standardLeftMul (M i j)) := by
      congr 1
      funext i j
      ext x
      simp only [unitizedStandardLeftMul_apply, Unitization.fst_inr, Unitization.snd_inr,
        zero_smul, zero_add]
    _ = moduleMatrixRepresentation M := (moduleMatrixRepresentation_coordinate_sum M).symm

/-- A unitization matrix with zero scalar part and zero represented action is
actually zero, by the faithful coefficient-matrix representation. -/
theorem unitizationMatrix_eq_zero_of_scalar_and_operator_zero
    (M : CStarMatrix ι ι (Unitization ℂ B)) (hScalar : unitizationScalarMatrix M = 0)
    (hOperator : unitizedModuleMatrixRepresentation M = 0) : M = 0 := by
  let K : CStarMatrix ι ι B := M.map fun a => a.snd
  have hM : M = unitizationCoefficientMatrix K := by
    apply CStarMatrix.ext
    intro i j
    apply Unitization.ext
    · have hh := congrArg (fun N : CStarMatrix ι ι ℂ => N i j) hScalar
      simpa only [unitizationScalarMatrix_apply, CStarMatrix.zero_apply, unitizationCoefficientMatrix_apply,
        Unitization.fst_inr] using hh
    · rfl
  have hK : moduleMatrixRepresentation K = moduleMatrixRepresentation (0 : CStarMatrix ι ι B) := by
    rw [← unitizedModuleMatrixRepresentation_coefficient, ← hM, hOperator, map_zero]
  have hKzero := moduleMatrixRepresentation_injective hK
  rw [hM, hKzero]
  apply CStarMatrix.ext
  intro i j
  simp only [unitizationCoefficientMatrix_apply, CStarMatrix.zero_apply, Unitization.inr_zero]

/-- The scalar matrix and the actual operator action are jointly faithful.
The unitization action by itself is not asserted faithful. -/
theorem unitizationMatrix_eq_of_scalar_and_operator_eq
    (M N : CStarMatrix ι ι (Unitization ℂ B))
    (hScalar : unitizationScalarMatrix M = unitizationScalarMatrix N)
    (hOperator : unitizedModuleMatrixRepresentation M = unitizedModuleMatrixRepresentation N) : M = N := by
  apply sub_eq_zero.mp
  apply unitizationMatrix_eq_zero_of_scalar_and_operator_zero
  · rw [unitizationScalarMatrix_sub, hScalar, sub_self]
  · rw [map_sub, hOperator, sub_self]

/-- A represented projection is a genuine unitization-matrix projection when
its actual complete scalar matrix part is also a projection. -/
theorem unitizationMatrix_isStarProjection_of_scalar_and_operator
    (M : CStarMatrix ι ι (Unitization ℂ B))
    (hScalar : IsStarProjection (unitizationScalarMatrix M))
    (hOperator : IsStarProjection (unitizedModuleMatrixRepresentation M)) : IsStarProjection M := by
  apply isStarProjection_iff'.mpr
  constructor
  · apply unitizationMatrix_eq_of_scalar_and_operator_eq
    · rw [unitizationScalarMatrix_mul, hScalar.isIdempotentElem.eq]
    · rw [map_mul, hOperator.isIdempotentElem.eq]
  · apply unitizationMatrix_eq_of_scalar_and_operator_eq
    · rw [unitizationScalarMatrix_star, hScalar.isSelfAdjoint.star_eq]
    · rw [map_star, hOperator.isSelfAdjoint.star_eq]

end BC4lean.KKTheory
