import BC4lean.RelativeProjectionPartialIsometry
import BC4lean.ProjectionHalmosUnitary
import BC4lean.FiniteModuleCompactMatrix

/-! # Actual scalar correction for a unitization projection conjugation

The scalar section composed with the scalar quotient is an actual idempotent
star-algebra homomorphism on finite unitization matrices. For a genuine unitary
U and a projection p, the partial isometry sigma(U) sigma(p) U* compares
U sigma(p) U* with sigma(U p U*). Its scalar matrix is the target scalar
projection, so its difference from the crossmap has zero full scalar part and
acts compactly on the genuine B-module. The resulting relative class is zero.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

local instance scalarCorrectionUnitizationOrder : PartialOrder (Unitization ℂ B) :=
  CStarAlgebra.spectralOrder _
local instance scalarCorrectionUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ B) :=
  CStarAlgebra.spectralOrderedRing _

/-- The actual scalar shadow, using the proved scalar quotient and its section. -/
def unitizationScalarLiftHom : CStarMatrix ι ι (Unitization ℂ B) →⋆ₐ[ℂ]
    CStarMatrix ι ι (Unitization ℂ B) :=
  (matrixMap (scalarSection B)).comp (matrixMap (scalarQuotient B))

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem unitizationScalarLiftHom_scalar
    (M : CStarMatrix ι ι (Unitization ℂ B)) :
    unitizationScalarMatrix (unitizationScalarLiftHom M) = unitizationScalarMatrix M := by
  ext i j
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem unitizationScalarLiftHom_idempotent
    (M : CStarMatrix ι ι (Unitization ℂ B)) :
    unitizationScalarLiftHom (unitizationScalarLiftHom M) = unitizationScalarLiftHom M := by
  apply CStarMatrix.ext
  intro i j
  change scalarSection B (scalarQuotient B (scalarSection B (scalarQuotient B (M i j)))) =
    scalarSection B (scalarQuotient B (M i j))
  apply congrArg (scalarSection B)
  have h := congrArg (fun f : ℂ →⋆ₐ[ℂ] ℂ => f (scalarQuotient B (M i j)))
    (scalarQuotient_section B)
  simpa only [StarAlgHom.comp_apply, StarAlgHom.coe_id, id_eq] using h

/-- The actual scalar shadow of a genuine unitization projection. -/
def unitizationScalarShadowProjection
    (p : MatrixProjection (Unitization ℂ B) ι) : MatrixProjection (Unitization ℂ B) ι :=
  ⟨unitizationScalarLiftHom p.val, p.property.map unitizationScalarLiftHom⟩

/-- The actual partial isometry correcting the scalar reference after conjugation. -/
def unitizationScalarProjectionCorrection
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) : CStarMatrix ι ι (Unitization ℂ B) :=
  unitizationScalarLiftHom (U : CStarMatrix ι ι (Unitization ℂ B)) *
    unitizationScalarLiftHom p.val * star (U : CStarMatrix ι ι (Unitization ℂ B))

omit [PartialOrder B] [StarOrderedRing B] in
/-- The initial support is the transported actual scalar projection. -/
theorem unitizationScalarProjectionCorrection_source
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) :
    star (unitizationScalarProjectionCorrection U p) * unitizationScalarProjectionCorrection U p =
      (unitaryProjectionConjugate U (unitizationScalarShadowProjection p)).val := by
  let s := unitizationScalarLiftHom (B := B) (ι := ι)
  have hU : star (s U.val) * s U.val = 1 := by rw [← map_star, ← map_mul, U.property.1, map_one]
  have hp : s p.val * s p.val = s p.val := by rw [← map_mul, p.property.isIdempotentElem.eq]
  have hps : star (s p.val) = s p.val := by rw [← map_star, p.property.isSelfAdjoint.star_eq]
  change star (s U.val * s p.val * star U.val) * (s U.val * s p.val * star U.val) = _
  calc
    star (s U.val * s p.val * star U.val) * (s U.val * s p.val * star U.val) =
        U.val * s p.val * (star (s U.val) * s U.val) * s p.val * star U.val := by
      simp only [star_mul, star_star, hps, mul_assoc]
    _ = U.val * s p.val * s p.val * star U.val := by rw [hU, mul_one]
    _ = U.val * s p.val * star U.val := by rw [mul_assoc U.val (s p.val) (s p.val), hp]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The final support is the actual scalar shadow of the conjugated projection. -/
theorem unitizationScalarProjectionCorrection_target
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) :
    unitizationScalarProjectionCorrection U p * star (unitizationScalarProjectionCorrection U p) =
      (unitizationScalarShadowProjection (unitaryProjectionConjugate U p)).val := by
  let s := unitizationScalarLiftHom (B := B) (ι := ι)
  have hp : s p.val * s p.val = s p.val := by rw [← map_mul, p.property.isIdempotentElem.eq]
  have hps : star (s p.val) = s p.val := by rw [← map_star, p.property.isSelfAdjoint.star_eq]
  change (s U.val * s p.val * star U.val) * star (s U.val * s p.val * star U.val) =
    s (U.val * p.val * star U.val)
  calc
    (s U.val * s p.val * star U.val) * star (s U.val * s p.val * star U.val) =
        s U.val * s p.val * (star U.val * U.val) * s p.val * star (s U.val) := by
      simp only [star_mul, star_star, hps, mul_assoc]
    _ = s U.val * s p.val * s p.val * star (s U.val) := by rw [U.property.1, mul_one]
    _ = s U.val * s p.val * star (s U.val) := by rw [mul_assoc (s U.val) (s p.val) (s p.val), hp]
    _ = s (U.val * p.val * star U.val) := by rw [map_mul, map_mul, map_star]

omit [PartialOrder B] [StarOrderedRing B] in
/-- Both reference projections have exactly the same full scalar matrix. -/
theorem unitizationScalarProjectionCorrection_reference_scalar
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) :
    unitizationScalarMatrix (unitaryProjectionConjugate U (unitizationScalarShadowProjection p)).val =
      unitizationScalarMatrix (unitizationScalarShadowProjection (unitaryProjectionConjugate U p)).val := by
  change unitizationScalarMatrix (U.val * unitizationScalarLiftHom p.val * star U.val) =
    unitizationScalarMatrix (unitizationScalarLiftHom (U.val * p.val * star U.val))
  simp only [unitizationScalarLiftHom_scalar, unitizationScalarMatrix_mul,
    unitizationScalarMatrix_star]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The correction has the target full scalar matrix, with no action-faithfulness claim. -/
theorem unitizationScalarProjectionCorrection_scalar
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) :
    unitizationScalarMatrix (unitizationScalarProjectionCorrection U p) =
      unitizationScalarMatrix (unitizationScalarShadowProjection (unitaryProjectionConjugate U p)).val := by
  change unitizationScalarMatrix
      (unitizationScalarLiftHom U.val * unitizationScalarLiftHom p.val * star U.val) =
    unitizationScalarMatrix (unitizationScalarLiftHom (U.val * p.val * star U.val))
  simp only [unitizationScalarLiftHom_scalar, unitizationScalarMatrix_mul,
    unitizationScalarMatrix_star]

/-- The scalar-correcting supported partial isometry is compactly relative to
its true crossmap, by equality of actual full scalar matrices. -/
theorem unitizationScalarProjectionCorrection_cross_isModuleCompact
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) :
    IsModuleCompact (unitizedModuleMatrixRepresentation (unitizationScalarProjectionCorrection U p) -
      unitizedProjectionOperator (unitizationScalarShadowProjection (unitaryProjectionConjugate U p)) *
        unitizedProjectionOperator (unitaryProjectionConjugate U (unitizationScalarShadowProjection p))) := by
  let r := unitaryProjectionConjugate U (unitizationScalarShadowProjection p)
  let q := unitizationScalarShadowProjection (unitaryProjectionConjugate U p)
  have hs : unitizationScalarMatrix (unitizationScalarProjectionCorrection U p) =
      unitizationScalarMatrix (q.val * r.val) := by
    rw [unitizationScalarMatrix_mul, unitizationScalarProjectionCorrection_reference_scalar U p,
      unitizationScalarProjectionCorrection_scalar U p]
    have hq : IsStarProjection (unitizationScalarMatrix q.val) := by
      apply isStarProjection_iff'.mpr
      constructor
      · rw [← unitizationScalarMatrix_mul, q.property.isIdempotentElem.eq]
      · rw [← unitizationScalarMatrix_star, q.property.isSelfAdjoint.star_eq]
    rw [hq.isIdempotentElem.eq]
  change IsModuleCompact (unitizedModuleMatrixRepresentation (unitizationScalarProjectionCorrection U p) -
    unitizedModuleMatrixRepresentation q.val * unitizedModuleMatrixRepresentation r.val)
  rw [← map_mul]
  apply unitizedModuleMatrixRepresentation_sub_isModuleCompact
  intro i j
  exact congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hs

/-- The correcting reference cycle has zero genuine full homotopy class. -/
theorem unitizationScalarProjectionCorrection_class_zero
    [TopologicalSpace.SeparableSpace B]
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (unitizedRelativeProjectionCycle (Γ := PUnit)
        (unitaryProjectionConjugate U (unitizationScalarShadowProjection p))
        (unitizationScalarShadowProjection (unitaryProjectionConjugate U p))
        (fun i j => congrArg (fun M : CStarMatrix ι ι ℂ => M i j)
          (unitizationScalarProjectionCorrection_reference_scalar U p)))) = 0 := by
  let r := unitaryProjectionConjugate U (unitizationScalarShadowProjection p)
  let q := unitizationScalarShadowProjection (unitaryProjectionConjugate U p)
  have hs : ∀ i j, (r.val i j).fst = (q.val i j).fst := fun i j =>
    congrArg (fun M : CStarMatrix ι ι ℂ => M i j)
      (unitizationScalarProjectionCorrection_reference_scalar U p)
  refine relativeProjection_class_zero_of_partialIsometry
    (unitizedProjectionOperator r) (unitizedProjectionOperator q)
    (unitizedModuleMatrixRepresentation (unitizationScalarProjectionCorrection U p))
    (unitizedProjectionOperator_isStarProjection r) (unitizedProjectionOperator_isStarProjection q)
    (unitizedModuleMatrixRepresentation_sub_isModuleCompact r.val q.val hs)
    finiteStandardModule_isCountablyGenerated_nonunital ?_ ?_ ?_
  · change star (unitizedModuleMatrixRepresentation (unitizationScalarProjectionCorrection U p)) *
      unitizedModuleMatrixRepresentation (unitizationScalarProjectionCorrection U p) = _
    rw [← map_star, ← map_mul, unitizationScalarProjectionCorrection_source]
    rfl
  · change unitizedModuleMatrixRepresentation (unitizationScalarProjectionCorrection U p) *
      star (unitizedModuleMatrixRepresentation (unitizationScalarProjectionCorrection U p)) = _
    rw [← map_star, ← map_mul, unitizationScalarProjectionCorrection_target]
    rfl
  · exact unitizationScalarProjectionCorrection_cross_isModuleCompact U p

end BC4lean.KKTheory
