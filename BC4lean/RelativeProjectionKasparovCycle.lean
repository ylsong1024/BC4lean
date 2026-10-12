import BC4lean.FiniteProjectionKasparovCycle
import BC4lean.FiniteModuleCountableGeneration
import BC4lean.UnitizedFiniteModuleOperator
import BC4lean.KasparovInverseRotation
import BC4lean.NonunitalOperatorK
import BC4lean.FiniteMatrixProjectionIndex

/-! # Relative projection cycles over possibly nonunital coefficients

For selfadjoint projections P and Q on a complete countably generated right
module with P-Q compact, use the supported module PE direct-sum QE, graded
even/odd, and the selfadjoint off-diagonal operator (PQ, QP). Its square defect
is a diagonal pair of compressions of Q-P and P-Q, so all Kasparov defects are
proved. Equal-scalar-part projections in matrices over the forced unitization
give this compact difference on B^n and an actual element of the previously
defined `OperatorKTheory.OperatorK0 B` kernel.

This is a concrete relative-projection construction. It does not assume that
every kernel element already has an equal-scalar-part normal form, and does
not assert a K0/KK comparison isomorphism or its well-definedness on classes.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace Matrix

variable {Γ B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The selfadjoint off-diagonal operator of an actual adjointable map. -/
def offDiagonalAdjointable (T : AdjointableMap B E F) :
    AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) :=
  (sumInl.comp T.adjoint).comp sumSnd + (sumInr.comp T).comp sumFst

@[simp] theorem offDiagonalAdjointable_apply (T : AdjointableMap B E F)
    (x : HilbertModuleSum B E F) : offDiagonalAdjointable T x = sumMk (T.adjoint x.snd) (T x.fst) := by
  change (T.adjoint x.snd, (0 : F)) + ((0 : E), T x.fst) = (T.adjoint x.snd, T x.fst)
  simp

@[simp] theorem offDiagonalAdjointable_star (T : AdjointableMap B E F) :
    star (offDiagonalAdjointable T) = offDiagonalAdjointable T := by
  ext x
  change ((0 : E), T x.fst) + (T.adjoint x.snd, (0 : F)) =
    (T.adjoint x.snd, (0 : F)) + ((0 : E), T x.fst)
  simp

theorem offDiagonalAdjointable_square (T : AdjointableMap B E F) :
    offDiagonalAdjointable T * offDiagonalAdjointable T = sumMap (T.adjoint.comp T) (T.comp T.adjoint) := by
  ext x
  simp only [AdjointableMap.mul_apply, offDiagonalAdjointable_apply, sumMap_apply,
    sumMk_fst, sumMk_snd, AdjointableMap.comp_apply]

/-- The off-diagonal map is odd for the even/odd supported grading. -/
theorem offDiagonalAdjointable_odd (T : AdjointableMap B E F) :
    ((GradedHilbertModule.trivial : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E).sum
      (GradedHilbertModule.trivial : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) F).opposite).IsOdd
      ((GradedHilbertModule.trivial : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E).sum
      (GradedHilbertModule.trivial : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) F).opposite)
      (offDiagonalAdjointable T) := by
  intro x
  simp only [GradedHilbertModule.sum_grading_apply, GradedHilbertModule.opposite_grading_apply,
    offDiagonalAdjointable_apply, sumMk_fst, sumMk_snd]
  apply Prod.ext <;> simp [GradedHilbertModule.trivial]

/-- The map from the P-supported range to the Q-supported range, correctly corestricted. -/
def projectionCrossMap (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    AdjointableMap B (ProjectionModule P) (ProjectionModule Q) :=
  (projectionCorestrict Q hQ).comp (projectionInclusion P hP)

omit [StarOrderedRing B] in
@[simp] theorem projectionCrossMap_adjoint (P Q : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (projectionCrossMap P Q hP hQ).adjoint = projectionCrossMap Q P hQ hP := by
  ext x
  rfl

omit [StarOrderedRing B] in
@[simp] theorem projectionCrossMap_coe (P Q : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (x : ProjectionModule P) :
    ((projectionCrossMap P Q hP hQ x : ProjectionModule Q) : E) = Q (x : E) := rfl

/-- The exact square defect is a pair of compact-difference compressions. -/
theorem relativeProjection_square_defect (P Q : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    offDiagonalAdjointable (projectionCrossMap P Q hP hQ) *
        offDiagonalAdjointable (projectionCrossMap P Q hP hQ) - 1 =
      sumMap ((projectionCorestrict P hP).comp ((Q - P).comp (projectionInclusion P hP)))
        ((projectionCorestrict Q hQ).comp ((P - Q).comp (projectionInclusion Q hQ))) := by
  have hp : (projectionCrossMap P Q hP hQ).adjoint.comp (projectionCrossMap P Q hP hQ) - 1 =
      (projectionCorestrict P hP).comp ((Q - P).comp (projectionInclusion P hP)) := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, Submodule.coe_sub]
    change P (Q (x : E)) - (x : E) = P ((Q - P) (x : E))
    have hx : P (x : E) = (x : E) := x.property
    simp only [AdjointableMap.coe_sub_apply, P.toCLM.map_sub, hx]
  have hq : (projectionCrossMap P Q hP hQ).comp (projectionCrossMap P Q hP hQ).adjoint - 1 =
      (projectionCorestrict Q hQ).comp ((P - Q).comp (projectionInclusion Q hQ)) := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, Submodule.coe_sub]
    change Q (P (x : E)) - (x : E) = Q ((P - Q) (x : E))
    have hx : Q (x : E) = (x : E) := x.property
    simp only [AdjointableMap.coe_sub_apply, Q.toCLM.map_sub, hx]
  rw [offDiagonalAdjointable_square, ← sumMap_one, ← sumMap_sub, hp, hq]

theorem relativeProjection_square_defect_isModuleCompact (P Q : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : IsModuleCompact (P - Q)) :
    IsModuleCompact (offDiagonalAdjointable (projectionCrossMap P Q hP hQ) *
      offDiagonalAdjointable (projectionCrossMap P Q hP hQ) - 1) := by
  rw [relativeProjection_square_defect]
  apply IsModuleCompact.sumMap
  · have hneg : IsModuleCompact (Q - P) := by simpa only [neg_sub] using h.neg
    exact (hneg.comp_right (projectionInclusion P hP)).comp_left (projectionCorestrict P hP)
  · exact (h.comp_right (projectionInclusion Q hQ)).comp_left (projectionCorestrict Q hQ)

variable [Group Γ] [CompleteSpace E]

/-- The genuine relative projection cycle; the endpoints/projection defects are proved. -/
def relativeProjectionCycle (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (h : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
      (HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q)) where
  countablyGenerated := (projectionModule_isCountablyGenerated P hP hE).sum
    (projectionModule_isCountablyGenerated Q hQ hE)
  grading := GradedHilbertModule.trivial.sum GradedHilbertModule.trivial.opposite
  groupAction := EquivariantHilbertModule.trivial
  grading_preserved := by intro g x; rfl
  representation := scalarModuleRepresentation
  representation_even := by
    intro a x
    exact (GradedHilbertModule.trivial.sum GradedHilbertModule.trivial.opposite).grading.map_smul a x
  representation_equivariant := by intro g a; ext x; rfl
  operator := offDiagonalAdjointable (projectionCrossMap P Q hP hQ)
  operator_odd := offDiagonalAdjointable_odd _
  selfadjoint_mod_compact := by
    intro a
    rw [offDiagonalAdjointable_star]
    simpa using IsModuleCompact.zero (B := B)
      (E := HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))
      (F := HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))
  square_mod_compact := by
    intro a
    exact (relativeProjection_square_defect_isModuleCompact P Q hP hQ h).comp_right
      (scalarModuleRepresentation a)
  commutator_compact := by
    intro a
    have hc : offDiagonalAdjointable (projectionCrossMap P Q hP hQ) * scalarModuleRepresentation a -
        scalarModuleRepresentation a * offDiagonalAdjointable (projectionCrossMap P Q hP hQ) = 0 := by
      ext x
      simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, scalarModuleRepresentation_apply]
      exact sub_eq_zero.mpr ((offDiagonalAdjointable (projectionCrossMap P Q hP hQ)).toCLM.map_smul a x)
    rw [hc]
    exact IsModuleCompact.zero
  equivariance_mod_compact := by
    intro g a
    have hc : (EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
        (offDiagonalAdjointable (projectionCrossMap P Q hP hQ)) =
        offDiagonalAdjointable (projectionCrossMap P Q hP hQ) := by ext x; rfl
    rw [hc]
    simpa using IsModuleCompact.zero (B := B)
      (E := HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))
      (F := HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))

/-- Equal supported projections produce an exactly degenerate cycle, with the
actual off-diagonal identity rather than a compactness assumption on either range. -/
theorem relativeProjectionCycle_diagonal_isDegenerate
    (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (h : IsModuleCompact (P - P)) (hE : IsCountablyGeneratedModule B E) :
    (relativeProjectionCycle (Γ := Γ) P P hP hP h hE).IsDegenerate := by
  have hT : projectionCrossMap P P hP hP = AdjointableMap.id := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    exact x.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (offDiagonalAdjointable (projectionCrossMap P P hP hP) -
      star (offDiagonalAdjointable (projectionCrossMap P P hP hP))) * scalarModuleRepresentation a = 0
    rw [offDiagonalAdjointable_star, sub_self, zero_mul]
  · intro a
    change (offDiagonalAdjointable (projectionCrossMap P P hP hP) *
      offDiagonalAdjointable (projectionCrossMap P P hP hP) - 1) * scalarModuleRepresentation a = 0
    rw [offDiagonalAdjointable_square, hT]
    have hi : sumMap
        ((AdjointableMap.id (B := B) (E := ProjectionModule P)).adjoint.comp AdjointableMap.id)
        ((AdjointableMap.id (B := B) (E := ProjectionModule P)).comp
          (AdjointableMap.id (B := B) (E := ProjectionModule P)).adjoint) = 1 := by
      simp only [AdjointableMap.adjoint_id, AdjointableMap.id_comp]
      exact sumMap_one (B := B) (E := ProjectionModule P) (F := ProjectionModule P)
    rw [hi, sub_self, zero_mul]
  · intro a
    change offDiagonalAdjointable (projectionCrossMap P P hP hP) * scalarModuleRepresentation a -
      scalarModuleRepresentation a * offDiagonalAdjointable (projectionCrossMap P P hP hP) = 0
    ext x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, scalarModuleRepresentation_apply,
      AdjointableMap.coe_zero_apply]
    exact sub_eq_zero.mpr ((offDiagonalAdjointable (projectionCrossMap P P hP hP)).toCLM.map_smul a x)
  · intro g a
    change ((EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
      (offDiagonalAdjointable (projectionCrossMap P P hP hP)) -
        offDiagonalAdjointable (projectionCrossMap P P hP hP)) * scalarModuleRepresentation a = 0
    have he : (EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
        (offDiagonalAdjointable (projectionCrossMap P P hP hP)) =
        offDiagonalAdjointable (projectionCrossMap P P hP hP) := by ext x; rfl
    rw [he, sub_self, zero_mul]

end BC4lean.KKTheory

namespace BC4lean.KKTheory

variable {Γ B ι : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι]

local instance relativeUnitizationOrder : PartialOrder (Unitization ℂ B) :=
  CStarAlgebra.spectralOrder (Unitization ℂ B)
local instance relativeUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ B) :=
  CStarAlgebra.spectralOrderedRing (Unitization ℂ B)
local instance relativeComplexOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance relativeComplexStarOrderedRing : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

/-- A unitization projection acts on B^n, rather than changing the coefficient module to B~. -/
def unitizedProjectionOperator (p : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) ι) :
    AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι) :=
  unitizedModuleMatrixRepresentation p.val

theorem unitizedProjectionOperator_isStarProjection
    (p : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) ι) :
    IsStarProjection (unitizedProjectionOperator p) := p.property.map unitizedModuleMatrixRepresentation

/-- The genuine B-valued supported module of a unitization projection. -/
abbrev UnitizedProjectionModule (p : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) ι) :=
  ProjectionModule (unitizedProjectionOperator p)

set_option maxHeartbeats 1000000 in
/-- Equal scalar matrix parts give an actual element of the existing nonunital K0 kernel.
Arbitrary finite index universes use the actual canonical finite ordinal presentation. -/
def equalScalarProjectionDifference
    (p q : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) : BC4lean.OperatorKTheory.OperatorK0 B := by
  have hpq : BC4lean.OperatorKTheory.matrixProjectionMap (BC4lean.OperatorKTheory.scalarQuotient B) p =
      BC4lean.OperatorKTheory.matrixProjectionMap (BC4lean.OperatorKTheory.scalarQuotient B) q := by
    apply Subtype.ext
    ext i j
    exact h i j
  have hm : BC4lean.OperatorKTheory.FiniteProjection.map (BC4lean.OperatorKTheory.scalarQuotient B)
        (BC4lean.OperatorKTheory.finiteProjectionOfMatrix p) =
      BC4lean.OperatorKTheory.FiniteProjection.map (BC4lean.OperatorKTheory.scalarQuotient B)
        (BC4lean.OperatorKTheory.finiteProjectionOfMatrix q) := by
    rw [BC4lean.OperatorKTheory.finiteProjectionOfMatrix_map,
      BC4lean.OperatorKTheory.finiteProjectionOfMatrix_map, hpq]
  refine ⟨BC4lean.OperatorKTheory.k0Projection (BC4lean.OperatorKTheory.finiteProjectionOfMatrix p) -
    BC4lean.OperatorKTheory.k0Projection (BC4lean.OperatorKTheory.finiteProjectionOfMatrix q), ?_⟩
  change BC4lean.OperatorKTheory.k0Map (BC4lean.OperatorKTheory.scalarQuotient B) _ = 0
  rw [map_sub, BC4lean.OperatorKTheory.k0Map_projection, BC4lean.OperatorKTheory.k0Map_projection, hm, sub_self]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem equalScalarProjectionDifference_inclusion
    (p q : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    BC4lean.OperatorKTheory.operatorK0Inclusion B (equalScalarProjectionDifference p q h) =
      BC4lean.OperatorKTheory.k0Projection (BC4lean.OperatorKTheory.finiteProjectionOfMatrix p) -
        BC4lean.OperatorKTheory.k0Projection (BC4lean.OperatorKTheory.finiteProjectionOfMatrix q) := rfl

variable [TopologicalSpace.SeparableSpace B]

/-- Equal-scalar-part unitization projections give an actual even scalar-to-B cycle.
The operator is the supported off-diagonal (PQ, QP), not zero. -/
def unitizedRelativeProjectionCycle
    (p q : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
      (HilbertModuleSum B (UnitizedProjectionModule p) (UnitizedProjectionModule q)) :=
  relativeProjectionCycle (unitizedProjectionOperator p) (unitizedProjectionOperator q)
    (unitizedProjectionOperator_isStarProjection p) (unitizedProjectionOperator_isStarProjection q)
    (unitizedModuleMatrixRepresentation_sub_isModuleCompact p.val q.val h)
    finiteStandardModule_isCountablyGenerated_nonunital

/-- The diagonal unitization pair is exactly degenerate over the original B. -/
theorem unitizedRelativeProjectionCycle_diagonal_isDegenerate
    (p : BC4lean.OperatorKTheory.MatrixProjection (Unitization ℂ B) ι) :
    (unitizedRelativeProjectionCycle (Γ := Γ) p p (fun _ _ => rfl)).IsDegenerate :=
  relativeProjectionCycle_diagonal_isDegenerate _ _ _ _

end BC4lean.KKTheory
