import BC4lean.OddKTheoryMatrixLoopFredholm
import BC4lean.OddKTheoryCountableGeneration
import BC4lean.FiniteProjectionKasparovCycle
import BC4lean.OddKasparovOperatorHomotopy

/-! # Genuine infinite odd cycles from matrix unitaries

A matrix unitary whose full scalar quotient is I gives an actual odd
Kasparov cycle on the genuine completed countable sum of finite B-valued
rows. The scalar representation is nonzero, and the Fredholm operator is the
actual periodic pullback. A scalar-identity unitary path gives an actual
operator homotopy of these cycles. No finite odd module or Bott comparison
is substituted for the genuine infinite construction.
-/

noncomputable section
namespace BC4lean.KKTheory

section ScalarFredholmCycle

variable {Γ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- An actual selfadjoint Fredholm operator supplies all four localized odd
cycle defects for the genuine scalar representation and trivial actions. -/
def oddKTheoryScalarFredholmCycle (hE : IsCountablyGeneratedModule B E)
    (F : AdjointableMap B E E) (hF : IsSelfAdjoint F)
    (hsq : IsModuleCompact (F * F - 1)) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) E where
  countablyGenerated := hE
  groupAction := EquivariantHilbertModule.trivial
  representation := scalarModuleRepresentation
  representation_equivariant := by intro g a; ext x; rfl
  operator := F
  selfadjoint_mod_compact := by
    intro a
    rw [hF.star_eq, sub_self, zero_mul]
    exact IsModuleCompact.zero
  square_mod_compact := by
    intro a
    exact hsq.comp_right (scalarModuleRepresentation a)
  commutator_compact := by
    intro a
    rw [scalarModuleRepresentation_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, sub_self]
    exact IsModuleCompact.zero
  equivariance_mod_compact := by
    intro g a
    have htriv : (EquivariantHilbertModule.trivial :
        EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) E).conjugateOperator
          g F = F := by
      ext x
      rfl
    rw [htriv, sub_self, zero_mul]
    exact IsModuleCompact.zero

@[simp] theorem oddKTheoryScalarFredholmCycle_operator
    (hE : IsCountablyGeneratedModule B E) (F : AdjointableMap B E E)
    (hF : IsSelfAdjoint F) (hsq : IsModuleCompact (F * F - 1)) :
    (oddKTheoryScalarFredholmCycle (Γ := Γ) hE F hF hsq).operator = F := rfl

@[simp] theorem oddKTheoryScalarFredholmCycle_representation
    (hE : IsCountablyGeneratedModule B E) (F : AdjointableMap B E E)
    (hF : IsSelfAdjoint F) (hsq : IsModuleCompact (F * F - 1)) (a : ℂ) :
    (oddKTheoryScalarFredholmCycle (Γ := Γ) hE F hF hsq).representation a =
      scalarModuleRepresentation a := rfl

end ScalarFredholmCycle

section MatrixCycles

variable {Γ B ι : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι] [TopologicalSpace.SeparableSpace B]

/-- The genuine infinite odd cycle of an actual matrix unitary with full
scalar matrix quotient I, over possibly nonunital separable B. -/
def oddKTheoryMatrixUnitaryCycle
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
      (CountableHilbertModuleSum B (FiniteStandardModule B ι)) :=
  oddKTheoryScalarFredholmCycle oddKTheoryCountableFiniteRows_isCountablyGenerated
    (oddKTheoryMatrixLoopPullback u) (oddKTheoryMatrixLoopPullback_isSelfAdjoint u)
    (oddKTheoryMatrixLoopPullback_square_isModuleCompact u hu)

@[simp] theorem oddKTheoryMatrixUnitaryCycle_operator
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    (oddKTheoryMatrixUnitaryCycle (Γ := Γ) u hu).operator = oddKTheoryMatrixLoopPullback u := rfl

@[simp] theorem oddKTheoryMatrixUnitaryCycle_representation
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) (a : ℂ) :
    (oddKTheoryMatrixUnitaryCycle (Γ := Γ) u hu).representation a =
      scalarModuleRepresentation a := rfl

set_option maxHeartbeats 1200000 in
/-- A genuine scalar-identity matrix-unitary path supplies an actual odd
operator homotopy on the fixed genuine completed countable row module. -/
def oddKTheoryMatrixUnitaryOperatorHomotopy
    {u v : unitary (CStarMatrix ι ι (Unitization ℂ B))}
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (p : Path u v)
    (hp : ∀ t : unitInterval,
      unitizationScalarMatrix (p t : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovOperatorHomotopy (oddKTheoryMatrixUnitaryCycle (Γ := Γ) u hu)
      (oddKTheoryMatrixLoopPullback u) (oddKTheoryMatrixLoopPullback v) where
  path :=
    { toFun := fun t => oddKTheoryMatrixLoopPullback (p t)
      continuous_toFun := continuous_oddKTheoryMatrixLoopPullback.comp p.continuous
      source' := congrArg oddKTheoryMatrixLoopPullback p.source
      target' := congrArg oddKTheoryMatrixLoopPullback p.target }
  conditions t := by
    constructor
    · intro a
      change IsModuleCompact ((oddKTheoryMatrixLoopPullback (p t) -
        star (oddKTheoryMatrixLoopPullback (p t))) *
          scalarModuleRepresentation (B := B)
            (E := CountableHilbertModuleSum B (FiniteStandardModule B ι)) a)
      rw [(oddKTheoryMatrixLoopPullback_isSelfAdjoint (p t)).star_eq, sub_self, zero_mul]
      exact IsModuleCompact.zero
    · intro a
      change IsModuleCompact ((oddKTheoryMatrixLoopPullback (p t) *
        oddKTheoryMatrixLoopPullback (p t) - 1) *
          scalarModuleRepresentation (B := B)
            (E := CountableHilbertModuleSum B (FiniteStandardModule B ι)) a)
      exact (oddKTheoryMatrixLoopPullback_square_isModuleCompact (p t) (hp t)).comp_right
        (scalarModuleRepresentation (B := B)
          (E := CountableHilbertModuleSum B (FiniteStandardModule B ι)) a)
    · intro a
      change IsModuleCompact (oddKTheoryMatrixLoopPullback (p t) *
        scalarModuleRepresentation (B := B)
          (E := CountableHilbertModuleSum B (FiniteStandardModule B ι)) a -
        scalarModuleRepresentation (B := B)
          (E := CountableHilbertModuleSum B (FiniteStandardModule B ι)) a *
            oddKTheoryMatrixLoopPullback (p t))
      rw [scalarModuleRepresentation_eq_smul_one, mul_smul_comm, smul_mul_assoc,
        mul_one, one_mul, sub_self]
      exact IsModuleCompact.zero
    · intro g a
      change IsModuleCompact (((EquivariantHilbertModule.trivial :
        EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
          (CountableHilbertModuleSum B (FiniteStandardModule B ι))).conjugateOperator g
            (oddKTheoryMatrixLoopPullback (p t)) - oddKTheoryMatrixLoopPullback (p t)) *
          scalarModuleRepresentation (B := B)
            (E := CountableHilbertModuleSum B (FiniteStandardModule B ι)) a)
      have htriv : (EquivariantHilbertModule.trivial :
          EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
            (CountableHilbertModuleSum B (FiniteStandardModule B ι))).conjugateOperator g
              (oddKTheoryMatrixLoopPullback (p t)) = oddKTheoryMatrixLoopPullback (p t) := by
        ext x
        rfl
      rw [htriv, sub_self, zero_mul]
      exact IsModuleCompact.zero

/-- The identity unitary gives an actual degenerate infinite odd cycle. -/
theorem oddKTheoryMatrixUnitaryCycle_one_isDegenerate :
    (oddKTheoryMatrixUnitaryCycle (Γ := Γ)
      (1 : unitary (CStarMatrix ι ι (Unitization ℂ B))) (by
        change unitizationScalarMatrix (1 : CStarMatrix ι ι (Unitization ℂ B)) = 1
        apply CStarMatrix.ext
        intro i j
        simp only [unitizationScalarMatrix_apply, CStarMatrix.one_apply]
        split_ifs <;> rfl)).IsDegenerate := by
  constructor
  · intro a
    rw [oddKTheoryMatrixUnitaryCycle_operator, oddKTheoryMatrixLoopPullback_one,
      oddKTheoryRowSignOperator_star, sub_self, zero_mul]
  constructor
  · intro a
    rw [oddKTheoryMatrixUnitaryCycle_operator, oddKTheoryMatrixLoopPullback_one,
      oddKTheoryRowSignOperator_square, sub_self, zero_mul]
  constructor
  · intro a
    rw [oddKTheoryMatrixUnitaryCycle_representation, scalarModuleRepresentation_eq_smul_one,
      mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]
  · intro g a
    have htriv : (oddKTheoryMatrixUnitaryCycle (Γ := Γ)
        (1 : unitary (CStarMatrix ι ι (Unitization ℂ B)))
        (by
        change unitizationScalarMatrix (1 : CStarMatrix ι ι (Unitization ℂ B)) = 1
        apply CStarMatrix.ext
        intro i j
        simp only [unitizationScalarMatrix_apply, CStarMatrix.one_apply]
        split_ifs <;> rfl)).groupAction.conjugateOperator g
          (oddKTheoryMatrixLoopPullback (1 : unitary (CStarMatrix ι ι (Unitization ℂ B)))) =
        oddKTheoryMatrixLoopPullback (1 : unitary (CStarMatrix ι ι (Unitization ℂ B))) := by
      ext x
      rfl
    rw [oddKTheoryMatrixUnitaryCycle_operator, htriv, sub_self, zero_mul]

end MatrixCycles
end BC4lean.KKTheory
