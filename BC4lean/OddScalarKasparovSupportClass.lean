import BC4lean.OddScalarKasparovSupport
import BC4lean.OddFredholmFullNormalization

/-! # Genuine odd scalar support reduction in the actual full homotopy group

Every scalar representation, including a degenerate one, is reduced to the
actual complete range of φ(1). The compact block-removal path supplies a full
witness, the actual orthogonal split identifies the complement, and its zero
representation vanishes through the genuine degenerate cone. The supported
selfadjoint contractive representative has a global compact square defect.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

variable (c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E)

/-- The genuine supported, symmetrized operator. -/
def scalarSupportSelfadjointOperator :=
  c.scalarSupportCycle.operator + c.scalarSupportCycle.symmetrizingPerturbation

theorem scalarSupportSelfadjointOperator_isSelfAdjoint :
    IsSelfAdjoint c.scalarSupportSelfadjointOperator :=
  c.scalarSupportCycle.symmetrizedOperator_selfadjoint

@[simp] theorem scalarSupportRepresentation_one : c.scalarSupportRepresentation 1 = 1 := by
  ext x
  simp only [c.scalarSupportRepresentation_apply, one_smul, AdjointableMap.one_apply]

/-- The original cycle at the scalar unit gives a globally compact square
defect for the supported selfadjoint representative. -/
theorem scalarSupportSelfadjointOperator_square_isModuleCompact :
    IsModuleCompact (c.scalarSupportSelfadjointOperator * c.scalarSupportSelfadjointOperator - 1) := by
  have hh := c.scalarSupportCycle.operatorConditions_symmetrization.square_mod_compact 1
  change IsModuleCompact ((c.scalarSupportSelfadjointOperator * c.scalarSupportSelfadjointOperator - 1) *
    c.scalarSupportRepresentation 1) at hh
  rwa [c.scalarSupportRepresentation_one, mul_one] at hh

/-- The actual supported selfadjoint cycle. -/
def scalarSupportSelfadjointCycle :=
  c.scalarSupportCycle.withOperator c.scalarSupportSelfadjointOperator
    c.scalarSupportCycle.operatorConditions_symmetrization

/-- The actual affine homotopy to the selfadjoint supported endpoint. -/
def scalarSupportSymmetrizationHomotopy :
    OddKasparovOperatorHomotopy c.scalarSupportCycle c.scalarSupportCycle.operator
      c.scalarSupportSelfadjointOperator := c.scalarSupportCycle.symmetrizationHomotopy

/-- The actual supported selfadjoint contractive odd representative. -/
def scalarSupportNormalizedCycle := c.scalarSupportCycle.normalized

theorem scalarSupportNormalizedCycle_selfadjoint :
    IsSelfAdjoint c.scalarSupportNormalizedCycle.operator := c.scalarSupportCycle.normalized_selfadjoint

theorem scalarSupportNormalizedCycle_norm_le_one :
    ‖c.scalarSupportNormalizedCycle.operator‖ ≤ 1 := c.scalarSupportCycle.normalized_norm_le_one

/-- Global compactness is derived from the original localized cycle at the
scalar unit after the actual support reduction. -/
theorem scalarSupportNormalizedCycle_square_isModuleCompact :
    IsModuleCompact (c.scalarSupportNormalizedCycle.operator *
      c.scalarSupportNormalizedCycle.operator - 1) := by
  have hh := c.scalarSupportNormalizedCycle.square_mod_compact 1
  change IsModuleCompact ((c.scalarSupportNormalizedCycle.operator *
    c.scalarSupportNormalizedCycle.operator - 1) * c.scalarSupportRepresentation 1) at hh
  rwa [c.scalarSupportRepresentation_one, mul_one] at hh

variable [TopologicalSpace.SeparableSpace B]

/-- Removing the compact off-support blocks and the degenerate complement
preserves the actual full-homotopy class. -/
theorem scalarSupport_class
    (c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E) :
    OddKK.mk (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportCycle) := by
  have hBlock : OddKK.mk (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportBlockCycle) := by
    simpa only [withOperator_self, scalarSupportBlockCycle] using
      OddKK.mk_eq_of_full
        (FullOddKasparovHomotopy.ofOperatorHomotopy c.scalarSupportBlockHomotopy)
  calc
    OddKK.mk (BundledOddKasparovCycle.of c) =
        OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportBlockCycle) := hBlock
    _ = OddKK.mk
        ((BundledOddKasparovCycle.of c.scalarSupportCycle).directSum
          (BundledOddKasparovCycle.of c.scalarComplementCycle)) :=
      OddKK.mk_eq_of_iso c.scalarSupportDirectSumIso.symm
    _ = OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportCycle) +
        OddKK.mk (BundledOddKasparovCycle.of c.scalarComplementCycle) :=
      OddKK.mk_directSum _ _
    _ = OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportCycle) := by
      rw [OddKK.mk_eq_zero_of_degenerate
        (BundledOddKasparovCycle.of c.scalarComplementCycle) c.scalarComplementCycle_isDegenerate,
        add_zero]

/-- The actual supported affine symmetrization also preserves the full class. -/
theorem scalarSupportSelfadjoint_class
    (c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E) :
    OddKK.mk (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportSelfadjointCycle) := by
  apply c.scalarSupport_class.trans
  simpa only [withOperator_self, scalarSupportSelfadjointCycle] using
    OddKK.mk_eq_of_full
      (FullOddKasparovHomotopy.ofOperatorHomotopy c.scalarSupportSymmetrizationHomotopy)

/-- Every possibly degenerate odd scalar cycle has the constructed actual
supported selfadjoint contraction in its genuine full-homotopy class. -/
theorem scalarSupportNormalized_class :
    OddKK.mk (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c.scalarSupportNormalizedCycle) :=
  c.scalarSupport_class.trans c.scalarSupportCycle.normalized_class

end OddKasparovCycle
end BC4lean.KKTheory
