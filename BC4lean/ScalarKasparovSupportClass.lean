import BC4lean.ScalarKasparovRectangularFredholm
import BC4lean.KasparovHomotopyGroup

/-! # Scalar support reduction in the genuine full homotopy group

The constructed compact support-block perturbation gives a full interval
homotopy through the proved operator-path-to-section construction. The actual
orthogonal support decomposition identifies its endpoint with the supported
cycle plus a zero-representation cycle. The latter has a genuine degenerate
cone homotopy. Symmetrization and the homogeneous unitary then give the actual
rectangular Fredholm representative for ordinary scalar cycles.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- Removing the compact off-support blocks and the degenerate complement
preserves the actual full-homotopy class. -/
theorem scalarSupport_class
    (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c.scalarSupportCycle) := by
  have hBlock : KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c.scalarSupportBlockCycle) := by
    simpa only [withOperator_self, scalarSupportBlockCycle] using
      KasparovHomotopyClass.mk_eq_of_full
        (FullKasparovHomotopy.ofOperatorHomotopy c.scalarSupportBlockHomotopy)
  calc
    KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
        KasparovHomotopyClass.mk (BundledKasparovCycle.of c.scalarSupportBlockCycle) := hBlock
    _ = KasparovHomotopyClass.mk
        ((BundledKasparovCycle.of c.scalarSupportCycle).directSum
          (BundledKasparovCycle.of c.scalarComplementCycle)) :=
      KasparovHomotopyClass.mk_eq_of_iso c.scalarSupportDirectSumIso.symm
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of c.scalarSupportCycle) +
        KasparovHomotopyClass.mk (BundledKasparovCycle.of c.scalarComplementCycle) :=
      KasparovHomotopyClass.mk_directSum _ _
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of c.scalarSupportCycle) := by
      rw [KasparovHomotopyClass.mk_eq_zero_of_degenerate
        (BundledKasparovCycle.of c.scalarComplementCycle) c.scalarComplementCycle_isDegenerate,
        add_zero]

/-- The actual supported affine symmetrization also preserves the full class. -/
theorem scalarSupportSelfadjoint_class
    (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c.scalarSupportSelfadjointCycle) := by
  apply c.scalarSupport_class.trans
  simpa only [withOperator_self, scalarSupportSelfadjointCycle] using
    KasparovHomotopyClass.mk_eq_of_full
      (FullKasparovHomotopy.ofOperatorHomotopy c.scalarSupportSymmetrizationHomotopy)

end KasparovCycle

namespace KasparovCycle

/-- Every ordinary scalar cycle has the constructed genuine rectangular
Fredholm cycle in its full-homotopy class. All global defects are derived from
the original localized Kasparov conditions after the actual support split. -/
theorem scalarRectangularFredholm_class
    (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B) E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (globalFredholmScalarCycle (Γ := PUnit) c.scalarRectangularFredholm
          c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
          c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated)) :=
  c.scalarSupportSelfadjoint_class.trans
    (KasparovHomotopyClass.mk_eq_of_iso c.scalarRectangularFredholmCycleIso)

end KasparovCycle
end BC4lean.KKTheory
