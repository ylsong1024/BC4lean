import BC4lean.OddFredholmRowNormalForm

/-! # Actual odd-cycle homotopy for arbitrary scalar Fredholm operators

The explicit commuting-phase path is bundled as an actual odd Kasparov
operator homotopy on a genuinely countably generated countable row module.
All four localized defects are proved from the actual selfadjoint compact
square conditions. This does not assume an abstract normal-form homotopy.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The actual compact square defect of the arbitrary-F stabilized operator. -/
theorem oddFredholmRowStabilizedOperator_square_isModuleCompact
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    IsModuleCompact (oddFredholmRowStabilizedOperator F * oddFredholmRowStabilizedOperator F - 1) := by
  rw [oddFredholmRowStabilizedOperator_square_defect]
  exact (hF.comp_left (oddKTheoryRowIntegerInclusion 0)).comp_right (oddKTheoryRowIntegerEvaluation 0)

/-- The actual odd scalar cycle on the genuinely stabilized row module. -/
def oddFredholmRowStabilizedCycle (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (CountableHilbertModuleSum B E) :=
  oddKTheoryScalarFredholmCycle (Γ := Γ) (B := B) (E := CountableHilbertModuleSum B E)
    (oddKTheoryCountableModule_countablyGenerated hE)
    (oddFredholmRowStabilizedOperator F : OddKTheoryCountableOperator B E)
    (oddFredholmRowStabilizedOperator_isSelfAdjoint F)
    (oddFredholmRowStabilizedOperator_square_isModuleCompact F hF)

set_option maxHeartbeats 1200000 in
/-- The explicit actual-module odd normal-form operator homotopy, with every
localized Kasparov defect proved along the whole path. -/
def oddFredholmRowNormalFormHomotopy (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    OddKasparovOperatorHomotopy (oddFredholmRowStabilizedCycle (Γ := Γ) hE F hF)
      (oddFredholmRowStabilizedOperator F) (oddFredholmRowNormalFormOperator F 1) where
  path :=
    { toFun := fun s => oddFredholmRowNormalFormOperator F s
      continuous_toFun := (continuous_oddFredholmRowNormalFormOperator F).comp continuous_subtype_val
      source' := oddFredholmRowNormalFormOperator_zero F
      target' := rfl }
  conditions s := by
    constructor
    · intro a
      change IsModuleCompact ((oddFredholmRowNormalFormOperator F s -
        star (oddFredholmRowNormalFormOperator F s)) *
          scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
      rw [(oddFredholmRowNormalFormOperator_isSelfAdjoint (B := B) (E := E) F s).star_eq,
        sub_self, zero_mul]
      exact IsModuleCompact.zero (B := B) (E := CountableHilbertModuleSum B E)
        (F := CountableHilbertModuleSum B E)
    · intro a
      change IsModuleCompact ((oddFredholmRowNormalFormOperator F s *
        oddFredholmRowNormalFormOperator F s - 1) *
          scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
      exact (oddFredholmRowNormalFormOperator_square_isModuleCompact (B := B) (E := E)
        F hF s).comp_right
          (scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
    · intro a
      change IsModuleCompact (oddFredholmRowNormalFormOperator F s *
        scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a -
        scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a *
          oddFredholmRowNormalFormOperator F s)
      rw [scalarModuleRepresentation_eq_smul_one, mul_smul_comm, smul_mul_assoc,
        mul_one, one_mul, sub_self]
      exact IsModuleCompact.zero (B := B) (E := CountableHilbertModuleSum B E)
        (F := CountableHilbertModuleSum B E)
    · intro g a
      change IsModuleCompact (((EquivariantHilbertModule.trivial :
        EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
          (CountableHilbertModuleSum B E)).conjugateOperator g
            (oddFredholmRowNormalFormOperator F s) - oddFredholmRowNormalFormOperator F s) *
          scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
      have htriv : (EquivariantHilbertModule.trivial :
          EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
            (CountableHilbertModuleSum B E)).conjugateOperator g
              (oddFredholmRowNormalFormOperator F s) = oddFredholmRowNormalFormOperator F s := by
        ext x
        rfl
      rw [htriv, sub_self, zero_mul]
      exact IsModuleCompact.zero (B := B) (E := CountableHilbertModuleSum B E)
        (F := CountableHilbertModuleSum B E)

end BC4lean.KKTheory
