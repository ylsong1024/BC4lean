import BC4lean.OddFredholmRowNormalFormHomotopy
import BC4lean.OddFredholmFullNormalization
import BC4lean.ProjectionHilbertModuleSplit

/-! # The actual zero-row and degenerate-tail decomposition

The zero row is genuinely unitarily isomorphic to E. Its orthogonal
complement is the complete range of I-P₀ and carries the restriction of the
actual sign symmetry. An actual whole-cycle unitary identifies the stabilized
operator with F direct sum this exactly degenerate tail. Consequently the
explicit row normal-form homotopy starts in the original full quotient class.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

theorem oddFredholmRowZeroProjection_isStarProjection :
    IsStarProjection (oddKTheoryRowZeroProjection (B := B) (E := E)) :=
  isStarProjection_iff'.mpr
    ⟨oddKTheoryRowZeroProjection_square, oddKTheoryRowZeroProjection_star⟩

/-- The actual zero row, with its genuine coefficient-valued module unitary. -/
def oddFredholmRowZeroEquiv :
    HilbertModuleEquiv B E (ProjectionModule (oddKTheoryRowZeroProjection (B := B) (E := E))) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨countableModuleInclusion 0 x, by
            change countableModuleInclusion 0
              (countableModuleEvaluation 0 (countableModuleInclusion 0 x)) =
                countableModuleInclusion 0 x
            simp only [countableModuleEvaluation_inclusion, if_true]⟩
          invFun := fun x => countableModuleEvaluation 0 (x : CountableHilbertModuleSum B E)
          left_inv := fun x => by
            simp only [countableModuleEvaluation_inclusion, if_true]
          right_inv := fun x => Subtype.ext x.property
          map_add' := fun x y => Subtype.ext ((countableModuleInclusion 0).toCLM.map_add x y)
          map_smul' := fun z x => Subtype.ext ((countableModuleInclusion 0).toCLM.map_smul z x) }
      norm_map' x := countableModuleInclusion_norm 0 x }
  inner_map x y := by
    change ⟪countableModuleInclusion (B := B) (E := E) 0 x, countableModuleInclusion (B := B) (E := E) 0 y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [(countableModuleInclusion (B := B) (E := E) 0).adjoint_identity]
    change ⟪x, countableModuleEvaluation 0 (countableModuleInclusion 0 y)⟫_(Bᵐᵒᵖ) = _
    rw [countableModuleEvaluation_inclusion, if_pos rfl]

@[simp] theorem oddFredholmRowZeroEquiv_coe (x : E) :
    (oddFredholmRowZeroEquiv (B := B) (E := E) x : CountableHilbertModuleSum B E) = countableModuleInclusion 0 x := rfl

/-- The genuine complete tail module, without the zero coordinate. -/
abbrev OddFredholmRowTailModule (B E : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] :=
  ProjectionModule (1 - oddKTheoryRowZeroProjection (B := B) (E := E))

theorem oddFredholmRowSign_commutes_complement :
    oddKTheoryRowSignOperator (B := B) (E := E) * (1 - oddKTheoryRowZeroProjection) =
      (1 - oddKTheoryRowZeroProjection) * oddKTheoryRowSignOperator := by
  simp only [mul_sub, sub_mul, mul_one, one_mul,
    oddKTheoryRowSign_mul_zeroProjection, oddKTheoryRowZeroProjection_mul_sign]

/-- Restrict the actual sign operator to its actual complete complementary range. -/
def oddFredholmRowTailSign :
    AdjointableMap B (OddFredholmRowTailModule B E) (OddFredholmRowTailModule B E) :=
  ((projectionCorestrict (1 - oddKTheoryRowZeroProjection)
    oddFredholmRowZeroProjection_isStarProjection.one_sub).comp oddKTheoryRowSignOperator).comp
      (projectionInclusion (1 - oddKTheoryRowZeroProjection)
        oddFredholmRowZeroProjection_isStarProjection.one_sub)

@[simp] theorem oddFredholmRowTailSign_coe (x : OddFredholmRowTailModule B E) :
    (oddFredholmRowTailSign x : CountableHilbertModuleSum B E) =
      oddKTheoryRowSignOperator (x : CountableHilbertModuleSum B E) := by
  have hh := congrArg (fun T : OddKTheoryCountableOperator B E =>
    T (x : CountableHilbertModuleSum B E)) oddFredholmRowSign_commutes_complement
  change oddKTheoryRowSignOperator ((1 - oddKTheoryRowZeroProjection)
    (x : CountableHilbertModuleSum B E)) =
      (1 - oddKTheoryRowZeroProjection) (oddKTheoryRowSignOperator
        (x : CountableHilbertModuleSum B E)) at hh
  rw [x.property] at hh
  exact hh.symm

theorem oddFredholmRowTailSign_star :
    star (oddFredholmRowTailSign (B := B) (E := E)) = oddFredholmRowTailSign := by
  have hstar : star (oddFredholmRowTailSign (B := B) (E := E)) =
      ((projectionCorestrict (1 - oddKTheoryRowZeroProjection)
        oddFredholmRowZeroProjection_isStarProjection.one_sub).comp
          (star oddKTheoryRowSignOperator)).comp
            (projectionInclusion (1 - oddKTheoryRowZeroProjection)
              oddFredholmRowZeroProjection_isStarProjection.one_sub) := by
    ext x
    rfl
  rw [hstar, oddKTheoryRowSignOperator_star]
  rfl

theorem oddFredholmRowTailSign_square :
    oddFredholmRowTailSign (B := B) (E := E) * oddFredholmRowTailSign = 1 := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  simp only [AdjointableMap.mul_apply, oddFredholmRowTailSign_coe, AdjointableMap.one_apply]
  have hh := congrArg (fun T : OddKTheoryCountableOperator B E =>
    T (x : CountableHilbertModuleSum B E)) oddKTheoryRowSignOperator_square
  exact hh

theorem oddFredholmRowTailModule_isCountablyGenerated (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B (OddFredholmRowTailModule B E) :=
  projectionModule_isCountablyGenerated (1 - oddKTheoryRowZeroProjection)
    oddFredholmRowZeroProjection_isStarProjection.one_sub
      (oddKTheoryCountableModule_countablyGenerated hE)

/-- The genuine tail cycle has nonzero scalar representation and exact
selfadjoint unitary sign operator, so every defect vanishes. -/
def oddFredholmRowTailCycle (hE : IsCountablyGeneratedModule B E) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (OddFredholmRowTailModule B E) :=
  oddKTheoryScalarFredholmCycle (oddFredholmRowTailModule_isCountablyGenerated hE)
    oddFredholmRowTailSign oddFredholmRowTailSign_star (by
      rw [oddFredholmRowTailSign_square, sub_self]
      exact IsModuleCompact.zero)

theorem oddFredholmRowTailCycle_isDegenerate (hE : IsCountablyGeneratedModule B E) :
    (oddFredholmRowTailCycle (Γ := Γ) hE).IsDegenerate := by
  constructor
  · intro a
    change (oddFredholmRowTailSign - star oddFredholmRowTailSign) *
      scalarModuleRepresentation a = 0
    rw [oddFredholmRowTailSign_star, sub_self, zero_mul]
  constructor
  · intro a
    change (oddFredholmRowTailSign * oddFredholmRowTailSign - 1) *
      scalarModuleRepresentation a = 0
    rw [oddFredholmRowTailSign_square, sub_self, zero_mul]
  constructor
  · intro a
    change oddFredholmRowTailSign * scalarModuleRepresentation a -
      scalarModuleRepresentation a * oddFredholmRowTailSign = 0
    rw [scalarModuleRepresentation_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, sub_self]
  · intro g a
    have htriv : (oddFredholmRowTailCycle (Γ := Γ) hE).groupAction.conjugateOperator g
        oddFredholmRowTailSign = oddFredholmRowTailSign := by
      ext x
      rfl
    change ((oddFredholmRowTailCycle (Γ := Γ) hE).groupAction.conjugateOperator g
      oddFredholmRowTailSign - oddFredholmRowTailSign) * scalarModuleRepresentation a = 0
    rw [htriv, sub_self, zero_mul]

/-- The actual orthogonal decomposition inserts E in the genuine zero row. -/
def oddFredholmRowDecompositionEquiv :
    HilbertModuleEquiv B (HilbertModuleSum B E (OddFredholmRowTailModule B E))
      (CountableHilbertModuleSum B E) :=
  (oddFredholmRowZeroEquiv.sum HilbertModuleEquiv.refl).trans
    (projectionModuleSplitEquiv oddKTheoryRowZeroProjection
      oddFredholmRowZeroProjection_isStarProjection).symm

@[simp] theorem oddFredholmRowDecompositionEquiv_apply
    (x : HilbertModuleSum B E (OddFredholmRowTailModule B E)) :
    oddFredholmRowDecompositionEquiv x =
      countableModuleInclusion 0 x.fst + (x.snd : CountableHilbertModuleSum B E) := rfl

theorem oddFredholmRowStabilizedOperator_tail
    (F : selfAdjoint (AdjointableMap B E E)) (x : OddFredholmRowTailModule B E) :
    oddFredholmRowStabilizedOperator F (x : CountableHilbertModuleSum B E) =
      oddKTheoryRowSignOperator (x : CountableHilbertModuleSum B E) := by
  simp only [oddFredholmRowStabilizedOperator, AdjointableMap.coe_add_apply,
    AdjointableMap.mul_apply, projection_complement_fixed_eq_zero,
    map_zero, add_zero]

set_option maxHeartbeats 1200000 in
/-- One actual module unitary intertwines the scalar representation,
trivial action, and the full stabilized Fredholm operator. -/
def oddFredholmRowDecompositionCycleIso (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    OddKasparovCycleIso
      ((oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF).directSum
        (oddFredholmRowTailCycle (Γ := Γ) hE)) (oddFredholmRowStabilizedCycle (Γ := Γ) hE F hF) where
  moduleEquiv := (oddFredholmRowDecompositionEquiv (B := B) (E := E) :
    HilbertModuleEquiv B (HilbertModuleSum B E (OddFredholmRowTailModule B E))
      (CountableHilbertModuleSum B E))
  action_intertwine g x := by
    dsimp only [OddKasparovCycle.directSum, oddFredholmRowTailCycle,
      oddFredholmRowStabilizedCycle, oddKTheoryScalarFredholmCycle]
    simp only [EquivariantHilbertModule.sum_action_apply] ; rfl
  representation_intertwine a x := by
    dsimp only [OddKasparovCycle.directSum, oddFredholmRowTailCycle,
      oddFredholmRowStabilizedCycle, oddKTheoryScalarFredholmCycle]
    simp only [sumRepresentation_apply (B := B), sumMap_apply (B := B),
      scalarModuleRepresentation_apply (B := B)]
    simpa only [sumMk_smul, sumMk_eta] using!
      (oddFredholmRowDecompositionEquiv (B := B) (E := E)).map_smul a
        (sumMk (B := B) x.fst x.snd)
  operator_intertwine x := by
    simp only [OddKasparovCycle.directSum_operator]
    dsimp only [oddFredholmRowTailCycle, oddFredholmRowStabilizedCycle,
      oddKTheoryScalarFredholmCycle]
    simp only [sumMap_apply (B := B), oddFredholmRowDecompositionEquiv_apply,
      sumMk_fst, sumMk_snd]
    rw [oddFredholmRowTailSign_coe (B := B) (E := E),
      (oddFredholmRowStabilizedOperator (B := B) (E := E) F).toCLM.map_add,
      oddFredholmRowStabilizedOperator_tail (B := B) (E := E)]
    have hzero := oddFredholmRowStabilizedOperator_inclusion (B := B) (E := E) F 0 x.fst
    simpa only [oddKTheoryRowIntegerInclusion, oddKTheoryRowIntegerIndex_zero,
      if_true] using congrArg
        (fun z : CountableHilbertModuleSum B E =>
          z + oddKTheoryRowSignOperator (B := B) (E := E)
            (x.snd : CountableHilbertModuleSum B E)) hzero.symm

variable [TopologicalSpace.SeparableSpace B]

/-- The genuine stabilized row cycle has exactly the original scalar
Fredholm full-homotopy class, by the actual split and the actual cone. -/
theorem oddFredholmRowStabilizedCycle_class (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    OddKK.mk (BundledOddKasparovCycle.of (oddFredholmRowStabilizedCycle (Γ := Γ) hE F hF)) =
      OddKK.mk (BundledOddKasparovCycle.of (oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF)) := by
  have hTailClass : OddKK.mk (BundledOddKasparovCycle.of
      (oddFredholmRowTailCycle (Γ := Γ) hE)) = 0 :=
    OddKK.mk_eq_zero_of_degenerate
      (BundledOddKasparovCycle.of (oddFredholmRowTailCycle (Γ := Γ) hE))
      (oddFredholmRowTailCycle_isDegenerate (Γ := Γ) hE)
  calc
    _ = OddKK.mk ((BundledOddKasparovCycle.of
        (oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF)).directSum
          (BundledOddKasparovCycle.of (oddFredholmRowTailCycle (Γ := Γ) hE))) :=
      OddKK.mk_eq_of_iso
        (c := BundledOddKasparovCycle.of (oddFredholmRowStabilizedCycle (Γ := Γ) hE F hF))
        (d := (BundledOddKasparovCycle.of
          (oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF)).directSum
            (BundledOddKasparovCycle.of (oddFredholmRowTailCycle (Γ := Γ) hE)))
        (oddFredholmRowDecompositionCycleIso (Γ := Γ) (B := B) (E := E) hE F hF).symm
    _ = _ := by
      rw [OddKK.mk_directSum, hTailClass, add_zero]

end BC4lean.KKTheory
