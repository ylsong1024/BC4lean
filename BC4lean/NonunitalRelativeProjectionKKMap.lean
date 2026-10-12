import BC4lean.UnitizationRelativeStableKKMap
import BC4lean.UnitizationRelativeProjectionK0

/-! # The genuine nonunital K0-to-scalar-KK homomorphism

The actual Grothendieck map is restricted along the repository's scalar-kernel
inclusion. For every pair with identical full scalar matrices, the constructed
relative cocycle proves that the image of its K0 difference is its actual
relative Kasparov cycle. No normal-form surjectivity or index descent is assumed.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

/-- Restriction to the actual already defined scalar kernel. -/
def nonunitalRelativeK0KasparovMap : OperatorK0 B →+ RelativeScalarKasparovGroup (B := B) :=
  unitizationK0RelativeKKMap.comp (operatorK0Inclusion B)

omit B [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] in
/-- Equal complete scalar matrices give exactly the same actual scalar shadow. -/
theorem unitizationScalarShadowProjection_eq_of_scalar_eq
    {B : Type u} [NonUnitalCStarAlgebra B] [hOrder : PartialOrder B]
    [hStarOrder : StarOrderedRing B] [hSeparable : TopologicalSpace.SeparableSpace B]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    unitizationScalarShadowProjection p = unitizationScalarShadowProjection q := by
  let _ := hOrder
  let _ := hStarOrder
  let _ := hSeparable
  apply Subtype.ext
  apply CStarMatrix.ext
  intro i j
  change scalarSection B (p.val i j).fst = scalarSection B (q.val i j).fst
  rw [h i j]

/-- The actual cocycle identifies the difference of scalar-relative classes
with the genuine relative cycle for an equal-scalar pair. -/
theorem unitizationScalarRelativeClass_difference
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    unitizationScalarRelativeClass p - unitizationScalarRelativeClass q =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (unitizedRelativeProjectionCycle (Γ := PUnit) p q h)) := by
  have hs := unitizationScalarShadowProjection_eq_of_scalar_eq p q h
  have hCocycle := relativeProjectionCocycle_class (Γ := PUnit)
    (unitizedProjectionOperator p) (unitizedProjectionOperator q)
    (unitizedProjectionOperator (unitizationScalarShadowProjection q))
    (unitizedProjectionOperator_isStarProjection p) (unitizedProjectionOperator_isStarProjection q)
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection q))
    (unitizedModuleMatrixRepresentation_sub_isModuleCompact p.val q.val h)
    (unitizedModuleMatrixRepresentation_sub_isModuleCompact q.val
      (unitizationScalarShadowProjection q).val (unitizationScalarShadowProjection_scalar q))
    finiteStandardModule_isCountablyGenerated_nonunital
  have hcPR : IsModuleCompact (unitizedProjectionOperator p -
      unitizedProjectionOperator (unitizationScalarShadowProjection q)) :=
    relativeProjectionCocycle_difference_compact
      (unitizedProjectionOperator p) (unitizedProjectionOperator q)
      (unitizedProjectionOperator (unitizationScalarShadowProjection q))
      (unitizedModuleMatrixRepresentation_sub_isModuleCompact p.val q.val h)
      (unitizedModuleMatrixRepresentation_sub_isModuleCompact q.val
        (unitizationScalarShadowProjection q).val (unitizationScalarShadowProjection_scalar q))
  have hShadowOperator : unitizedProjectionOperator (unitizationScalarShadowProjection q) =
      unitizedProjectionOperator (unitizationScalarShadowProjection p) :=
    congrArg unitizedProjectionOperator hs.symm
  have hTerminalClass
      (P' Q' : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
      (hP' : IsStarProjection P') (hQ' : IsStarProjection Q')
      (hc' : IsModuleCompact (P' - Q'))
      (hE' : IsCountablyGeneratedModule B (FiniteStandardModule B ι))
      (hPoperator : P' = unitizedProjectionOperator p)
      (hQoperator : Q' = unitizedProjectionOperator (unitizationScalarShadowProjection p)) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P' Q' hP' hQ' hc' hE')) =
      unitizationScalarRelativeClass p := by
    subst P'
    subst Q'
    rfl
  have hTerminal := hTerminalClass (unitizedProjectionOperator p)
    (unitizedProjectionOperator (unitizationScalarShadowProjection q))
    (unitizedProjectionOperator_isStarProjection p)
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection q))
    hcPR finiteStandardModule_isCountablyGenerated_nonunital rfl hShadowOperator
  have hAdd : KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (unitizedRelativeProjectionCycle (Γ := PUnit) p q h)) + unitizationScalarRelativeClass q =
        unitizationScalarRelativeClass p := by
    exact hCocycle.trans hTerminal
  exact (eq_sub_of_add_eq hAdd).symm

/-- The actual kernel projection difference maps to the whole genuine relative cycle. -/
@[simp] theorem nonunitalRelativeK0KasparovMap_equalScalarProjectionDifference
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    nonunitalRelativeK0KasparovMap (equalScalarProjectionDifference p q h) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (unitizedRelativeProjectionCycle (Γ := PUnit) p q h)) := by
  rw [nonunitalRelativeK0KasparovMap, AddMonoidHom.comp_apply,
    equalScalarProjectionDifference_inclusion,
    k0Projection_finiteProjectionOfMatrix, k0Projection_finiteProjectionOfMatrix, map_sub,
    unitizationK0RelativeKKMap_projection, unitizationK0RelativeKKMap_projection]
  exact unitizationScalarRelativeClass_difference p q h

/-- The same formula applies to the actual matrix-based scalar-kernel constructor. -/
theorem nonunitalRelativeK0KasparovMap_unitizationRelativeProjectionK0
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q : CStarMatrix ι ι (Unitization ℂ B))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hs : unitizationScalarMatrix P = unitizationScalarMatrix Q) :
    nonunitalRelativeK0KasparovMap (unitizationRelativeProjectionK0 P Q hP hQ hs) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (unitizedRelativeProjectionCycle (Γ := PUnit) ⟨P, hP⟩ ⟨Q, hQ⟩
          (fun i j => congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hs))) := by
  have hClass : unitizationRelativeProjectionK0 P Q hP hQ hs =
      equalScalarProjectionDifference (⟨P, hP⟩ : MatrixProjection (Unitization ℂ B) ι)
        ⟨Q, hQ⟩ (fun i j => congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hs) := by
    apply operatorK0Inclusion_injective B
    have hInclusion := equalScalarProjectionDifference_inclusion
      (⟨P, hP⟩ : MatrixProjection (Unitization ℂ B) ι) ⟨Q, hQ⟩
      (fun i j => congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hs)
    have hFiniteClasses := congrArg₂ (fun a b : K0 (Unitization ℂ B) => a - b)
      (k0Projection_finiteProjectionOfMatrix
        (⟨P, hP⟩ : MatrixProjection (Unitization ℂ B) ι))
      (k0Projection_finiteProjectionOfMatrix
        (⟨Q, hQ⟩ : MatrixProjection (Unitization ℂ B) ι))
    exact (operatorK0Inclusion_unitizationRelativeProjectionK0 P Q hP hQ hs).trans
      (hFiniteClasses.symm.trans hInclusion.symm)
  rw [hClass]
  exact nonunitalRelativeK0KasparovMap_equalScalarProjectionDifference _ _ _

end BC4lean.KKTheory
