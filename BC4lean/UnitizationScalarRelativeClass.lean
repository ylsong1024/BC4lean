import BC4lean.AdjointableUnitaryHilbertModuleEquiv
import BC4lean.UnitizationScalarProjectionCorrection
import BC4lean.RelativeProjectionCocycle

/-! # Unitary invariance of the genuine scalar-relative projection class

A projection p is compared to its actual scalar shadow on the original finite
B-module. Its genuine relative class is unchanged by conjugation with a matrix
unitary. The proof combines whole-cycle unitary transport, the constructed
scalar-correcting compact partial isometry and the actual relative cocycle.
This leaf does not yet claim stable-monoid or Grothendieck descent.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type u} {ι : Type} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [Fintype ι] [DecidableEq ι]

local instance scalarRelativeUnitizationOrder : PartialOrder (Unitization ℂ B) :=
  CStarAlgebra.spectralOrder _
local instance scalarRelativeUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ B) :=
  CStarAlgebra.spectralOrderedRing _

/-- The finite unitization action preserves the true identity operator. -/
@[simp] theorem unitizedModuleMatrixRepresentation_one :
    unitizedModuleMatrixRepresentation (1 : CStarMatrix ι ι (Unitization ℂ B)) =
      (1 : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) := by
  ext x i
  rw [unitizedModuleMatrixRepresentation_apply, AdjointableMap.one_apply]
  have hEntry (j : ι) :
      unitizedStandardLeftMul ((1 : CStarMatrix ι ι (Unitization ℂ B)) i j) (x j) =
        if i = j then x j else 0 := by
    by_cases hij : i = j
    · rw [CStarMatrix.one_apply, if_pos hij, map_one,
        AdjointableMap.one_apply, if_pos hij]
    · rw [CStarMatrix.one_apply, if_neg hij, map_zero,
        AdjointableMap.coe_zero_apply, if_neg hij]
  calc
    _ = ∑ j : ι, if i = j then x j else 0 :=
      Finset.sum_congr rfl (fun j _ => hEntry j)
    _ = x i := Fintype.sum_ite_eq i x

/-- A matrix unitary acts as an actual adjointable unitary on the original B-module. -/
def unitizedMatrixUnitaryOperator (U : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :=
  ⟨unitizedModuleMatrixRepresentation U.val, by
    constructor
    · rw [← map_star, ← map_mul, U.property.1, unitizedModuleMatrixRepresentation_one]
    · rw [← map_star, ← map_mul, U.property.2, unitizedModuleMatrixRepresentation_one]⟩

/-- The actual matrix unitary gives a true coefficient-inner-product unitary. -/
def unitizedMatrixUnitaryEquiv (U : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    HilbertModuleEquiv B (FiniteStandardModule B ι) (FiniteStandardModule B ι) :=
  HilbertModuleEquiv.ofAdjointableUnitary (unitizedMatrixUnitaryOperator U)

/-- Actual operator conjugation agrees with actual matrix conjugation. -/
theorem unitizedMatrixUnitaryEquiv_transport
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (M : CStarMatrix ι ι (Unitization ℂ B)) :
    (unitizedMatrixUnitaryEquiv U).transport (unitizedModuleMatrixRepresentation M) =
      unitizedModuleMatrixRepresentation (U.val * M * star U.val) := by
  apply AdjointableMap.ext
  intro x
  rw [HilbertModuleEquiv.transport_apply]
  change unitizedModuleMatrixRepresentation U.val
    (unitizedModuleMatrixRepresentation M
      ((star (unitizedModuleMatrixRepresentation U.val)) x)) = _
  rw [map_mul, map_mul, map_star]
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- The full scalar parts of a projection and its actual scalar shadow agree. -/
theorem unitizationScalarShadowProjection_scalar [PartialOrder B] [StarOrderedRing B]
    (p : MatrixProjection (Unitization ℂ B) ι) :
    ∀ i j, (p.val i j).fst = ((unitizationScalarShadowProjection p).val i j).fst := by
  intro i j
  rfl

variable [TopologicalSpace.SeparableSpace B]

/-- The genuine scalar-relative full homotopy class of one finite projection. -/
def unitizationScalarRelativeClass (p : MatrixProjection (Unitization ℂ B) ι) :=
  KasparovHomotopyClass.mk (BundledKasparovCycle.of
    (unitizedRelativeProjectionCycle (Γ := PUnit) p (unitizationScalarShadowProjection p)
      (unitizationScalarShadowProjection_scalar p)))

/-- Actual unitary conjugation preserves the scalar-relative full class. -/
theorem unitizationScalarRelativeClass_unitaryConjugate
    (U : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (p : MatrixProjection (Unitization ℂ B) ι) :
    unitizationScalarRelativeClass p = unitizationScalarRelativeClass (unitaryProjectionConjugate U p) := by
  let q := unitaryProjectionConjugate U p
  let r := unitaryProjectionConjugate U (unitizationScalarShadowProjection p)
  let s := unitizationScalarShadowProjection q
  let W := unitizedMatrixUnitaryEquiv U
  have hc : IsModuleCompact (unitizedProjectionOperator p -
      unitizedProjectionOperator (unitizationScalarShadowProjection p)) :=
    unitizedModuleMatrixRepresentation_sub_isModuleCompact _ _
      (unitizationScalarShadowProjection_scalar p)
  have hTransport := relativeProjectionTransport_class (Γ := PUnit) W
    (unitizedProjectionOperator p) (unitizedProjectionOperator (unitizationScalarShadowProjection p))
    (unitizedProjectionOperator_isStarProjection p)
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection p))
    hc finiteStandardModule_isCountablyGenerated_nonunital
  have hcqr : IsModuleCompact (unitizedProjectionOperator q - unitizedProjectionOperator r) := by
    simpa only [W, q, r, unitizedProjectionOperator, unitaryProjectionConjugate,
      unitizedMatrixUnitaryEquiv_transport] using W.transport_difference_isModuleCompact hc
  have hcrs : IsModuleCompact (unitizedProjectionOperator r - unitizedProjectionOperator s) := by
    apply unitizedModuleMatrixRepresentation_sub_isModuleCompact
    intro i j
    exact congrArg (fun M : CStarMatrix ι ι ℂ => M i j)
      (unitizationScalarProjectionCorrection_reference_scalar U p)
  have hCocycle := relativeProjectionCocycle_class (Γ := PUnit)
    (unitizedProjectionOperator q) (unitizedProjectionOperator r) (unitizedProjectionOperator s)
    (unitizedProjectionOperator_isStarProjection q) (unitizedProjectionOperator_isStarProjection r)
    (unitizedProjectionOperator_isStarProjection s) hcqr hcrs
    finiteStandardModule_isCountablyGenerated_nonunital
  have hZero := unitizationScalarProjectionCorrection_class_zero U p
  change KasparovHomotopyClass.mk (BundledKasparovCycle.of
    (relativeProjectionCycle (Γ := PUnit) (unitizedProjectionOperator r)
      (unitizedProjectionOperator s) (unitizedProjectionOperator_isStarProjection r)
      (unitizedProjectionOperator_isStarProjection s) hcrs
      finiteStandardModule_isCountablyGenerated_nonunital)) = 0 at hZero
  rw [hZero, add_zero] at hCocycle
  have hPvalue : W.transport (unitizedProjectionOperator p) = unitizedProjectionOperator q := by
    change (unitizedMatrixUnitaryEquiv U).transport (unitizedModuleMatrixRepresentation p.val) =
      unitizedModuleMatrixRepresentation (U.val * p.val * star U.val)
    exact unitizedMatrixUnitaryEquiv_transport U p.val
  have hQvalue : W.transport (unitizedProjectionOperator (unitizationScalarShadowProjection p)) =
      unitizedProjectionOperator r := by
    change (unitizedMatrixUnitaryEquiv U).transport
        (unitizedModuleMatrixRepresentation (unitizationScalarShadowProjection p).val) =
      unitizedModuleMatrixRepresentation
        (U.val * (unitizationScalarShadowProjection p).val * star U.val)
    exact unitizedMatrixUnitaryEquiv_transport U (unitizationScalarShadowProjection p).val
  have hTransportClass
      (P' Q' : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
      (hP' : IsStarProjection P') (hQ' : IsStarProjection Q')
      (hc' : IsModuleCompact (P' - Q'))
      (hE' : IsCountablyGeneratedModule B (FiniteStandardModule B ι))
      (hPoperator : P' = unitizedProjectionOperator q)
      (hQoperator : Q' = unitizedProjectionOperator r) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P' Q' hP' hQ' hc' hE')) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) (unitizedProjectionOperator q)
          (unitizedProjectionOperator r) (unitizedProjectionOperator_isStarProjection q)
          (unitizedProjectionOperator_isStarProjection r) hcqr
          finiteStandardModule_isCountablyGenerated_nonunital)) := by
    subst P'
    subst Q'
    rfl
  have hFirst : unitizationScalarRelativeClass p =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) (unitizedProjectionOperator q)
          (unitizedProjectionOperator r) (unitizedProjectionOperator_isStarProjection q)
          (unitizedProjectionOperator_isStarProjection r) hcqr
          finiteStandardModule_isCountablyGenerated_nonunital)) :=
    hTransport.trans (hTransportClass _ _
      (W.transport_isStarProjection (unitizedProjectionOperator_isStarProjection p))
      (W.transport_isStarProjection
        (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection p)))
      (W.transport_difference_isModuleCompact hc)
      (W.isCountablyGeneratedModule finiteStandardModule_isCountablyGenerated_nonunital)
      hPvalue hQvalue)
  exact hFirst.trans hCocycle

end BC4lean.KKTheory
