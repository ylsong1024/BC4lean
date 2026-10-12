import BC4lean.UnitizationScalarRelativeClass
import BC4lean.FiniteProjectionBlockSum

/-! # Actual addition of scalar-relative finite unitization projections

Splitting the finite coordinate index preserves the actual B-valued inner
product. It intertwines the genuine unitization block action and the actual
scalar shadows, so the full relative class adds under matrix block sum.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open scoped Matrix

variable {B : Type u} {ι κ : Type} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

local instance scalarBlockUnitizationOrder : PartialOrder (Unitization ℂ B) :=
  CStarAlgebra.spectralOrder _
local instance scalarBlockUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ B) :=
  CStarAlgebra.spectralOrderedRing _

/-- Splitting actual B-coordinates intertwines the full unitization matrix action. -/
theorem finiteStandardSumEquiv_unitization_block_action
    (M : CStarMatrix ι ι (Unitization ℂ B)) (N : CStarMatrix κ κ (Unitization ℂ B))
    (x : FiniteStandardModule B (ι ⊕ κ)) :
    finiteStandardSumEquiv (unitizedModuleMatrixRepresentation (matrixBlockSum M N) x) =
      sumMap (unitizedModuleMatrixRepresentation M) (unitizedModuleMatrixRepresentation N)
        (finiteStandardSumEquiv x) := by
  apply Prod.ext
  · ext i
    simp only [finiteStandardSumEquiv_apply, finiteStandardSplit_fst,
      unitizedModuleMatrixRepresentation_apply, sumMap_apply, sumMk_fst,
      Fintype.sum_sum_type, matrixBlockSum, CStarMatrix.ofMatrix_apply,
      CStarMatrix.ofMatrix_symm_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      map_zero, AdjointableMap.coe_zero_apply, Finset.sum_const_zero, add_zero]
  · ext j
    simp only [finiteStandardSumEquiv_apply, finiteStandardSplit_snd,
      unitizedModuleMatrixRepresentation_apply, sumMap_apply, sumMk_snd,
      Fintype.sum_sum_type, matrixBlockSum, CStarMatrix.ofMatrix_apply,
      CStarMatrix.ofMatrix_symm_apply,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      map_zero, AdjointableMap.coe_zero_apply, Finset.sum_const_zero, zero_add]

/-- The actual finite coordinate unitary transports the full block representation. -/
theorem finiteStandardSumEquiv_unitization_block_transport
    (M : CStarMatrix ι ι (Unitization ℂ B)) (N : CStarMatrix κ κ (Unitization ℂ B)) :
    (finiteStandardSumEquiv (B := B) (ι := ι) (κ := κ)).transport
      (unitizedModuleMatrixRepresentation (matrixBlockSum M N)) =
      sumMap (unitizedModuleMatrixRepresentation M) (unitizedModuleMatrixRepresentation N) := by
  ext x
  rw [HilbertModuleEquiv.transport_apply,
    finiteStandardSumEquiv_unitization_block_action, HilbertModuleEquiv.apply_symm_apply]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The actual scalar shadow preserves finite projection block sums. -/
theorem unitizationScalarShadowProjection_blockSum [PartialOrder B] [StarOrderedRing B]
    (p : MatrixProjection (Unitization ℂ B) ι) (q : MatrixProjection (Unitization ℂ B) κ) :
    unitizationScalarShadowProjection (projectionBlockSum p q) =
      projectionBlockSum (unitizationScalarShadowProjection p) (unitizationScalarShadowProjection q) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  intro i j
  cases i <;> cases j <;> rfl

variable [TopologicalSpace.SeparableSpace B]

/-- Actual block addition of scalar-relative full classes. -/
theorem unitizationScalarRelativeClass_blockSum
    (p : MatrixProjection (Unitization ℂ B) ι) (q : MatrixProjection (Unitization ℂ B) κ) :
    unitizationScalarRelativeClass (projectionBlockSum p q) =
      unitizationScalarRelativeClass p + unitizationScalarRelativeClass q := by
  let U := finiteStandardSumEquiv (B := B) (ι := ι) (κ := κ)
  have hc : IsModuleCompact (unitizedProjectionOperator (projectionBlockSum p q) -
      unitizedProjectionOperator (unitizationScalarShadowProjection (projectionBlockSum p q))) :=
    unitizedModuleMatrixRepresentation_sub_isModuleCompact _ _
      (unitizationScalarShadowProjection_scalar (projectionBlockSum p q))
  have hTransport := relativeProjectionTransport_class (Γ := PUnit) U
    (unitizedProjectionOperator (projectionBlockSum p q))
    (unitizedProjectionOperator (unitizationScalarShadowProjection (projectionBlockSum p q)))
    (unitizedProjectionOperator_isStarProjection (projectionBlockSum p q))
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection (projectionBlockSum p q)))
    hc finiteStandardModule_isCountablyGenerated_nonunital
  have hSum := relativeProjectionSum_class (Γ := PUnit)
    (unitizedProjectionOperator p) (unitizedProjectionOperator (unitizationScalarShadowProjection p))
    (unitizedProjectionOperator q) (unitizedProjectionOperator (unitizationScalarShadowProjection q))
    (unitizedProjectionOperator_isStarProjection p)
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection p))
    (unitizedProjectionOperator_isStarProjection q)
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection q))
    (unitizedModuleMatrixRepresentation_sub_isModuleCompact _ _ (unitizationScalarShadowProjection_scalar p))
    (unitizedModuleMatrixRepresentation_sub_isModuleCompact _ _ (unitizationScalarShadowProjection_scalar q))
    finiteStandardModule_isCountablyGenerated_nonunital finiteStandardModule_isCountablyGenerated_nonunital
  let P := sumMap (unitizedProjectionOperator p) (unitizedProjectionOperator q)
  let Q := sumMap (unitizedProjectionOperator (unitizationScalarShadowProjection p))
    (unitizedProjectionOperator (unitizationScalarShadowProjection q))
  have hP : IsStarProjection P := sumMap_isStarProjection
    (unitizedProjectionOperator_isStarProjection p) (unitizedProjectionOperator_isStarProjection q)
  have hQ : IsStarProjection Q := sumMap_isStarProjection
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection p))
    (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection q))
  have hcP : IsModuleCompact (unitizedProjectionOperator p -
      unitizedProjectionOperator (unitizationScalarShadowProjection p)) :=
    unitizedModuleMatrixRepresentation_sub_isModuleCompact _ _ (unitizationScalarShadowProjection_scalar p)
  have hcQ : IsModuleCompact (unitizedProjectionOperator q -
      unitizedProjectionOperator (unitizationScalarShadowProjection q)) :=
    unitizedModuleMatrixRepresentation_sub_isModuleCompact _ _ (unitizationScalarShadowProjection_scalar q)
  have hcPQ : IsModuleCompact (P - Q) := by
    change IsModuleCompact
      (sumMap (unitizedProjectionOperator p) (unitizedProjectionOperator q) -
        sumMap (unitizedProjectionOperator (unitizationScalarShadowProjection p))
          (unitizedProjectionOperator (unitizationScalarShadowProjection q)))
    rw [← sumMap_sub]
    exact hcP.sumMap hcQ
  have hE : IsCountablyGeneratedModule B
      (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ)) :=
    (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι)).sum
      (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := κ))
  have hPvalue : U.transport (unitizedProjectionOperator (projectionBlockSum p q)) = P := by
    change (finiteStandardSumEquiv (B := B) (ι := ι) (κ := κ)).transport
        (unitizedModuleMatrixRepresentation (matrixBlockSum p.val q.val)) =
      sumMap (unitizedModuleMatrixRepresentation p.val) (unitizedModuleMatrixRepresentation q.val)
    exact finiteStandardSumEquiv_unitization_block_transport p.val q.val
  have hQmatrix : (unitizationScalarShadowProjection (projectionBlockSum p q)).val =
      matrixBlockSum (unitizationScalarShadowProjection p).val (unitizationScalarShadowProjection q).val :=
    congrArg (fun r : MatrixProjection (Unitization ℂ B) (ι ⊕ κ) => r.val)
      (unitizationScalarShadowProjection_blockSum p q)
  have hQvalue : U.transport
      (unitizedProjectionOperator (unitizationScalarShadowProjection (projectionBlockSum p q))) = Q := by
    change (finiteStandardSumEquiv (B := B) (ι := ι) (κ := κ)).transport
        (unitizedModuleMatrixRepresentation (unitizationScalarShadowProjection (projectionBlockSum p q)).val) =
      sumMap (unitizedModuleMatrixRepresentation (unitizationScalarShadowProjection p).val)
        (unitizedModuleMatrixRepresentation (unitizationScalarShadowProjection q).val)
    rw [hQmatrix]
    exact finiteStandardSumEquiv_unitization_block_transport
      (unitizationScalarShadowProjection p).val (unitizationScalarShadowProjection q).val
  have hTransportClass
      (P' Q' : AdjointableMap B
        (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ))
        (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ)))
      (hP' : IsStarProjection P') (hQ' : IsStarProjection Q')
      (hc' : IsModuleCompact (P' - Q'))
      (hE' : IsCountablyGeneratedModule B
        (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ)))
      (hPoperator : P' = P) (hQoperator : Q' = Q) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P' Q' hP' hQ' hc' hE')) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := PUnit) P Q hP hQ hcPQ hE)) := by
    subst P'
    subst Q'
    rfl
  exact hTransport.trans ((hTransportClass _ _
    (U.transport_isStarProjection (unitizedProjectionOperator_isStarProjection (projectionBlockSum p q)))
    (U.transport_isStarProjection
      (unitizedProjectionOperator_isStarProjection (unitizationScalarShadowProjection (projectionBlockSum p q))))
    (U.transport_difference_isModuleCompact hc)
    (U.isCountablyGeneratedModule finiteStandardModule_isCountablyGenerated_nonunital)
    hPvalue hQvalue).trans hSum)

/-- The zero projection and its scalar shadow coincide, so its actual relative class vanishes. -/
@[simp] theorem unitizationScalarRelativeClass_zero :
    unitizationScalarRelativeClass (Projection.zero : MatrixProjection (Unitization ℂ B) ι) = 0 := by
  have hs : unitizationScalarShadowProjection (Projection.zero : MatrixProjection (Unitization ℂ B) ι) =
      Projection.zero := by
    apply Subtype.ext
    exact map_zero unitizationScalarLiftHom
  have hZeroClass (q : MatrixProjection (Unitization ℂ B) ι)
      (hScalar : ∀ i j, ((Projection.zero : MatrixProjection (Unitization ℂ B) ι).val i j).fst =
        (q.val i j).fst)
      (hq : q = Projection.zero) :
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (unitizedRelativeProjectionCycle (Γ := PUnit) Projection.zero q hScalar)) = 0 := by
    subst q
    exact KasparovHomotopyClass.mk_eq_zero_of_degenerate _
      (unitizedRelativeProjectionCycle_diagonal_isDegenerate _)
  exact hZeroClass
    (unitizationScalarShadowProjection (Projection.zero : MatrixProjection (Unitization ℂ B) ι))
    (unitizationScalarShadowProjection_scalar (Projection.zero : MatrixProjection (Unitization ℂ B) ι)) hs

end BC4lean.KKTheory
