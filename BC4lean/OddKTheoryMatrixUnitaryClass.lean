import BC4lean.OddKTheoryCompactUnitaryClass
import BC4lean.OddKTheoryScalarUnitaryNormalization

/-! # The actual stable finite-unitary inverse in the full odd group

Finite coordinate changes intertwine whole cycles, norm homotopies give
actual full interval witnesses, and identity blocks split off exactly
degenerate infinite sign cycles. The resulting inverse therefore descends
through the project's existing geometric stable-unitary relation.
-/

noncomputable section
universe uB
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local instance oddContinuationOddKTheoryMatrixUnitaryClassLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryMatrixUnitaryClassLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryMatrixUnitaryClassLocalInstance03 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryMatrixUnitaryClassLocalInstance04 : CompleteSpace (FiniteStandardModule B κ) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryMatrixUnitaryClassLocalInstance05 : CompleteSpace (FiniteStandardModule B (ι ⊕ κ)) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryMatrixUnitaryClassLocalInstance06 : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B ι)
    (FiniteStandardModule B κ)) := hilbertModuleSum_complete

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

def oddKTheoryMatrixUnitaryClass (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKK.{0, 0, uB, uB} α₁ β₁ :=
  OddKK.mk (BundledOddKasparovCycle.of (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu))

theorem oddKTheoryMatrixUnitaryClass_path {u v : MatrixUnitary (Unitization ℂ B) ι}
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (hv : unitizationScalarMatrix (v : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (p : Path u v)
    (hp : ∀ t, unitizationScalarMatrix (p t : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    oddKTheoryMatrixUnitaryClass u hu = oddKTheoryMatrixUnitaryClass v hv := by
  exact OddKK.mk_eq_of_full (FullOddKasparovHomotopy.ofOperatorHomotopy
    (oddKTheoryMatrixUnitaryOperatorHomotopy (Γ := PUnit) hu p hp))

def oddKTheoryMatrixOperatorUnitary (u : MatrixUnitary (Unitization ℂ B) ι) :
    unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) :=
  ⟨oddKTheoryUnitizedRowMatrixHom u, Unitary.map_mem oddKTheoryUnitizedRowMatrixHom u.property⟩

theorem oddKTheoryMatrixOperatorUnitary_compact (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    IsModuleCompact ((oddKTheoryMatrixOperatorUnitary u : _) - 1) := by
  have h := unitizedModuleMatrixRepresentation_sub_isModuleCompact
    (u : CStarMatrix ι ι (Unitization ℂ B)) 1 (fun i j => by
      have hh := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hu
      simpa only [unitizationScalarMatrix_apply, CStarMatrix.one_apply, Unitization.fst_one,
        Unitization.fst_zero] using hh)
  simpa only [oddKTheoryMatrixOperatorUnitary, oddKTheoryUnitizedRowMatrixHom,
    oddKTheoryUnitizedRowMatrix_one] using h

theorem oddKTheoryMatrixLoopPullback_eq_compactPullback
    (u : MatrixUnitary (Unitization ℂ B) ι) :
    oddKTheoryMatrixLoopPullback u = oddFredholmRowUnitaryPullback (oddKTheoryMatrixOperatorUnitary u) := by
  rw [oddKTheoryMatrixLoopPullback_finiteFormula]
  unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  exact oddKTheoryCircleCFC_map oddKTheoryUnitizedRowMatrixHom (map_continuous _) u
    (oddKTheoryMatrixOperatorUnitary u) rfl (oddKTheoryLoopTermCoefficient i)

def oddKTheoryMatrixCompactPullbackCycleIso (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    OddKasparovCycleIso (oddKTheoryMatrixUnitaryCycle (Γ := PUnit) u hu)
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
        finiteStandardModule_isCountablyGenerated_nonunital (oddKTheoryMatrixOperatorUnitary u)
        (oddKTheoryMatrixOperatorUnitary_compact u hu)) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine x := congrArg (fun T => T x) (oddKTheoryMatrixLoopPullback_eq_compactPullback u)

theorem oddKTheoryMatrixUnitaryClass_reindex (e : ι ≃ κ)
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (hv : unitizationScalarMatrix (unitaryReindex e u : CStarMatrix κ κ (Unitization ℂ B)) = 1) :
    oddKTheoryMatrixUnitaryClass u hu = oddKTheoryMatrixUnitaryClass (unitaryReindex e u) hv := by
  have he : oddKTheoryTransportOperatorUnitary (oddKTheoryFiniteReindexEquiv (B := B) e)
      (oddKTheoryMatrixOperatorUnitary u) = oddKTheoryMatrixOperatorUnitary (unitaryReindex e u) := by
    apply Subtype.ext
    ext x
    rw [HilbertModuleEquiv.transport_apply, oddKTheoryFiniteReindexEquiv_matrix,
      HilbertModuleEquiv.apply_symm_apply]
  have hc := oddKTheoryCompactUnitaryTransportIso finiteStandardModule_isCountablyGenerated_nonunital
    finiteStandardModule_isCountablyGenerated_nonunital (oddKTheoryFiniteReindexEquiv (B := B) e)
    (oddKTheoryMatrixOperatorUnitary u) (oddKTheoryMatrixOperatorUnitary_compact u hu)
  rw [he] at hc
  exact OddKK.mk_eq_of_iso ((oddKTheoryMatrixCompactPullbackCycleIso u hu).trans
    (hc.trans (oddKTheoryMatrixCompactPullbackCycleIso (unitaryReindex e u) hv).symm))

def oddKTheoryBlockCircleHom (u : MatrixUnitary (Unitization ℂ B) ι)
    (v : MatrixUnitary (Unitization ℂ B) κ) :
    C(Circle, ℂ) →⋆ₐ[ℂ] CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B) where
  toFun f := matrixBlockSum (oddKTheoryCircleCFC u f) (oddKTheoryCircleCFC v f)
  map_one' := by rw [map_one, map_one, matrixBlockSum_one]
  map_zero' := by rw [map_zero, map_zero, matrixBlockSum_zero]
  map_mul' f g := by rw [map_mul, map_mul, matrixBlockSum_mul]
  map_add' f g := by
    ext i j
    cases i <;> cases j <;> simp [matrixBlockSum, Matrix.fromBlocks, map_add]
  map_star' f := by rw [map_star, map_star, matrixBlockSum_star]
  commutes' c := by
    rw [(oddKTheoryCircleCFC u).commutes, (oddKTheoryCircleCFC v).commutes]
    ext i j
    cases i <;> cases j <;> simp [matrixBlockSum, Matrix.fromBlocks, Algebra.algebraMap_eq_smul_one,
      CStarMatrix.one_apply, CStarMatrix.smul_apply]

theorem oddKTheoryCircleCFC_blockSum (u : MatrixUnitary (Unitization ℂ B) ι)
    (v : MatrixUnitary (Unitization ℂ B) κ) (f : C(Circle, ℂ)) :
    oddKTheoryCircleCFC (unitaryBlockSum u v) f =
      matrixBlockSum (oddKTheoryCircleCFC u f) (oddKTheoryCircleCFC v f) := by
  have hh : oddKTheoryCircleCFC (unitaryBlockSum u v) = oddKTheoryBlockCircleHom u v := by
    apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (Metric.sphere (0 : ℂ) 1)
      _ _ (continuous_oddKTheoryCircleCFC _) (map_continuous _)
    rw [oddKTheoryCircleCFC_coordinate]
    change matrixBlockSum (u : CStarMatrix ι ι (Unitization ℂ B))
      (v : CStarMatrix κ κ (Unitization ℂ B)) = _
    rw [oddKTheoryBlockCircleHom, oddKTheoryCircleCFC_coordinate, oddKTheoryCircleCFC_coordinate]
  exact DFunLike.congr_fun hh f

theorem oddKTheoryMatrixUnitaryClass_blockSum
    (u : MatrixUnitary (Unitization ℂ B) ι) (v : MatrixUnitary (Unitization ℂ B) κ)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (hv : unitizationScalarMatrix (v : CStarMatrix κ κ (Unitization ℂ B)) = 1)
    (huv : unitizationScalarMatrix (unitaryBlockSum u v :
      CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B)) = 1) :
    oddKTheoryMatrixUnitaryClass (unitaryBlockSum u v) huv =
      oddKTheoryMatrixUnitaryClass u hu + oddKTheoryMatrixUnitaryClass v hv := by
  have he : oddKTheoryTransportOperatorUnitary (oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := κ))
      (oddKTheoryMatrixOperatorUnitary (unitaryBlockSum u v)) =
      oddKTheorySumOperatorUnitary (oddKTheoryMatrixOperatorUnitary u) (oddKTheoryMatrixOperatorUnitary v) := by
    apply Subtype.ext
    ext x
    rw [HilbertModuleEquiv.transport_apply, oddKTheoryFiniteSumEquiv_matrix,
      HilbertModuleEquiv.apply_symm_apply]
  have hc := oddKTheoryCompactUnitaryTransportIso finiteStandardModule_isCountablyGenerated_nonunital
    (finiteStandardModule_isCountablyGenerated_nonunital.sum finiteStandardModule_isCountablyGenerated_nonunital)
    (oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := κ))
    (oddKTheoryMatrixOperatorUnitary (unitaryBlockSum u v))
    (oddKTheoryMatrixOperatorUnitary_compact (unitaryBlockSum u v) huv)
  rw [he] at hc
  have hs := oddKTheoryCompactUnitarySumIso finiteStandardModule_isCountablyGenerated_nonunital
    finiteStandardModule_isCountablyGenerated_nonunital (oddKTheoryMatrixOperatorUnitary u)
    (oddKTheoryMatrixOperatorUnitary v) (oddKTheoryMatrixOperatorUnitary_compact u hu)
    (oddKTheoryMatrixOperatorUnitary_compact v hv)
  exact OddKK.mk_eq_of_iso ((oddKTheoryMatrixCompactPullbackCycleIso (unitaryBlockSum u v) huv).trans
    (hc.trans (hs.trans ((oddKTheoryMatrixCompactPullbackCycleIso u hu).directSum
      (oddKTheoryMatrixCompactPullbackCycleIso v hv)).symm)))

@[simp] theorem oddKTheoryMatrixUnitaryClass_one :
    oddKTheoryMatrixUnitaryClass (1 : MatrixUnitary (Unitization ℂ B) ι)
      (by simp [unitizationScalarMatrix]) = 0 :=
  OddKK.mk_eq_zero_of_degenerate _ oddKTheoryMatrixUnitaryCycle_one_isDegenerate

def oddKTheoryNormalizedFiniteUnitaryClass (a : FiniteUnitary (Unitization ℂ B)) :
    OddKK.{0, 0, uB, uB} α₁ β₁ :=
  oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary a.val)
    (oddKTheoryScalarNormalizedUnitary_scalar a.val)

theorem oddKTheoryNormalizedFiniteUnitaryClass_move
    {a b : FiniteUnitary (Unitization ℂ B)} (h : FiniteUnitary.Move a b) :
    oddKTheoryNormalizedFiniteUnitaryClass a = oddKTheoryNormalizedFiniteUnitaryClass b := by
  cases h with
  | homotopy a b e h =>
    obtain ⟨p⟩ := h
    let q : Path (oddKTheoryScalarNormalizedUnitary (unitaryReindex e a.val))
        (oddKTheoryScalarNormalizedUnitary b.val) :=
      p.map oddKTheoryScalarNormalizedUnitary continuous_oddKTheoryScalarNormalizedUnitary
    have hq := oddKTheoryMatrixUnitaryClass_path
      (oddKTheoryScalarNormalizedUnitary_scalar (unitaryReindex e a.val))
      (oddKTheoryScalarNormalizedUnitary_scalar b.val) q
      (fun t => oddKTheoryScalarNormalizedUnitary_scalar (p t))
    rw [oddKTheoryScalarNormalizedUnitary_reindex] at hq
    exact (oddKTheoryMatrixUnitaryClass_reindex e (oddKTheoryScalarNormalizedUnitary a.val)
      (oddKTheoryScalarNormalizedUnitary_scalar a.val)
      (by simpa only [← oddKTheoryScalarNormalizedUnitary_reindex] using
        oddKTheoryScalarNormalizedUnitary_scalar (unitaryReindex e a.val))).trans hq
  | stabilize a κ =>
    change oddKTheoryMatrixUnitaryClass _ _ = oddKTheoryMatrixUnitaryClass _ _
    rw [oddKTheoryScalarNormalizedUnitary_blockSum, oddKTheoryScalarNormalizedUnitary_one,
      oddKTheoryMatrixUnitaryClass_blockSum, oddKTheoryMatrixUnitaryClass_one, add_zero]

theorem oddKTheoryNormalizedFiniteUnitaryClass_equivalent
    {a b : FiniteUnitary (Unitization ℂ B)} (h : FiniteUnitary.Equivalent a b) :
    oddKTheoryNormalizedFiniteUnitaryClass a = oddKTheoryNormalizedFiniteUnitaryClass b := by
  induction h with
  | rel a b h => exact oddKTheoryNormalizedFiniteUnitaryClass_move h
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h k ih ik => exact ih.trans ik

/-- A genuine additive inverse construction on the existing stable unitary
group. Its restriction to the actual scalar kernel is the nonunital inverse. -/
def oddKTheoryStableUnitaryInverse : K1 (Unitization ℂ B) →+ OddKK.{0, 0, uB, uB} α₁ β₁ where
  toFun := Quotient.lift oddKTheoryNormalizedFiniteUnitaryClass
    (fun _ _ h => oddKTheoryNormalizedFiniteUnitaryClass_equivalent h)
  map_zero' := oddKTheoryMatrixUnitaryClass_one
  map_add' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change oddKTheoryMatrixUnitaryClass _ _ = oddKTheoryMatrixUnitaryClass _ _ +
      oddKTheoryMatrixUnitaryClass _ _
    rw [oddKTheoryScalarNormalizedUnitary_blockSum, oddKTheoryMatrixUnitaryClass_blockSum]

def oddOperatorK1KKInverse : OperatorK1 B →+ OddKK.{0, 0, uB, uB} α₁ β₁ :=
  oddKTheoryStableUnitaryInverse.comp (AddSubgroup.subtype _)

@[simp] theorem oddOperatorK1KKInverse_scalarIdentityUnitary
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    oddOperatorK1KKInverse (oddFredholmScalarIdentityUnitaryIndex u hu) =
      oddKTheoryMatrixUnitaryClass u hu := by
  change oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary u) _ = _
  rw [oddKTheoryScalarNormalizedUnitary_of_scalarIdentity u hu]

end BC4lean.KKTheory
