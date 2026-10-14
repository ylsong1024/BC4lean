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

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryMatrixOperatorUnitary_compact (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    IsModuleCompact ((oddKTheoryMatrixOperatorUnitary u :
      AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) - 1) := by
  change IsModuleCompact (unitizedModuleMatrixRepresentation (u : CStarMatrix ι ι (Unitization ℂ B)) - 1)
  have h := unitizedModuleMatrixRepresentation_sub_isModuleCompact
    (u : CStarMatrix ι ι (Unitization ℂ B)) 1 (fun i j => by
      have hh := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hu
      by_cases hij : i = j
      · simpa only [unitizationScalarMatrix_apply, CStarMatrix.one_apply, if_pos hij,
          Unitization.fst_one] using hh
      · simpa only [unitizationScalarMatrix_apply, CStarMatrix.one_apply, if_neg hij,
          Unitization.fst_zero] using hh)
  simpa only [oddKTheoryUnitizedRowMatrix_one] using h

set_option maxHeartbeats 4000000 in
omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryMatrixLoopPullback_eq_compactPullback
    (u : MatrixUnitary (Unitization ℂ B) ι) :
    oddKTheoryMatrixLoopPullback (B := B) (ι := ι) u =
      oddFredholmRowUnitaryPullback (B := B) (E := FiniteStandardModule B ι)
        (oddKTheoryMatrixOperatorUnitary (B := B) (ι := ι) u) := by
  rw [oddKTheoryMatrixLoopPullback_finiteFormula]
  unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  exact oddKTheoryCircleCFC_map
    (A := CStarMatrix ι ι (Unitization ℂ B))
    (C := AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι))
    (oddKTheoryUnitizedRowMatrixHom (B := B) (ι := ι))
    (map_continuous (oddKTheoryUnitizedRowMatrixHom (B := B) (ι := ι))) u
    (oddKTheoryMatrixOperatorUnitary (B := B) (ι := ι) u) rfl (oddKTheoryLoopTermCoefficient i)

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
    apply AdjointableMap.ext
    intro x
    change (oddKTheoryFiniteReindexEquiv (B := B) e).transport
        (unitizedModuleMatrixRepresentation (u : CStarMatrix ι ι (Unitization ℂ B))) x =
      unitizedModuleMatrixRepresentation (unitaryReindex e u : CStarMatrix κ κ (Unitization ℂ B)) x
    rw [HilbertModuleEquiv.transport_apply, oddKTheoryFiniteReindexEquiv_matrix,
      HilbertModuleEquiv.apply_symm_apply]
    rfl
  have hc := oddKTheoryCompactUnitaryTransportIso finiteStandardModule_isCountablyGenerated_nonunital
    finiteStandardModule_isCountablyGenerated_nonunital (oddKTheoryFiniteReindexEquiv (B := B) e)
    (oddKTheoryMatrixOperatorUnitary u) (oddKTheoryMatrixOperatorUnitary_compact u hu)
  have hc' : OddKasparovCycleIso
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
        (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι))
        (oddKTheoryMatrixOperatorUnitary u) (oddKTheoryMatrixOperatorUnitary_compact u hu))
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
        (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := κ))
        (oddKTheoryMatrixOperatorUnitary (unitaryReindex e u))
        (oddKTheoryMatrixOperatorUnitary_compact (unitaryReindex e u) hv)) := by
    simpa only [he] using hc
  exact OddKK.mk_eq_of_iso ((oddKTheoryMatrixCompactPullbackCycleIso u hu).trans
    (hc'.trans (oddKTheoryMatrixCompactPullbackCycleIso (unitaryReindex e u) hv).symm))

def oddKTheoryBlockCircleHom (u : MatrixUnitary (Unitization ℂ B) ι)
    (v : MatrixUnitary (Unitization ℂ B) κ) :
    C(Circle, ℂ) →⋆ₐ[ℂ] CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B) where
  toFun f := matrixBlockSum (oddKTheoryCircleCFC u f) (oddKTheoryCircleCFC v f)
  map_one' := by rw [map_one, map_one, matrixBlockSum_one]
  map_zero' := by rw [map_zero, map_zero, matrixBlockSum_zero]
  map_mul' f g := by rw [map_mul, map_mul, matrixBlockSum_mul]
  map_add' f g := by
    have hufg := map_add (oddKTheoryCircleCFC (A := CStarMatrix ι ι (Unitization ℂ B)) u) f g
    have hvfg := map_add (oddKTheoryCircleCFC (A := CStarMatrix κ κ (Unitization ℂ B)) v) f g
    rw [hufg, hvfg]
    apply CStarMatrix.ext
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact (zero_add (0 : Unitization ℂ B)).symm
    | inr i =>
      cases j with
      | inl j => exact (zero_add (0 : Unitization ℂ B)).symm
      | inr j => rfl
  map_star' f := by rw [map_star, map_star, matrixBlockSum_star]
  commutes' c := by
    have hu : oddKTheoryCircleCFC (A := CStarMatrix ι ι (Unitization ℂ B)) u
        (algebraMap ℂ C(Circle, ℂ) c) = algebraMap ℂ (CStarMatrix ι ι (Unitization ℂ B)) c :=
      (oddKTheoryCircleCFC (A := CStarMatrix ι ι (Unitization ℂ B)) u).commutes c
    have hv : oddKTheoryCircleCFC (A := CStarMatrix κ κ (Unitization ℂ B)) v
        (algebraMap ℂ C(Circle, ℂ) c) = algebraMap ℂ (CStarMatrix κ κ (Unitization ℂ B)) c :=
      (oddKTheoryCircleCFC (A := CStarMatrix κ κ (Unitization ℂ B)) v).commutes c
    have hscalar : matrixBlockSum (algebraMap ℂ (CStarMatrix ι ι (Unitization ℂ B)) c)
        (algebraMap ℂ (CStarMatrix κ κ (Unitization ℂ B)) c) =
      algebraMap ℂ (CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B)) c := by
      simp only [Algebra.algebraMap_eq_smul_one]
      change Matrix.fromBlocks (c • (1 : Matrix ι ι (Unitization ℂ B)))
          (0 : Matrix ι κ (Unitization ℂ B)) (0 : Matrix κ ι (Unitization ℂ B))
          (c • (1 : Matrix κ κ (Unitization ℂ B))) =
        c • (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B))
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
      simp only [smul_zero]
    exact (congrArg₂ (fun (M : CStarMatrix ι ι (Unitization ℂ B))
      (N : CStarMatrix κ κ (Unitization ℂ B)) => matrixBlockSum M N) hu hv).trans hscalar

set_option maxHeartbeats 4000000 in
omit [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryCircleCFC_blockSum (u : MatrixUnitary (Unitization ℂ B) ι)
    (v : MatrixUnitary (Unitization ℂ B) κ) (f : C(Circle, ℂ)) :
    oddKTheoryCircleCFC (A := CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B))
        (unitaryBlockSum u v) f =
      matrixBlockSum (oddKTheoryCircleCFC (A := CStarMatrix ι ι (Unitization ℂ B)) u f)
        (oddKTheoryCircleCFC (A := CStarMatrix κ κ (Unitization ℂ B)) v f) := by
  have hh : oddKTheoryCircleCFC (A := CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B))
      (unitaryBlockSum u v) = oddKTheoryBlockCircleHom (B := B) (ι := ι) (κ := κ) u v := by
    apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (R := ℂ)
      (A := CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B)) (Metric.sphere (0 : ℂ) 1)
      (oddKTheoryCircleCFC (A := CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B)) (unitaryBlockSum u v))
      (oddKTheoryBlockCircleHom (B := B) (ι := ι) (κ := κ) u v)
      (continuous_oddKTheoryCircleCFC (A := CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B)) (unitaryBlockSum u v))
      (map_continuous (oddKTheoryBlockCircleHom (B := B) (ι := ι) (κ := κ) u v))
    change oddKTheoryCircleCFC (A := CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B))
        (unitaryBlockSum u v) ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)) =
      matrixBlockSum (oddKTheoryCircleCFC (A := CStarMatrix ι ι (Unitization ℂ B)) u
        ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)))
        (oddKTheoryCircleCFC (A := CStarMatrix κ κ (Unitization ℂ B)) v
          ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)))
    have hsum := oddKTheoryCircleCFC_coordinate
      (A := CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B)) (unitaryBlockSum u v)
    have hu := oddKTheoryCircleCFC_coordinate (A := CStarMatrix ι ι (Unitization ℂ B)) u
    have hv := oddKTheoryCircleCFC_coordinate (A := CStarMatrix κ κ (Unitization ℂ B)) v
    exact hsum.trans (congrArg₂ (fun (M : CStarMatrix ι ι (Unitization ℂ B))
      (N : CStarMatrix κ κ (Unitization ℂ B)) => matrixBlockSum M N) hu.symm hv.symm)
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
    apply AdjointableMap.ext
    intro x
    change (oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := κ)).transport
        (unitizedModuleMatrixRepresentation (unitaryBlockSum u v :
          CStarMatrix (ι ⊕ κ) (ι ⊕ κ) (Unitization ℂ B))) x =
      sumMap (unitizedModuleMatrixRepresentation (u : CStarMatrix ι ι (Unitization ℂ B)))
        (unitizedModuleMatrixRepresentation (v : CStarMatrix κ κ (Unitization ℂ B))) x
    rw [HilbertModuleEquiv.transport_apply, unitaryBlockSum_coe, oddKTheoryFiniteSumEquiv_matrix,
      HilbertModuleEquiv.apply_symm_apply]
  have hc := oddKTheoryCompactUnitaryTransportIso
    (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι ⊕ κ))
    ((finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι)).sum
      (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := κ)))
    (oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := κ))
    (oddKTheoryMatrixOperatorUnitary (unitaryBlockSum u v))
    (oddKTheoryMatrixOperatorUnitary_compact (unitaryBlockSum u v) huv)
  have hc' : OddKasparovCycleIso
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
        (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι ⊕ κ))
        (oddKTheoryMatrixOperatorUnitary (unitaryBlockSum u v))
        (oddKTheoryMatrixOperatorUnitary_compact (unitaryBlockSum u v) huv))
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit)
        ((finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι)).sum
          (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := κ)))
        (oddKTheorySumOperatorUnitary (oddKTheoryMatrixOperatorUnitary u) (oddKTheoryMatrixOperatorUnitary v))
        (oddKTheorySumOperatorUnitary_compact (oddKTheoryMatrixOperatorUnitary u)
          (oddKTheoryMatrixOperatorUnitary v) (oddKTheoryMatrixOperatorUnitary_compact u hu)
          (oddKTheoryMatrixOperatorUnitary_compact v hv))) := by
    simpa only [he] using hc
  have hs := oddKTheoryCompactUnitarySumIso
    (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := ι))
    (finiteStandardModule_isCountablyGenerated_nonunital (B := B) (ι := κ)) (oddKTheoryMatrixOperatorUnitary u)
    (oddKTheoryMatrixOperatorUnitary v) (oddKTheoryMatrixOperatorUnitary_compact u hu)
    (oddKTheoryMatrixOperatorUnitary_compact v hv)
  exact OddKK.mk_eq_of_iso ((oddKTheoryMatrixCompactPullbackCycleIso (unitaryBlockSum u v) huv).trans
    (hc'.trans (hs.trans ((oddKTheoryMatrixCompactPullbackCycleIso u hu).directSum
      (oddKTheoryMatrixCompactPullbackCycleIso v hv)).symm)))

@[simp] theorem oddKTheoryMatrixUnitaryClass_one :
    oddKTheoryMatrixUnitaryClass (1 : MatrixUnitary (Unitization ℂ B) ι)
      (by change matrixMap (scalarQuotient B)
            (1 : CStarMatrix ι ι (Unitization ℂ B)) = 1
          exact map_one (matrixMap (scalarQuotient B))) = 0 :=
  OddKK.mk_eq_zero_of_degenerate _ oddKTheoryMatrixUnitaryCycle_one_isDegenerate

def oddKTheoryNormalizedFiniteUnitaryClass (a : FiniteUnitary (Unitization ℂ B)) :
    OddKK.{0, 0, uB, uB} α₁ β₁ :=
  oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary a.val)
    (oddKTheoryScalarNormalizedUnitary_scalar a.val)

theorem oddKTheoryNormalizedFiniteUnitaryClass_move
    {a b : FiniteUnitary (Unitization ℂ B)} (h : FiniteUnitary.Move a b) :
    oddKTheoryNormalizedFiniteUnitaryClass a = oddKTheoryNormalizedFiniteUnitaryClass b := by
  cases h with
  | homotopy b e h =>
    obtain ⟨p⟩ := h
    let q : Path (oddKTheoryScalarNormalizedUnitary (unitaryReindex e a.val))
        (oddKTheoryScalarNormalizedUnitary b.val) :=
      p.map (f := oddKTheoryScalarNormalizedUnitary) continuous_oddKTheoryScalarNormalizedUnitary
    have hq := oddKTheoryMatrixUnitaryClass_path
      (oddKTheoryScalarNormalizedUnitary_scalar (unitaryReindex e a.val))
      (oddKTheoryScalarNormalizedUnitary_scalar b.val) q
      (fun t => oddKTheoryScalarNormalizedUnitary_scalar (p t))
    have he : oddKTheoryScalarNormalizedUnitary (unitaryReindex e a.val) =
        unitaryReindex e (oddKTheoryScalarNormalizedUnitary a.val) :=
      oddKTheoryScalarNormalizedUnitary_reindex e a.val
    have hv : unitizationScalarMatrix (unitaryReindex e (oddKTheoryScalarNormalizedUnitary a.val) :
        CStarMatrix b.Index b.Index (Unitization ℂ B)) = 1 := by
      simpa only [he] using oddKTheoryScalarNormalizedUnitary_scalar (unitaryReindex e a.val)
    have hp : oddKTheoryMatrixUnitaryClass (unitaryReindex e (oddKTheoryScalarNormalizedUnitary a.val)) hv =
        oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary b.val)
          (oddKTheoryScalarNormalizedUnitary_scalar b.val) := by
      simpa only [he] using hq
    exact (oddKTheoryMatrixUnitaryClass_reindex e (oddKTheoryScalarNormalizedUnitary a.val)
      (oddKTheoryScalarNormalizedUnitary_scalar a.val) hv).trans hp
  | stabilize κ =>
    have huv : unitizationScalarMatrix
        (unitaryBlockSum (oddKTheoryScalarNormalizedUnitary a.val)
          (1 : MatrixUnitary (Unitization ℂ B) κ) :
            CStarMatrix (a.Index ⊕ κ) (a.Index ⊕ κ) (Unitization ℂ B)) = 1 := by
      simpa only [oddKTheoryScalarNormalizedUnitary_blockSum, oddKTheoryScalarNormalizedUnitary_one]
        using oddKTheoryScalarNormalizedUnitary_scalar (unitaryBlockSum a.val (1 : MatrixUnitary (Unitization ℂ B) κ))
    have hs := oddKTheoryMatrixUnitaryClass_blockSum (oddKTheoryScalarNormalizedUnitary a.val)
      (1 : MatrixUnitary (Unitization ℂ B) κ) (oddKTheoryScalarNormalizedUnitary_scalar a.val)
      (by change matrixMap (scalarQuotient B) (1 : CStarMatrix κ κ (Unitization ℂ B)) = 1
          exact map_one (matrixMap (scalarQuotient B))) huv
    change oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary a.val)
        (oddKTheoryScalarNormalizedUnitary_scalar a.val) =
      oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary (unitaryBlockSum a.val 1))
        (oddKTheoryScalarNormalizedUnitary_scalar (unitaryBlockSum a.val 1))
    simpa only [oddKTheoryScalarNormalizedUnitary_blockSum, oddKTheoryScalarNormalizedUnitary_one,
      oddKTheoryMatrixUnitaryClass_one, add_zero] using hs.symm

theorem oddKTheoryNormalizedFiniteUnitaryClass_equivalent
    {a b : FiniteUnitary (Unitization ℂ B)} (h : FiniteUnitary.Equivalent a b) :
    oddKTheoryNormalizedFiniteUnitaryClass a = oddKTheoryNormalizedFiniteUnitaryClass b := by
  induction h with
  | rel a b h => exact oddKTheoryNormalizedFiniteUnitaryClass_move h
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h k ih ik => exact ih.trans ik

set_option maxHeartbeats 4000000 in
/-- A genuine additive inverse construction on the existing stable unitary
group. Its restriction to the actual scalar kernel is the nonunital inverse. -/
def oddKTheoryStableUnitaryInverse : K1 (Unitization ℂ B) →+ OddKK.{0, 0, uB, uB} α₁ β₁ where
  toFun := Quotient.lift oddKTheoryNormalizedFiniteUnitaryClass
    (fun _ _ h => oddKTheoryNormalizedFiniteUnitaryClass_equivalent h)
  map_zero' := by
    change oddKTheoryMatrixUnitaryClass
      (oddKTheoryScalarNormalizedUnitary (1 : MatrixUnitary (Unitization ℂ B) Empty))
      (oddKTheoryScalarNormalizedUnitary_scalar (1 : MatrixUnitary (Unitization ℂ B) Empty)) = 0
    simpa only [oddKTheoryScalarNormalizedUnitary_one] using
      (oddKTheoryMatrixUnitaryClass_one (B := B) (ι := Empty))
  map_add' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary (unitaryBlockSum a.val b.val))
        (oddKTheoryScalarNormalizedUnitary_scalar (unitaryBlockSum a.val b.val)) =
      oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary a.val)
        (oddKTheoryScalarNormalizedUnitary_scalar a.val) +
      oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary b.val)
        (oddKTheoryScalarNormalizedUnitary_scalar b.val)
    have huv : unitizationScalarMatrix
        (unitaryBlockSum (oddKTheoryScalarNormalizedUnitary a.val)
          (oddKTheoryScalarNormalizedUnitary b.val) :
            CStarMatrix (a.Index ⊕ b.Index) (a.Index ⊕ b.Index) (Unitization ℂ B)) = 1 := by
      simpa only [oddKTheoryScalarNormalizedUnitary_blockSum]
        using oddKTheoryScalarNormalizedUnitary_scalar (unitaryBlockSum a.val b.val)
    simpa only [oddKTheoryScalarNormalizedUnitary_blockSum] using
      oddKTheoryMatrixUnitaryClass_blockSum (oddKTheoryScalarNormalizedUnitary a.val)
        (oddKTheoryScalarNormalizedUnitary b.val) (oddKTheoryScalarNormalizedUnitary_scalar a.val)
        (oddKTheoryScalarNormalizedUnitary_scalar b.val) huv

def oddOperatorK1KKInverse : OperatorK1 B →+ OddKK.{0, 0, uB, uB} α₁ β₁ :=
  oddKTheoryStableUnitaryInverse.comp (AddSubgroup.subtype _)

@[simp] theorem oddOperatorK1KKInverse_scalarIdentityUnitary
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    oddOperatorK1KKInverse (oddFredholmScalarIdentityUnitaryIndex u hu) =
      oddKTheoryMatrixUnitaryClass u hu := by
  change oddKTheoryMatrixUnitaryClass (oddKTheoryScalarNormalizedUnitary u)
    (oddKTheoryScalarNormalizedUnitary_scalar u) = oddKTheoryMatrixUnitaryClass u hu
  simp only [oddKTheoryScalarNormalizedUnitary_of_scalarIdentity u hu]

end BC4lean.KKTheory
