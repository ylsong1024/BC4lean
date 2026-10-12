import BC4lean.OddKTheoryCountableRowEquiv
import BC4lean.HilbertModuleSum

/-! # Genuine splitting of completed countable sums

The finite coefficient forms split into their two actual summands. The
coordinate maps descend through the null quotients and extend to the
completions. Their inverse identities hold on the actual dense finite-vector
images. This is the whole Hilbert-module unitary needed for identity
stabilization of the infinite odd construction.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance oddContinuationOddKTheoryCountableSumEquivLocalInstance01 : CompleteSpace (HilbertModuleSum B E F) := hilbertModuleSum_complete
local instance oddContinuationOddKTheoryCountableSumEquivLocalInstance02 : CompleteSpace (HilbertModuleSum B (CountableHilbertModuleSum B E)
    (CountableHilbertModuleSum B F)) := hilbertModuleSum_complete

def oddKTheoryRowSumFstLinear :
    CountableModuleVectors (HilbertModuleSum B E F) →ₗ[ℂ] CountableModuleVectors E :=
  Finsupp.mapRange.linearMap sumFstCLM.toLinearMap

def oddKTheoryRowSumSndLinear :
    CountableModuleVectors (HilbertModuleSum B E F) →ₗ[ℂ] CountableModuleVectors F :=
  Finsupp.mapRange.linearMap sumSndCLM.toLinearMap

def oddKTheoryRowSumInlLinear :
    CountableModuleVectors E →ₗ[ℂ] CountableModuleVectors (HilbertModuleSum B E F) :=
  Finsupp.mapRange.linearMap sumInlCLM.toLinearMap

def oddKTheoryRowSumInrLinear :
    CountableModuleVectors F →ₗ[ℂ] CountableModuleVectors (HilbertModuleSum B E F) :=
  Finsupp.mapRange.linearMap sumInrCLM.toLinearMap

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumFstLinear_apply
    (x : CountableModuleVectors (HilbertModuleSum B E F)) (i : ℕ) :
    oddKTheoryRowSumFstLinear x i = (x i).fst := rfl
omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumSndLinear_apply
    (x : CountableModuleVectors (HilbertModuleSum B E F)) (i : ℕ) :
    oddKTheoryRowSumSndLinear x i = (x i).snd := rfl
omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumInlLinear_apply (x : CountableModuleVectors E) (i : ℕ) :
    oddKTheoryRowSumInlLinear (B := B) (F := F) x i = sumMk (B := B) (x i) 0 := rfl
omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumInrLinear_apply (x : CountableModuleVectors F) (i : ℕ) :
    oddKTheoryRowSumInrLinear (B := B) (E := E) x i = sumMk (B := B) 0 (x i) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumFinite_inner
    (x y : CountableModuleVectors (HilbertModuleSum B E F)) :
    countableModuleFiniteInner (B := B) x y =
      countableModuleFiniteInner (B := B) (oddKTheoryRowSumFstLinear x)
        (oddKTheoryRowSumFstLinear y) +
      countableModuleFiniteInner (B := B) (oddKTheoryRowSumSndLinear x)
        (oddKTheoryRowSumSndLinear y) := by
  have hfst : (oddKTheoryRowSumFstLinear (B := B) x).support ⊆ x.support :=
    Finsupp.support_mapRange (hf := map_zero
      (sumFstCLM (B := B) (E := E) (F := F)).toLinearMap)
  have hsnd : (oddKTheoryRowSumSndLinear (B := B) x).support ⊆ x.support :=
    Finsupp.support_mapRange (hf := map_zero
      (sumSndCLM (B := B) (E := E) (F := F)).toLinearMap)
  rw [countableModuleFiniteInner_eq_sum x y x.support Finset.Subset.rfl,
    countableModuleFiniteInner_eq_sum _ _ x.support hfst,
    countableModuleFiniteInner_eq_sum _ _ x.support hsnd]
  simp only [oddKTheoryRowSumFstLinear_apply, oddKTheoryRowSumSndLinear_apply,
    inner_sum, Finset.sum_add_distrib]

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumFst_formNorm_le
    (x : CountableModuleVectors (HilbertModuleSum B E F)) :
    PositiveModuleForm.formNorm (B := B) (oddKTheoryRowSumFstLinear x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  have hfst : 0 ≤ countableModuleFiniteInner (B := B)
      (oddKTheoryRowSumFstLinear x) (oddKTheoryRowSumFstLinear x) :=
    PositiveModuleForm.inner_self_nonneg (B := B) (x := oddKTheoryRowSumFstLinear x)
  have hsnd : 0 ≤ countableModuleFiniteInner (B := B)
      (oddKTheoryRowSumSndLinear x) (oddKTheoryRowSumSndLinear x) :=
    PositiveModuleForm.inner_self_nonneg (B := B) (x := oddKTheoryRowSumSndLinear x)
  rw [one_mul]
  unfold PositiveModuleForm.formNorm
  simp only [countableModuleFinite_inner, oddKTheoryRowSumFinite_inner]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le
    hfst
    (le_add_of_nonneg_right hsnd)

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumSnd_formNorm_le
    (x : CountableModuleVectors (HilbertModuleSum B E F)) :
    PositiveModuleForm.formNorm (B := B) (oddKTheoryRowSumSndLinear x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  have hfst : 0 ≤ countableModuleFiniteInner (B := B)
      (oddKTheoryRowSumFstLinear x) (oddKTheoryRowSumFstLinear x) :=
    PositiveModuleForm.inner_self_nonneg (B := B) (x := oddKTheoryRowSumFstLinear x)
  have hsnd : 0 ≤ countableModuleFiniteInner (B := B)
      (oddKTheoryRowSumSndLinear x) (oddKTheoryRowSumSndLinear x) :=
    PositiveModuleForm.inner_self_nonneg (B := B) (x := oddKTheoryRowSumSndLinear x)
  rw [one_mul]
  unfold PositiveModuleForm.formNorm
  simp only [countableModuleFinite_inner, oddKTheoryRowSumFinite_inner]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le
    hsnd
    (le_add_of_nonneg_left hfst)

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumInl_formNorm (x : CountableModuleVectors E) :
    PositiveModuleForm.formNorm (B := B) (oddKTheoryRowSumInlLinear (B := B) (F := F) x) =
      PositiveModuleForm.formNorm (B := B) x := by
  unfold PositiveModuleForm.formNorm
  simp only [countableModuleFinite_inner]
  congr 2
  have hs : (oddKTheoryRowSumInlLinear (B := B) (F := F) x).support ⊆ x.support :=
    Finsupp.support_mapRange (hf := map_zero
      (sumInlCLM (B := B) (E := E) (F := F)).toLinearMap)
  rw [countableModuleFiniteInner_eq_sum _ _ x.support hs,
    countableModuleFiniteInner_eq_sum x x x.support Finset.Subset.rfl]
  simp only [oddKTheoryRowSumInlLinear_apply, inner_sum, sumMk_fst, sumMk_snd,
    CStarModule.inner_zero_left, add_zero]

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumInr_formNorm (x : CountableModuleVectors F) :
    PositiveModuleForm.formNorm (B := B) (oddKTheoryRowSumInrLinear (B := B) (E := E) x) =
      PositiveModuleForm.formNorm (B := B) x := by
  unfold PositiveModuleForm.formNorm
  simp only [countableModuleFinite_inner]
  congr 2
  have hs : (oddKTheoryRowSumInrLinear (B := B) (E := E) x).support ⊆ x.support :=
    Finsupp.support_mapRange (hf := map_zero
      (sumInrCLM (B := B) (E := E) (F := F)).toLinearMap)
  rw [countableModuleFiniteInner_eq_sum _ _ x.support hs,
    countableModuleFiniteInner_eq_sum x x x.support Finset.Subset.rfl]
  simp only [oddKTheoryRowSumInrLinear_apply, inner_sum, sumMk_fst, sumMk_snd,
    CStarModule.inner_zero_left, zero_add]

def oddKTheoryRowSumQuotientInl :
    AdjointableMap B (CountableHilbertModulePreSum B E)
      (CountableHilbertModulePreSum B (HilbertModuleSum B E F)) where
  toCLM := positiveModuleQuotientLiftCLM oddKTheoryRowSumInlLinear (K := 1)
    (fun x => by rw [oddKTheoryRowSumInl_formNorm, one_mul])
  adjointCLM := positiveModuleQuotientLiftCLM oddKTheoryRowSumFstLinear
    oddKTheoryRowSumFst_formNorm_le
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    change countableModuleFiniteInner (B := B) (oddKTheoryRowSumInlLinear x) y =
      countableModuleFiniteInner (B := B) x (oddKTheoryRowSumFstLinear y)
    have hs : (oddKTheoryRowSumInlLinear (B := B) (F := F) x).support ⊆ x.support :=
      Finsupp.support_mapRange (hf := map_zero
        (sumInlCLM (B := B) (E := E) (F := F)).toLinearMap)
    rw [countableModuleFiniteInner_eq_sum _ _ x.support hs,
      countableModuleFiniteInner_eq_sum _ _ x.support Finset.Subset.rfl]
    simp only [oddKTheoryRowSumInlLinear_apply, oddKTheoryRowSumFstLinear_apply,
      inner_sum, sumMk_fst, sumMk_snd, CStarModule.inner_zero_left, add_zero]

def oddKTheoryRowSumQuotientInr :
    AdjointableMap B (CountableHilbertModulePreSum B F)
      (CountableHilbertModulePreSum B (HilbertModuleSum B E F)) where
  toCLM := positiveModuleQuotientLiftCLM oddKTheoryRowSumInrLinear (K := 1)
    (fun x => by rw [oddKTheoryRowSumInr_formNorm, one_mul])
  adjointCLM := positiveModuleQuotientLiftCLM oddKTheoryRowSumSndLinear
    oddKTheoryRowSumSnd_formNorm_le
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    change countableModuleFiniteInner (B := B) (oddKTheoryRowSumInrLinear x) y =
      countableModuleFiniteInner (B := B) x (oddKTheoryRowSumSndLinear y)
    have hs : (oddKTheoryRowSumInrLinear (B := B) (E := E) x).support ⊆ x.support :=
      Finsupp.support_mapRange (hf := map_zero
        (sumInrCLM (B := B) (E := E) (F := F)).toLinearMap)
    rw [countableModuleFiniteInner_eq_sum _ _ x.support hs,
      countableModuleFiniteInner_eq_sum _ _ x.support Finset.Subset.rfl]
    simp only [oddKTheoryRowSumInrLinear_apply, oddKTheoryRowSumSndLinear_apply,
      inner_sum, sumMk_fst, sumMk_snd, CStarModule.inner_zero_left, zero_add]

def oddKTheoryRowSumInl := (oddKTheoryRowSumQuotientInl (B := B) (E := E) (F := F)).completion
def oddKTheoryRowSumInr := (oddKTheoryRowSumQuotientInr (B := B) (E := E) (F := F)).completion
def oddKTheoryRowSumFst := (oddKTheoryRowSumInl (B := B) (E := E) (F := F)).adjoint
def oddKTheoryRowSumSnd := (oddKTheoryRowSumInr (B := B) (E := E) (F := F)).adjoint

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumInl_mk (x : CountableModuleVectors E) :
    oddKTheoryRowSumInl (F := F) (countableModuleMk (B := B) x) =
      countableModuleMk (B := B) (oddKTheoryRowSumInlLinear x) := by
  rw [countableModuleMk_apply, oddKTheoryRowSumInl, AdjointableMap.completion_apply_coe,
    countableModuleMk_apply]
  rfl
omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumInr_mk (x : CountableModuleVectors F) :
    oddKTheoryRowSumInr (E := E) (countableModuleMk (B := B) x) =
      countableModuleMk (B := B) (oddKTheoryRowSumInrLinear x) := by
  rw [countableModuleMk_apply, oddKTheoryRowSumInr, AdjointableMap.completion_apply_coe,
    countableModuleMk_apply]
  rfl
omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumFst_mk (x : CountableModuleVectors (HilbertModuleSum B E F)) :
    oddKTheoryRowSumFst (countableModuleMk (B := B) x) =
      countableModuleMk (B := B) (oddKTheoryRowSumFstLinear x) := by
  rw [countableModuleMk_apply, oddKTheoryRowSumFst, oddKTheoryRowSumInl,
    AdjointableMap.completion_adjoint, AdjointableMap.completion_apply_coe, countableModuleMk_apply]
  rfl
omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumSnd_mk (x : CountableModuleVectors (HilbertModuleSum B E F)) :
    oddKTheoryRowSumSnd (countableModuleMk (B := B) x) =
      countableModuleMk (B := B) (oddKTheoryRowSumSndLinear x) := by
  rw [countableModuleMk_apply, oddKTheoryRowSumSnd, oddKTheoryRowSumInr,
    AdjointableMap.completion_adjoint, AdjointableMap.completion_apply_coe, countableModuleMk_apply]
  rfl

def oddKTheoryRowSumSplit : AdjointableMap B
    (CountableHilbertModuleSum B (HilbertModuleSum B E F))
    (HilbertModuleSum B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B F)) :=
  sumInl.comp oddKTheoryRowSumFst + sumInr.comp oddKTheoryRowSumSnd

def oddKTheoryRowSumJoin : AdjointableMap B
    (HilbertModuleSum B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B F))
    (CountableHilbertModuleSum B (HilbertModuleSum B E F)) :=
  oddKTheoryRowSumInl.comp sumFst + oddKTheoryRowSumInr.comp sumSnd

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumSplit_adjoint :
    (oddKTheoryRowSumSplit (B := B) (E := E) (F := F)).adjoint = oddKTheoryRowSumJoin := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumSplit_mk (x : CountableModuleVectors (HilbertModuleSum B E F)) :
    oddKTheoryRowSumSplit (countableModuleMk (B := B) x) =
      sumMk (countableModuleMk (B := B) (oddKTheoryRowSumFstLinear x))
        (countableModuleMk (B := B) (oddKTheoryRowSumSndLinear x)) := by
  simp only [oddKTheoryRowSumSplit, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
    oddKTheoryRowSumFst_mk, oddKTheoryRowSumSnd_mk, sumInl_apply, sumInr_apply,
    sumMk_add, zero_add, add_zero]

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem oddKTheoryRowSumJoin_mk (x : CountableModuleVectors E)
    (y : CountableModuleVectors F) :
    oddKTheoryRowSumJoin (sumMk (countableModuleMk (B := B) x) (countableModuleMk (B := B) y)) =
      countableModuleMk (B := B) (oddKTheoryRowSumInlLinear x + oddKTheoryRowSumInrLinear y) := by
  simp only [oddKTheoryRowSumJoin, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
    sumFst_apply, sumSnd_apply, sumMk_fst, sumMk_snd, oddKTheoryRowSumInl_mk,
    oddKTheoryRowSumInr_mk, map_add]

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumJoin_comp_split :
    (oddKTheoryRowSumJoin (B := B) (E := E) (F := F)).comp oddKTheoryRowSumSplit = AdjointableMap.id := by
  ext z
  refine countableModuleMk_denseRange.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  simp only [AdjointableMap.comp_apply, oddKTheoryRowSumSplit_mk, oddKTheoryRowSumJoin_mk,
    AdjointableMap.id_apply]
  congr 1
  ext i
  simp only [Finsupp.add_apply, oddKTheoryRowSumInlLinear_apply, oddKTheoryRowSumInrLinear_apply,
    oddKTheoryRowSumFstLinear_apply, oddKTheoryRowSumSndLinear_apply, sumMk_add,
    add_zero, zero_add, sumMk_eta]

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumMk_denseRange : DenseRange
    (fun p : CountableModuleVectors E × CountableModuleVectors F =>
      sumMk (B := B) (countableModuleMk (B := B) p.1) (countableModuleMk (B := B) p.2)) := by
  let e := (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ)
    (E := CountableHilbertModuleSum B E × CountableHilbertModuleSum B F)).symm
  exact e.surjective.denseRange.comp
    (countableModuleMk_denseRange.prodMap countableModuleMk_denseRange) e.continuous

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumSplit_comp_join :
    (oddKTheoryRowSumSplit (B := B) (E := E) (F := F)).comp oddKTheoryRowSumJoin = AdjointableMap.id := by
  ext z
  refine oddKTheoryRowSumMk_denseRange.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  rintro ⟨x, y⟩
  simp only [AdjointableMap.comp_apply, oddKTheoryRowSumJoin_mk, oddKTheoryRowSumSplit_mk,
    AdjointableMap.id_apply]
  apply congrArg₂ (sumMk (B := B))
  · apply congrArg (countableModuleMk (B := B) (E := E))
    ext i
    change x i + 0 = x i
    exact add_zero _
  · apply congrArg (countableModuleMk (B := B) (E := F))
    ext i
    change 0 + y i = y i
    exact zero_add _

omit [CompleteSpace E] [CompleteSpace F] in
theorem oddKTheoryRowSumSplit_inner (x y : CountableHilbertModuleSum B (HilbertModuleSum B E F)) :
    ⟪oddKTheoryRowSumSplit x, oddKTheoryRowSumSplit y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(oddKTheoryRowSumSplit (B := B) (E := E) (F := F)).adjoint_identity]
  change ⟪x, (oddKTheoryRowSumSplit (B := B) (E := E) (F := F)).adjoint
    (oddKTheoryRowSumSplit y)⟫_(Bᵐᵒᵖ) = _
  rw [oddKTheoryRowSumSplit_adjoint, ← AdjointableMap.comp_apply,
    oddKTheoryRowSumJoin_comp_split, AdjointableMap.id_apply]

def oddKTheoryCountableSumEquiv : HilbertModuleEquiv B
    (CountableHilbertModuleSum B (HilbertModuleSum B E F))
    (HilbertModuleSum B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B F)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := oddKTheoryRowSumSplit
          invFun := oddKTheoryRowSumJoin
          left_inv x := by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
              congrArg (fun T => T x) (oddKTheoryRowSumJoin_comp_split (B := B) (E := E) (F := F))
          right_inv x := by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
              congrArg (fun T => T x) (oddKTheoryRowSumSplit_comp_join (B := B) (E := E) (F := F))
          map_add' := (oddKTheoryRowSumSplit (B := B) (E := E) (F := F)).toCLM.map_add
          map_smul' := (oddKTheoryRowSumSplit (B := B) (E := E) (F := F)).toCLM.map_smul }
      norm_map' x := by
        change ‖oddKTheoryRowSumSplit x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), oddKTheoryRowSumSplit_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := oddKTheoryRowSumSplit_inner

@[simp] theorem oddKTheoryCountableSumEquiv_inclusion (i : ℕ) (x : HilbertModuleSum B E F) :
    oddKTheoryCountableSumEquiv (countableModuleInclusion i x) =
      sumMk (countableModuleInclusion i x.fst) (countableModuleInclusion i x.snd) := by
  change oddKTheoryRowSumSplit (countableModuleInclusion (B := B) i x) =
    sumMk (countableModuleInclusion (B := B) i x.fst) (countableModuleInclusion (B := B) i x.snd)
  simp only [countableModuleInclusion_apply, oddKTheoryRowSumSplit_mk]
  apply congrArg₂ (sumMk (B := B))
  · apply congrArg (countableModuleMk (B := B) (E := E))
    ext j
    by_cases h : i = j <;> simp [oddKTheoryRowSumFstLinear_apply, h]
  · apply congrArg (countableModuleMk (B := B) (E := F))
    ext j
    by_cases h : i = j <;> simp [oddKTheoryRowSumSndLinear_apply, h]

end BC4lean.KKTheory
