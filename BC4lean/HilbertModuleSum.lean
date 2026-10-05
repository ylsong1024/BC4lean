import BC4lean.CompactModuleOperator
import BC4lean.CountablyGeneratedModule
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Logic.Equiv.Nat

/-! # Finite direct sums of right Hilbert C⋆-modules

The underlying vector space is a product, but its norm is the norm induced by
the sum of the coefficient-valued inner products. The ordinary product norm
is used only through Mathlib's proved continuous linear equivalence. Coordinate
inclusions and projections are adjointable; compact summand maps give compact
block maps by the two composition ideal properties.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B E F G H : Type*}

/-- The Hilbert-module direct sum, with its coefficient-valued Hilbert norm. -/
abbrev HilbertModuleSum (B E F : Type*) := WithCStarModule Bᵐᵒᵖ (E × F)

/-- A vector in the Hilbert-module direct sum. -/
def sumMk (x : E) (y : F) : HilbertModuleSum B E F :=
  (WithCStarModule.equiv Bᵐᵒᵖ (E × F)).symm (x, y)

@[simp] theorem sumMk_fst (x : E) (y : F) : (sumMk (B := B) x y).fst = x := rfl
@[simp] theorem sumMk_snd (x : E) (y : F) : (sumMk (B := B) x y).snd = y := rfl
@[simp] theorem sumMk_eta (x : HilbertModuleSum B E F) : sumMk x.fst x.snd = x := rfl

@[simp] theorem sumMk_zero [Zero E] [Zero F] : sumMk (B := B) (0 : E) (0 : F) = 0 := rfl
@[simp] theorem sumMk_add [Add E] [Add F] (x u : E) (y v : F) :
    sumMk (B := B) x y + sumMk u v = sumMk (x + u) (y + v) := rfl
@[simp] theorem sumMk_smul {K : Type*} [SMul K E] [SMul K F] (c : K) (x : E) (y : F) :
    c • sumMk (B := B) x y = sumMk (c • x) (c • y) := rfl

variable [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- The direct-sum inner product has the actual two coefficient summands. -/
theorem inner_sum (x y : HilbertModuleSum B E F) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = ⟪x.fst, y.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd, y.snd⟫_(Bᵐᵒᵖ) := rfl

omit [StarOrderedRing B] in
/-- The direct-sum norm is the Hilbert-module norm. -/
theorem norm_sum (x : HilbertModuleSum B E F) :
    ‖x‖ = Real.sqrt ‖⟪x.fst, x.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd, x.snd⟫_(Bᵐᵒᵖ)‖ := rfl

theorem sum_fst_norm_le (x : HilbertModuleSum B E F) : ‖x.fst‖ ≤ ‖x‖ :=
  (le_max_left _ _).trans (WithCStarModule.max_le_prod_norm x)

theorem sum_snd_norm_le (x : HilbertModuleSum B E F) : ‖x.snd‖ ≤ ‖x‖ :=
  (le_max_right _ _).trans (WithCStarModule.max_le_prod_norm x)

omit [StarOrderedRing B] in
@[simp] theorem norm_sumMk_zero (x : E) : ‖sumMk (B := B) x (0 : F)‖ = ‖x‖ := by
  rw [norm_sum]
  simp only [sumMk_fst, sumMk_snd, CStarModule.inner_zero_left, add_zero]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

omit [StarOrderedRing B] in
@[simp] theorem norm_sumMk_zero_left (y : F) : ‖sumMk (B := B) (0 : E) y‖ = ‖y‖ := by
  rw [norm_sum]
  simp only [sumMk_fst, sumMk_snd, CStarModule.inner_zero_left, zero_add]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) y).symm

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] in
/-- Completeness is transported through Mathlib's proved uniform equivalence. -/
theorem hilbertModuleSum_complete [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (HilbertModuleSum B E F) :=
  (WithCStarModule.uniformEquiv (A := Bᵐᵒᵖ) (E := E × F)).completeSpace_iff.mpr inferInstance

/-- The first coordinate inclusion as a bounded complex-linear map. -/
def sumInlCLM : E →L[ℂ] HilbertModuleSum B E F :=
  (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ) (E := E × F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ E F)

/-- The second coordinate inclusion as a bounded complex-linear map. -/
def sumInrCLM : F →L[ℂ] HilbertModuleSum B E F :=
  (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ) (E := E × F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ E F)

/-- The first coordinate projection, continuous for the actual Hilbert norm. -/
def sumFstCLM : HilbertModuleSum B E F →L[ℂ] E :=
  (ContinuousLinearMap.fst ℂ E F).comp
    (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ) (E := E × F)).toContinuousLinearMap

/-- The second coordinate projection, continuous for the actual Hilbert norm. -/
def sumSndCLM : HilbertModuleSum B E F →L[ℂ] F :=
  (ContinuousLinearMap.snd ℂ E F).comp
    (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ) (E := E × F)).toContinuousLinearMap

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] in
@[simp] theorem sumInlCLM_apply (x : E) : sumInlCLM (B := B) (F := F) x = sumMk x 0 := rfl
omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] in
@[simp] theorem sumInrCLM_apply (y : F) : sumInrCLM (B := B) (E := E) y = sumMk 0 y := rfl
omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] in
@[simp] theorem sumFstCLM_apply (x : HilbertModuleSum B E F) : sumFstCLM x = x.fst := rfl
omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] in
@[simp] theorem sumSndCLM_apply (x : HilbertModuleSum B E F) : sumSndCLM x = x.snd := rfl

/-- The first inclusion is adjointable, with adjoint the first projection. -/
def sumInl : AdjointableMap B E (HilbertModuleSum B E F) where
  toCLM := sumInlCLM
  adjointCLM := sumFstCLM
  adjoint_identity x y := by
    change ⟪x, y.fst⟫_(Bᵐᵒᵖ) + ⟪(0 : F), y.snd⟫_(Bᵐᵒᵖ) = ⟪x, y.fst⟫_(Bᵐᵒᵖ)
    simp

/-- The second inclusion is adjointable, with adjoint the second projection. -/
def sumInr : AdjointableMap B F (HilbertModuleSum B E F) where
  toCLM := sumInrCLM
  adjointCLM := sumSndCLM
  adjoint_identity x y := by
    change ⟪(0 : E), y.fst⟫_(Bᵐᵒᵖ) + ⟪x, y.snd⟫_(Bᵐᵒᵖ) = ⟪x, y.snd⟫_(Bᵐᵒᵖ)
    simp

/-- The first projection as an adjointable map. -/
def sumFst : AdjointableMap B (HilbertModuleSum B E F) E := sumInl.adjoint
/-- The second projection as an adjointable map. -/
def sumSnd : AdjointableMap B (HilbertModuleSum B E F) F := sumInr.adjoint

@[simp] theorem sumInl_apply (x : E) : sumInl (B := B) (F := F) x = sumMk x 0 := rfl
@[simp] theorem sumInr_apply (y : F) : sumInr (B := B) (E := E) y = sumMk 0 y := rfl
@[simp] theorem sumFst_apply (x : HilbertModuleSum B E F) : sumFst x = x.fst := rfl
@[simp] theorem sumSnd_apply (x : HilbertModuleSum B E F) : sumSnd x = x.snd := rfl
@[simp] theorem sumInl_adjoint : (sumInl (B := B) (E := E) (F := F)).adjoint = sumFst := rfl
@[simp] theorem sumInr_adjoint : (sumInr (B := B) (E := E) (F := F)).adjoint = sumSnd := rfl
@[simp] theorem sumFst_adjoint : (sumFst (B := B) (E := E) (F := F)).adjoint = sumInl := rfl
@[simp] theorem sumSnd_adjoint : (sumSnd (B := B) (E := E) (F := F)).adjoint = sumInr := rfl

@[simp] theorem sumFst_comp_inl :
    (sumFst (B := B) (E := E) (F := F)).comp sumInl = AdjointableMap.id := by ext x; rfl
@[simp] theorem sumSnd_comp_inr :
    (sumSnd (B := B) (E := E) (F := F)).comp sumInr = AdjointableMap.id := by ext x; rfl
@[simp] theorem sumFst_comp_inr :
    (sumFst (B := B) (E := E) (F := F)).comp sumInr = 0 := by ext x; rfl
@[simp] theorem sumSnd_comp_inl :
    (sumSnd (B := B) (E := E) (F := F)).comp sumInl = 0 := by ext x; rfl

theorem sumInl_comp_fst_add_inr_comp_snd :
    (sumInl (B := B) (E := E) (F := F)).comp sumFst + sumInr.comp sumSnd =
      AdjointableMap.id := by
  ext x
  change sumMk (B := B) x.fst (0 : F) + sumMk (0 : E) x.snd = x
  rw [sumMk_add]
  simp only [add_zero, zero_add]
  exact sumMk_eta x

theorem norm_sumInl_le : ‖sumInl (B := B) (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖sumMk (B := B) x (0 : F)‖ ≤ 1 * ‖x‖
  simp

theorem norm_sumInr_le : ‖sumInr (B := B) (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  change ‖sumMk (B := B) (0 : E) y‖ ≤ 1 * ‖y‖
  simp

theorem norm_sumFst_le : ‖sumFst (B := B) (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.fst‖ ≤ 1 * ‖x‖
  simpa using sum_fst_norm_le x

theorem norm_sumSnd_le : ‖sumSnd (B := B) (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.snd‖ ≤ 1 * ‖x‖
  simpa using sum_snd_norm_le x

/-- Block-diagonal adjointable maps, also between distinct direct sums. -/
def sumMap (S : AdjointableMap B E G) (T : AdjointableMap B F H) :
    AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B G H) :=
  ((sumInl (B := B) (E := G) (F := H)).comp S).comp sumFst +
    ((sumInr (B := B) (E := G) (F := H)).comp T).comp sumSnd

@[simp] theorem sumMap_apply (S : AdjointableMap B E G) (T : AdjointableMap B F H)
    (x : HilbertModuleSum B E F) : sumMap S T x = sumMk (S x.fst) (T x.snd) := by
  change (S x.fst, (0 : H)) + ((0 : G), T x.snd) = (S x.fst, T x.snd)
  simp

@[simp] theorem sumMap_adjoint (S : AdjointableMap B E G) (T : AdjointableMap B F H) :
    (sumMap S T).adjoint = sumMap S.adjoint T.adjoint := by
  ext x
  change (S.adjoint x.fst, (0 : F)) + ((0 : E), T.adjoint x.snd) =
    (S.adjoint x.fst, (0 : F)) + ((0 : E), T.adjoint x.snd)
  rfl

@[simp] theorem sumMap_zero : sumMap (0 : AdjointableMap B E G) (0 : AdjointableMap B F H) = 0 := by
  ext x
  apply Prod.ext <;> simp

theorem sumMap_add (S U : AdjointableMap B E G) (T V : AdjointableMap B F H) :
    sumMap (S + U) (T + V) = sumMap S T + sumMap U V := by
  ext x
  apply Prod.ext <;> simp

theorem sumMap_smul (c : ℂ) (S : AdjointableMap B E G) (T : AdjointableMap B F H) :
    sumMap (c • S) (c • T) = c • sumMap S T := by
  ext x
  apply Prod.ext <;> simp

theorem sumMap_neg (S : AdjointableMap B E G) (T : AdjointableMap B F H) :
    sumMap (-S) (-T) = -sumMap S T := by
  ext x
  apply Prod.ext <;> simp

theorem sumMap_sub (S U : AdjointableMap B E G) (T V : AdjointableMap B F H) :
    sumMap (S - U) (T - V) = sumMap S T - sumMap U V := by
  ext x
  apply Prod.ext <;> simp

@[simp] theorem sumMap_one :
    sumMap (1 : AdjointableMap B E E) (1 : AdjointableMap B F F) = 1 := by
  ext x
  apply Prod.ext <;> simp

theorem sumMap_mul (S U : AdjointableMap B E E) (T V : AdjointableMap B F F) :
    sumMap (S * U) (T * V) = sumMap S T * sumMap U V := by
  ext x
  apply Prod.ext <;> simp

@[simp] theorem sumMap_star (S : AdjointableMap B E E) (T : AdjointableMap B F F) :
    sumMap (star S) (star T) = star (sumMap S T) := sumMap_adjoint S T |>.symm

/-- Compact summand maps remain compact under the actual adjointable block embeddings. -/
theorem IsModuleCompact.sumMap {S : AdjointableMap B E G} {T : AdjointableMap B F H}
    (hS : IsModuleCompact S) (hT : IsModuleCompact T) : IsModuleCompact (sumMap S T) :=
  ((hS.comp_left (sumInl (B := B) (E := G) (F := H))).comp_right sumFst).add
    ((hT.comp_left (sumInr (B := B) (E := G) (F := H))).comp_right sumSnd)

/-- Finite direct sums of countably generated modules are countably generated. -/
theorem IsCountablyGeneratedModule.sum (hE : IsCountablyGeneratedModule B E)
    (hF : IsCountablyGeneratedModule B F) : IsCountablyGeneratedModule B (HilbertModuleSum B E F) := by
  obtain ⟨ξ, hξ⟩ := hE
  obtain ⟨η, hη⟩ := hF
  let ζ : ℕ → HilbertModuleSum B E F := fun n =>
    Sum.elim (fun k => sumMk (ξ k) 0) (fun k => sumMk 0 (η k)) (Equiv.natSumNatEquivNat.symm n)
  refine ⟨ζ, ?_⟩
  have hzL (n : ℕ) : ζ (Equiv.natSumNatEquivNat (Sum.inl n)) = sumMk (ξ n) 0 := by
    simp only [ζ, Equiv.symm_apply_apply, Sum.elim_inl]
  have hzR (n : ℕ) : ζ (Equiv.natSumNatEquivNat (Sum.inr n)) = sumMk 0 (η n) := by
    simp only [ζ, Equiv.symm_apply_apply, Sum.elim_inr]
  have hleft : ∀ x ∈ moduleGeneratingSpan (B := B) ξ,
      sumInlCLM (B := B) (F := F) x ∈ moduleGeneratingSpan (B := B) ζ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      change sumInl (B := B) (F := F) (b • ξ n) ∈ moduleGeneratingSpan (B := B) ζ
      rw [AdjointableMap.map_op_smul]
      simpa only [hzL, sumInl_apply] using
        smul_mem_moduleGeneratingSpan ζ (Equiv.natSumNatEquivNat (Sum.inl n)) b
    | zero => simpa only [map_zero] using (moduleGeneratingSpan (B := B) ζ).zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using (moduleGeneratingSpan (B := B) ζ).add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using (moduleGeneratingSpan (B := B) ζ).smul_mem c hx
  have hright : ∀ y ∈ moduleGeneratingSpan (B := B) η,
      sumInrCLM (B := B) (E := E) y ∈ moduleGeneratingSpan (B := B) ζ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨n, b, rfl⟩
      change sumInr (B := B) (E := E) (b • η n) ∈ moduleGeneratingSpan (B := B) ζ
      rw [AdjointableMap.map_op_smul]
      simpa only [hzR, sumInr_apply] using
        smul_mem_moduleGeneratingSpan ζ (Equiv.natSumNatEquivNat (Sum.inr n)) b
    | zero => simpa only [map_zero] using (moduleGeneratingSpan (B := B) ζ).zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using (moduleGeneratingSpan (B := B) ζ).add_mem hx hy
    | smul c y _ hy => simpa only [map_smul] using (moduleGeneratingSpan (B := B) ζ).smul_mem c hy
  let e := (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ) (E := E × F)).symm
  have hd : DenseRange e := e.surjective.denseRange
  apply (hd.dense_image e.continuous (hξ.prod hη)).mono
  rintro x ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
  have hsum := (moduleGeneratingSpan (B := B) ζ).add_mem (hleft u hu) (hright v hv)
  change sumMk (B := B) u v ∈ moduleGeneratingSpan (B := B) ζ
  change sumMk (B := B) u (0 : F) + sumMk (0 : E) v ∈ moduleGeneratingSpan (B := B) ζ at hsum
  rw [sumMk_add] at hsum
  simpa only [add_zero, zero_add] using hsum

/-- Exchanging summands is isometric for the coefficient-valued Hilbert norm. -/
def sumSwap : HilbertModuleSum B E F ≃ₗᵢ[ℂ] HilbertModuleSum B F E where
  toLinearEquiv := (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (E × F)).trans
    ((LinearEquiv.prodComm ℂ E F).trans
      (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (F × E)).symm)
  norm_map' x := by
    change Real.sqrt ‖⟪x.snd, x.snd⟫_(Bᵐᵒᵖ) + ⟪x.fst, x.fst⟫_(Bᵐᵒᵖ)‖ =
      Real.sqrt ‖⟪x.fst, x.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd, x.snd⟫_(Bᵐᵒᵖ)‖
    rw [add_comm]

@[simp] theorem sumSwap_apply (x : HilbertModuleSum B E F) :
    sumSwap x = sumMk x.snd x.fst := rfl

theorem sumSwap_inner (x y : HilbertModuleSum B E F) :
    ⟪sumSwap x, sumSwap y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  simp only [inner_sum, sumSwap_apply, sumMk_fst, sumMk_snd, add_comm]

@[simp] theorem sumSwap_op_smul (b : Bᵐᵒᵖ) (x : HilbertModuleSum B E F) :
    sumSwap (b • x) = b • sumSwap x := rfl

/-- Reassociation is isometric because the coefficient-valued inner sum is associative. -/
def sumAssoc : HilbertModuleSum B (HilbertModuleSum B E F) G ≃ₗᵢ[ℂ]
    HilbertModuleSum B E (HilbertModuleSum B F G) where
  toLinearEquiv :=
    { toFun := fun x => sumMk x.fst.fst (sumMk x.fst.snd x.snd)
      invFun := fun y => sumMk (sumMk y.fst y.snd.fst) y.snd.snd
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' x := by
    change Real.sqrt ‖⟪x.fst.fst, x.fst.fst⟫_(Bᵐᵒᵖ) +
      (⟪x.fst.snd, x.fst.snd⟫_(Bᵐᵒᵖ) + ⟪x.snd, x.snd⟫_(Bᵐᵒᵖ))‖ =
      Real.sqrt ‖(⟪x.fst.fst, x.fst.fst⟫_(Bᵐᵒᵖ) +
        ⟪x.fst.snd, x.fst.snd⟫_(Bᵐᵒᵖ)) + ⟪x.snd, x.snd⟫_(Bᵐᵒᵖ)‖
    rw [add_assoc]

@[simp] theorem sumAssoc_apply (x : HilbertModuleSum B (HilbertModuleSum B E F) G) :
    sumAssoc x = sumMk x.fst.fst (sumMk x.fst.snd x.snd) := rfl

theorem sumAssoc_inner (x y : HilbertModuleSum B (HilbertModuleSum B E F) G) :
    ⟪sumAssoc x, sumAssoc y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  simp only [inner_sum, sumAssoc_apply, sumMk_fst, sumMk_snd, add_assoc]

@[simp] theorem sumAssoc_op_smul (b : Bᵐᵒᵖ)
    (x : HilbertModuleSum B (HilbertModuleSum B E F) G) :
    sumAssoc (b • x) = b • sumAssoc x := rfl

end BC4lean.KKTheory
