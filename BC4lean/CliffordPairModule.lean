import BC4lean.CliffordCoefficientRange

/-! # The genuine product-coefficient module used for Clifford parity

For a right Hilbert B-module H, the two copies of H are acted on separately
by the two coefficient coordinates. The inner product is the pair of the
two B-valued inner products, so the genuine module norm is the ordinary max
norm on H × H. It differs from the Hilbert direct sum over B, whose inner
product is a sum. All module laws and countable generation are proved here.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B H K : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K] [SMul Bᵐᵒᵖ K] [CStarModule Bᵐᵒᵖ K]

/-- A distinct carrier for the product-coefficient module, with its max norm. -/
def CliffordPairModule (_B H : Type*) := H × H

instance cliffordPairNormedAddCommGroup : NormedAddCommGroup (CliffordPairModule B H) :=
  inferInstanceAs (NormedAddCommGroup (H × H))

instance cliffordPairNormedSpace : NormedSpace ℂ (CliffordPairModule B H) :=
  inferInstanceAs (NormedSpace ℂ (H × H))

omit [StarOrderedRing B] in
private theorem cliffordPair_zero_op_smul (x : H) : (0 : Bᵐᵒᵖ) • x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero, zero_mul] using module_norm_smul_le (0 : Bᵐᵒᵖ) x

instance cliffordPairSMul : SMul (B × B)ᵐᵒᵖ (CliffordPairModule B H) where
  smul b x :=
    (MulOpposite.op (MulOpposite.unop b).1 • x.1,
      MulOpposite.op (MulOpposite.unop b).2 • x.2)

def cliffordPairMk (x y : H) : CliffordPairModule B H := (x, y)

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CStarModule Bᵐᵒᵖ H] in
@[simp] theorem cliffordPair_smul (b : (B × B)ᵐᵒᵖ) (x : CliffordPairModule B H) :
    b • x = cliffordPairMk (MulOpposite.op (MulOpposite.unop b).1 • x.1)
      (MulOpposite.op (MulOpposite.unop b).2 • x.2) := rfl

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H] in
@[simp] theorem cliffordPair_norm (x : CliffordPairModule B H) :
    ‖x‖ = max ‖x.1‖ ‖x.2‖ := Prod.norm_def _

/-- The genuine product-coefficient Hilbert-module structure. -/
instance cliffordPairCStarModule : CStarModule (B × B)ᵐᵒᵖ (CliffordPairModule B H) where
  inner x y := MulOpposite.op
    (MulOpposite.unop ⟪x.1, y.1⟫_(Bᵐᵒᵖ), MulOpposite.unop ⟪x.2, y.2⟫_(Bᵐᵒᵖ))
  inner_add_right := by
    intro x y z
    apply MulOpposite.unop_injective
    ext <;> exact congrArg MulOpposite.unop (CStarModule.inner_add_right (A := Bᵐᵒᵖ))
  inner_self_nonneg {x} := by
    change (0 : B) ≤ MulOpposite.unop ⟪x.1, x.1⟫_(Bᵐᵒᵖ) ∧
      (0 : B) ≤ MulOpposite.unop ⟪x.2, x.2⟫_(Bᵐᵒᵖ)
    constructor
    · change (0 : Bᵐᵒᵖ) ≤ ⟪x.1, x.1⟫_(Bᵐᵒᵖ)
      exact CStarModule.inner_self_nonneg
    · change (0 : Bᵐᵒᵖ) ≤ ⟪x.2, x.2⟫_(Bᵐᵒᵖ)
      exact CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro h
      have h1 := congrArg (fun a : (B × B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop a).1) h
      have h2 := congrArg (fun a : (B × B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop a).2) h
      apply Prod.ext
      · exact CStarModule.inner_self.mp h1
      · exact CStarModule.inner_self.mp h2
    · intro h
      rw [h]
      apply MulOpposite.unop_injective
      change (MulOpposite.unop ⟪(0 : H), (0 : H)⟫_(Bᵐᵒᵖ),
        MulOpposite.unop ⟪(0 : H), (0 : H)⟫_(Bᵐᵒᵖ)) = (0, 0)
      simp only [CStarModule.inner_zero_left, MulOpposite.unop_zero]
  inner_op_smul_right := by
    intro b x y
    apply MulOpposite.unop_injective
    ext <;> exact congrArg MulOpposite.unop (CStarModule.inner_op_smul_right (A := Bᵐᵒᵖ))
  inner_smul_right_complex := by
    intro c x y
    apply MulOpposite.unop_injective
    ext <;> exact congrArg MulOpposite.unop (CStarModule.inner_smul_right_complex (A := Bᵐᵒᵖ))
  star_inner x y := by
    apply MulOpposite.unop_injective
    ext <;> exact congrArg MulOpposite.unop (CStarModule.star_inner (A := Bᵐᵒᵖ) _ _)
  norm_eq_sqrt_norm_inner_self x := by
    change max ‖x.1‖ ‖x.2‖ = Real.sqrt
      (max ‖⟪x.1, x.1⟫_(Bᵐᵒᵖ)‖ ‖⟪x.2, x.2⟫_(Bᵐᵒᵖ)‖)
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x.1,
      CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x.2]
    rcases le_total ‖⟪x.1, x.1⟫_(Bᵐᵒᵖ)‖ ‖⟪x.2, x.2⟫_(Bᵐᵒᵖ)‖ with h | h
    · rw [max_eq_right h, max_eq_right (Real.sqrt_le_sqrt h)]
    · rw [max_eq_left h, max_eq_left (Real.sqrt_le_sqrt h)]

omit [StarOrderedRing B] in
@[simp] theorem cliffordPair_inner (x y : CliffordPairModule B H) :
    ⟪x, y⟫_((B × B)ᵐᵒᵖ) = MulOpposite.op
      (MulOpposite.unop ⟪x.1, y.1⟫_(Bᵐᵒᵖ), MulOpposite.unop ⟪x.2, y.2⟫_(Bᵐᵒᵖ)) := rfl

instance cliffordPairCompleteSpace [CompleteSpace H] : CompleteSpace (CliffordPairModule B H) :=
  inferInstanceAs (CompleteSpace (H × H))

omit [StarOrderedRing B] in
/-- The two coefficient ideals are generated by interleaved genuine B generators. -/
theorem IsCountablyGeneratedModule.cliffordPair (hH : IsCountablyGeneratedModule B H) :
    IsCountablyGeneratedModule (B × B) (CliffordPairModule B H) := by
  obtain ⟨ξ, hξ⟩ := hH
  let ζ : ℕ → CliffordPairModule B H := fun n =>
    Sum.elim (fun k => cliffordPairMk (ξ k) 0) (fun k => cliffordPairMk 0 (ξ k))
      (Equiv.natSumNatEquivNat.symm n)
  refine ⟨ζ, ?_⟩
  have hzL (n : ℕ) : ζ (Equiv.natSumNatEquivNat (Sum.inl n)) = cliffordPairMk (ξ n) 0 := by
    simp only [ζ, Equiv.symm_apply_apply, Sum.elim_inl]
  have hzR (n : ℕ) : ζ (Equiv.natSumNatEquivNat (Sum.inr n)) = cliffordPairMk 0 (ξ n) := by
    simp only [ζ, Equiv.symm_apply_apply, Sum.elim_inr]
  let inl : H →L[ℂ] CliffordPairModule B H := ContinuousLinearMap.inl ℂ H H
  let inr : H →L[ℂ] CliffordPairModule B H := ContinuousLinearMap.inr ℂ H H
  have hleft : ∀ x ∈ moduleGeneratingSpan (B := B) ξ,
      inl x ∈ moduleGeneratingSpan (B := B × B) ζ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      have h := smul_mem_moduleGeneratingSpan ζ (Equiv.natSumNatEquivNat (Sum.inl n))
        (cliffordCoordinateEmbedding true b)
      rw [hzL] at h
      change cliffordPairMk (b • ξ n) ((0 : Bᵐᵒᵖ) • (0 : H)) ∈
        moduleGeneratingSpan (B := B × B) ζ at h
      rw [cliffordPair_zero_op_smul] at h
      change cliffordPairMk (b • ξ n) 0 ∈ moduleGeneratingSpan (B := B × B) ζ
      exact h
    | zero => simpa only [map_zero] using (moduleGeneratingSpan (B := B × B) ζ).zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using (moduleGeneratingSpan (B := B × B) ζ).add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using (moduleGeneratingSpan (B := B × B) ζ).smul_mem c hx
  have hright : ∀ x ∈ moduleGeneratingSpan (B := B) ξ,
      inr x ∈ moduleGeneratingSpan (B := B × B) ζ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      have h := smul_mem_moduleGeneratingSpan ζ (Equiv.natSumNatEquivNat (Sum.inr n))
        (cliffordCoordinateEmbedding false b)
      rw [hzR] at h
      change cliffordPairMk ((0 : Bᵐᵒᵖ) • (0 : H)) (b • ξ n) ∈
        moduleGeneratingSpan (B := B × B) ζ at h
      rw [cliffordPair_zero_op_smul] at h
      change cliffordPairMk 0 (b • ξ n) ∈ moduleGeneratingSpan (B := B × B) ζ
      exact h
    | zero => simpa only [map_zero] using (moduleGeneratingSpan (B := B × B) ζ).zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using (moduleGeneratingSpan (B := B × B) ζ).add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using (moduleGeneratingSpan (B := B × B) ζ).smul_mem c hx
  apply (hξ.prod hξ).mono
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have h := (moduleGeneratingSpan (B := B × B) ζ).add_mem (hleft x hx) (hright y hy)
  change cliffordPairMk x y ∈ moduleGeneratingSpan (B := B × B) ζ
  convert h using 1
  change (x, y) = (x, (0 : H)) + (0, y)
  exact Prod.ext (add_zero x).symm (zero_add y).symm

/-- Swapping the coordinates is the genuine semilinear module grading. -/
def cliffordPairGrading :
    GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (B × B)) (CliffordPairModule B H) where
  grading :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := Prod.swap_swap
      right_inv := Prod.swap_swap
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      norm_map' x := max_comm ‖x.2‖ ‖x.1‖ }
  involutive := Prod.swap_swap
  inner_grading _ _ := rfl

/-- A pair of genuine B-adjointable maps acts diagonally on the two
coefficient ideals. Its adjoint is the pair of the actual adjoints. -/
def cliffordPairMap (S T : AdjointableMap B H K) :
    AdjointableMap (B × B) (CliffordPairModule B H) (CliffordPairModule B K) where
  toCLM := S.toCLM.prodMap T.toCLM
  adjointCLM := S.adjointCLM.prodMap T.adjointCLM
  adjoint_identity x y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · exact congrArg MulOpposite.unop (S.adjoint_identity x.1 y.1)
    · exact congrArg MulOpposite.unop (T.adjoint_identity x.2 y.2)

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_apply (S T : AdjointableMap B H K) (x : CliffordPairModule B H) :
    cliffordPairMap S T x = cliffordPairMk (S x.1) (T x.2) := rfl

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_zero :
    cliffordPairMap (0 : AdjointableMap B H K) 0 = 0 := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_add (S T U V : AdjointableMap B H K) :
    cliffordPairMap (S + U) (T + V) = cliffordPairMap S T + cliffordPairMap U V := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_smul (c : ℂ) (S T : AdjointableMap B H K) :
    cliffordPairMap (c • S) (c • T) = c • cliffordPairMap S T := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_sub (S T U V : AdjointableMap B H K) :
    cliffordPairMap (S - U) (T - V) = cliffordPairMap S T - cliffordPairMap U V := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_star (S T : AdjointableMap B H H) :
    cliffordPairMap (star S) (star T) = star (cliffordPairMap S T) := rfl

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_mul (S T U V : AdjointableMap B H H) :
    cliffordPairMap (S * U) (T * V) = cliffordPairMap S T * cliffordPairMap U V := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem cliffordPairMap_one :
    cliffordPairMap (1 : AdjointableMap B H H) 1 = 1 := by ext x; rfl

omit [StarOrderedRing B] in
/-- A diagonal operator obeys the actual max-norm bound. -/
theorem cliffordPairMap_norm_le (S T : AdjointableMap B H K) :
    ‖cliffordPairMap S T‖ ≤ max ‖S‖ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _))
  intro x
  change ‖cliffordPairMap S T x‖ ≤ max ‖S‖ ‖T‖ * ‖x‖
  rw [cliffordPairMap_apply, cliffordPair_norm]
  apply max_le
  · exact (S.toCLM.le_opNorm x.1).trans
      (mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) (le_max_of_le_left (norm_nonneg _)))
  · exact (T.toCLM.le_opNorm x.2).trans
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) (le_max_of_le_left (norm_nonneg _)))

/-- The first or second block embedding is a genuinely continuous linear map. -/
def cliffordPairBlockMap (k : Bool) : AdjointableMap B H K →L[ℂ]
    AdjointableMap (B × B) (CliffordPairModule B H) (CliffordPairModule B K) :=
  ({ toFun T := if k then cliffordPairMap T 0 else cliffordPairMap 0 T
     map_add' S T := by
       cases k
       · simp only [Bool.false_eq_true, ↓reduceIte]
         simpa only [zero_add] using cliffordPairMap_add (0 : AdjointableMap B H K) S 0 T
       · simpa only [↓reduceIte, zero_add] using cliffordPairMap_add S (0 : AdjointableMap B H K) T 0
     map_smul' c T := by
       cases k
       · simp only [Bool.false_eq_true, ↓reduceIte]
         simpa only [smul_zero, RingHom.id_apply] using cliffordPairMap_smul c (0 : AdjointableMap B H K) T
       · simpa only [↓reduceIte, smul_zero, RingHom.id_apply] using cliffordPairMap_smul c T (0 : AdjointableMap B H K) } :
      AdjointableMap B H K →ₗ[ℂ]
        AdjointableMap (B × B) (CliffordPairModule B H) (CliffordPairModule B K)).mkContinuous
    1 (fun T => by
      cases k
      · change ‖cliffordPairMap (0 : AdjointableMap B H K) T‖ ≤ 1 * ‖T‖
        simpa only [norm_zero, max_eq_right (norm_nonneg _), one_mul] using
          cliffordPairMap_norm_le (0 : AdjointableMap B H K) T
      · change ‖cliffordPairMap T (0 : AdjointableMap B H K)‖ ≤ 1 * ‖T‖
        simpa only [norm_zero, max_eq_left (norm_nonneg _), one_mul] using
          cliffordPairMap_norm_le T (0 : AdjointableMap B H K))

/-- Rank-one block embeddings are the actual product-module rank-one maps. -/
theorem cliffordPairBlockMap_rankOne (k : Bool) (x : K) (y : H) :
    cliffordPairBlockMap k (moduleRankOne (B := B) x y) =
      moduleRankOne (B := B × B)
        (if k then cliffordPairMk x 0 else cliffordPairMk 0 x)
        (if k then cliffordPairMk y 0 else cliffordPairMk 0 y) := by
  change (if k then cliffordPairMap (moduleRankOne (B := B) x y) 0
    else cliffordPairMap 0 (moduleRankOne (B := B) x y)) = _
  cases k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply AdjointableMap.ext
    intro z
    change cliffordPairMk (B := B) 0 (⟪y, z.2⟫_(Bᵐᵒᵖ) • x) =
      ⟪cliffordPairMk (B := B) 0 y, z⟫_((B × B)ᵐᵒᵖ) • cliffordPairMk (B := B) 0 x
    rw [cliffordPair_inner, cliffordPair_smul]
    simp only [cliffordPairMk, CStarModule.inner_zero_left,
      MulOpposite.unop_zero, MulOpposite.unop_op]
    apply Prod.ext
    · change (0 : K) = (0 : Bᵐᵒᵖ) • (0 : K)
      exact (cliffordPair_zero_op_smul (0 : K)).symm
    · change ⟪y, z.2⟫_(Bᵐᵒᵖ) • x =
        MulOpposite.op (MulOpposite.unop ⟪y, z.2⟫_(Bᵐᵒᵖ)) • x
      rw [MulOpposite.op_unop]
  · simp only [↓reduceIte]
    apply AdjointableMap.ext
    intro z
    change cliffordPairMk (B := B) (⟪y, z.1⟫_(Bᵐᵒᵖ) • x) 0 =
      ⟪cliffordPairMk (B := B) y 0, z⟫_((B × B)ᵐᵒᵖ) • cliffordPairMk (B := B) x 0
    rw [cliffordPair_inner, cliffordPair_smul]
    simp only [cliffordPairMk, CStarModule.inner_zero_left,
      MulOpposite.unop_zero, MulOpposite.unop_op]
    apply Prod.ext
    · change ⟪y, z.1⟫_(Bᵐᵒᵖ) • x =
        MulOpposite.op (MulOpposite.unop ⟪y, z.1⟫_(Bᵐᵒᵖ)) • x
      rw [MulOpposite.op_unop]
    · change (0 : K) = (0 : Bᵐᵒᵖ) • (0 : K)
      exact (cliffordPair_zero_op_smul (0 : K)).symm

/-- Actual compactness passes to a block by the proved rank-one formula and
the closed rank-one-span definition, without assuming a compactness equivalence. -/
theorem IsModuleCompact.cliffordPairBlock {T : AdjointableMap B H K}
    (hT : IsModuleCompact T) (k : Bool) : IsModuleCompact (cliffordPairBlockMap k T) := by
  let S := (moduleCompact (B × B) (CliffordPairModule B H) (CliffordPairModule B K)).comap
    (cliffordPairBlockMap k).toLinearMap
  have hS : IsClosed (S : Set (AdjointableMap B H K)) :=
    moduleCompact_isClosed.preimage (cliffordPairBlockMap k).continuous
  apply moduleCompact_le_of_isClosed S hS ?_ hT
  intro x y
  change cliffordPairBlockMap k (moduleRankOne (B := B) x y) ∈
    moduleCompact (B × B) (CliffordPairModule B H) (CliffordPairModule B K)
  rw [cliffordPairBlockMap_rankOne]
  exact moduleRankOne_mem_moduleCompact _ _

/-- Compactness of two genuine B maps supplies actual product-module
compactness of their diagonal pair. -/
theorem IsModuleCompact.cliffordPairMap {S T : AdjointableMap B H K}
    (hS : IsModuleCompact S) (hT : IsModuleCompact T) : IsModuleCompact (KKTheory.cliffordPairMap S T) := by
  have h := (hS.cliffordPairBlock true).add (hT.cliffordPairBlock false)
  have heq : cliffordPairBlockMap true S + cliffordPairBlockMap false T = KKTheory.cliffordPairMap S T := by
    change KKTheory.cliffordPairMap S 0 + KKTheory.cliffordPairMap 0 T = KKTheory.cliffordPairMap S T
    simpa only [add_zero, zero_add] using (cliffordPairMap_add S (0 : AdjointableMap B H K) 0 T).symm
  exact heq ▸ h

/-- A genuine group action on H acts separately on the two coordinates. -/
def cliffordPairActionIsometry {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule β H) (g : Γ) :
    CliffordPairModule B H ≃ₗᵢ[ℂ] CliffordPairModule B H where
  toFun x := cliffordPairMk (U.action g x.1) (U.action g x.2)
  invFun x := cliffordPairMk (U.action g⁻¹ x.1) (U.action g⁻¹ x.2)
  left_inv x := by apply Prod.ext <;> exact U.inv_apply_apply g _
  right_inv x := by apply Prod.ext <;> exact U.apply_inv_apply g _
  map_add' x y := by apply Prod.ext <;> exact (U.action g).map_add _ _
  map_smul' c x := by apply Prod.ext <;> exact (U.action g).map_smul _ _
  norm_map' x := by
    change max ‖U.action g x.1‖ ‖U.action g x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [(U.action g).norm_map, (U.action g).norm_map]

def cliffordPairAction {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule β H) :
    EquivariantHilbertModule (cliffordCoefficientAction β) (CliffordPairModule B H) where
  action :=
    { toFun := cliffordPairActionIsometry U
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro x
        apply Prod.ext <;> exact U.one_apply _
      map_mul' g h := by
        apply LinearIsometryEquiv.ext
        intro x
        apply Prod.ext <;> exact U.mul_apply g h _ }
  inner_action g x y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · exact congrArg MulOpposite.unop (U.inner_action g x.1 y.1)
    · exact congrArg MulOpposite.unop (U.inner_action g x.2 y.2)

omit [StarOrderedRing B] in
theorem cliffordPairAction_preservesGrading {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule β H) :
    (cliffordPairAction U).PreservesGrading cliffordPairGrading := fun _ _ => rfl

omit [StarOrderedRing B] in
theorem cliffordPairAction_conjugate {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule β H) (g : Γ) (S T : AdjointableMap B H H) :
    (cliffordPairAction U).conjugateOperator g (cliffordPairMap S T) =
      cliffordPairMap (U.conjugateOperator g S) (U.conjugateOperator g T) := by
  ext x
  rfl

/-- Diagonal B operators give an actual unital complex star homomorphism. -/
def cliffordPairDiagonalHom [CompleteSpace H] :
    AdjointableMap B H H →⋆ₐ[ℂ] AdjointableMap (B × B) (CliffordPairModule B H) (CliffordPairModule B H) where
  toFun T := cliffordPairMap T T
  map_zero' := cliffordPairMap_zero
  map_add' S T := cliffordPairMap_add S S T T
  map_one' := cliffordPairMap_one
  map_mul' S T := cliffordPairMap_mul S S T T
  map_star' T := cliffordPairMap_star T T
  commutes' c := by ext x; rfl

end BC4lean.KKTheory
