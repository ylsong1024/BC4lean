import BC4lean.IntervalModuleFibre
import BC4lean.HilbertModuleCoefficientApproximateUnit
import Mathlib.Topology.UrysohnsLemma

/-! # The genuine quotient norm of a continuous-coefficient fibre

For a Hilbert `C(X,B)`-module over a compact Hausdorff space, the evaluated
form norm equals the ambient Banach quotient norm by the evaluated radical.
The proof localizes vectors using an actual coefficient approximate unit
and continuous scalar cutoffs of that coefficient. In particular, no unit
of `B`, multiplier action on the module, or assumed fibre surjectivity is used.

Consequently the radical quotient is already complete for complete modules,
and the canonical map into its completed fibre is surjective. These facts
are needed to glue homotopies on arbitrary varying modules.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open UniformSpace

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M]
  [CompleteSpace M]

/-- The evaluated radical, as the kernel of the actual continuous quotient
map on the original normed module. -/
def hilbertModuleFibreNullSubmodule (t : X) : Submodule ℂ M :=
  (hilbertModuleFibreQuotientMk (B := B) (M := M) t).ker

instance hilbertModuleFibreNullSubmodule_closed (t : X) :
    IsClosed (hilbertModuleFibreNullSubmodule (B := B) (M := M) t : Set M) :=
  (hilbertModuleFibreQuotientMk (B := B) (M := M) t).isClosed_ker

omit [T2Space X] [CompleteSpace M] in
@[simp] theorem mem_hilbertModuleFibreNullSubmodule (t : X) (x : M) :
    x ∈ hilbertModuleFibreNullSubmodule (B := B) t ↔
      (evaluatedModuleOfOriginal B t x) ∈
        PositiveModuleForm.nullRadical (B := B) := by
  change hilbertModuleFibreQuotientMk (B := B) t x = 0 ↔ _
  exact PositiveModuleQuotient.mk_eq_zero (B := B)
    (E := EvaluatedModuleSpace B M t) (evaluatedModuleOfOriginal B t x)

omit [T2Space X] [CompleteSpace M] in
/-- Coefficients agreeing at `t` give the same class in the actual
evaluated-form quotient. -/
theorem hilbertModuleFibreQuotientMk_smul_eq (t : X)
    (b c : C(X, B)ᵐᵒᵖ) (hbc : MulOpposite.unop b t = MulOpposite.unop c t)
    (x : M) :
    hilbertModuleFibreQuotientMk (B := B) t (b • x) =
      hilbertModuleFibreQuotientMk (B := B) t (c • x) := by
  apply (PositiveModuleQuotient.mk_eq_mk (B := B) (E := EvaluatedModuleSpace B M t)
    (evaluatedModuleOfOriginal B t (b • x)) (evaluatedModuleOfOriginal B t (c • x))).mpr
  change ∀ y : EvaluatedModuleSpace B M t,
    ⟪evaluatedModuleOfOriginal B t (b • x) - evaluatedModuleOfOriginal B t (c • x), y⟫_(Bᵐᵒᵖ) = 0
  intro y
  rw [PositiveModuleForm.inner_sub_left]
  change evaluatedModuleInner t (evaluatedModuleOfOriginal B t (b • x)) y -
    evaluatedModuleInner t (evaluatedModuleOfOriginal B t (c • x)) y = 0
  have hb := evaluatedModule_inner_variable_smul_left t b (evaluatedModuleOfOriginal B t x) y
  have hc := evaluatedModule_inner_variable_smul_left t c (evaluatedModuleOfOriginal B t x) y
  simp only [evaluatedModule_to_of] at hb hc
  rw [hb, hc, hbc, sub_self]

/-- A scalar cutoff is applied to an actual coefficient function, rather
than assumed to act on an arbitrary nonunital coefficient module. -/
def fibreCutoffCoefficient (f : C(X, ℝ)) (e : C(X, B)ᵐᵒᵖ) : C(X, B)ᵐᵒᵖ :=
  MulOpposite.op ⟨fun s => f s • MulOpposite.unop e s,
    f.continuous.smul (MulOpposite.unop e).continuous⟩

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] [T2Space X] in
@[simp] theorem fibreCutoffCoefficient_apply (f : C(X, ℝ))
    (e : C(X, B)ᵐᵒᵖ) (s : X) :
    MulOpposite.unop (fibreCutoffCoefficient f e) s =
      f s • MulOpposite.unop e s := rfl

omit [T2Space X] [CompleteSpace M] [StarOrderedRing B] in
/-- Localized representatives have a norm controlled by the diagonal inner
product on the support of the cutoff. -/
theorem norm_fibreCutoffCoefficient_smul_le (x : M) (e : C(X, B)ᵐᵒᵖ)
    (he : ‖e‖ ≤ 1) (f : C(X, ℝ)) (hf : ∀ s, f s ∈ Set.Icc 0 1)
    (r : ℝ) (hr : 0 ≤ r)
    (hlocal : ∀ s, f s ≠ 0 →
      ‖MulOpposite.unop ⟪x, x⟫_(C(X, B)ᵐᵒᵖ) s‖ ≤ r ^ 2) :
    ‖fibreCutoffCoefficient f e • x‖ ≤ r := by
  have hsq : ‖fibreCutoffCoefficient f e • x‖ ^ 2 ≤ r ^ 2 := by
    rw [CStarModule.norm_sq_eq (C(X, B)ᵐᵒᵖ)]
    change ‖MulOpposite.unop
      ⟪fibreCutoffCoefficient f e • x,
        fibreCutoffCoefficient f e • x⟫_(C(X, B)ᵐᵒᵖ)‖ ≤ _
    apply (ContinuousMap.norm_le _ (sq_nonneg r)).mpr
    intro s
    have hei : ‖MulOpposite.unop e s‖ ≤ 1 :=
      ((MulOpposite.unop e).norm_coe_le_norm s).trans he
    have hwi : ‖MulOpposite.unop (fibreCutoffCoefficient f e) s‖ ≤ 1 := by
      rw [fibreCutoffCoefficient_apply, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (hf s).1]
      nlinarith [norm_nonneg (MulOpposite.unop e s), (hf s).2]
    have hdiag :
        MulOpposite.unop
          ⟪fibreCutoffCoefficient f e • x,
            fibreCutoffCoefficient f e • x⟫_(C(X, B)ᵐᵒᵖ) s =
          star (MulOpposite.unop (fibreCutoffCoefficient f e) s) *
            MulOpposite.unop ⟪x, x⟫_(C(X, B)ᵐᵒᵖ) s *
              MulOpposite.unop (fibreCutoffCoefficient f e) s := by
      rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left]
      rfl
    rw [hdiag]
    by_cases hz : f s = 0
    · simp [fibreCutoffCoefficient_apply, hz, sq_nonneg r]
    · calc
        _ ≤ ‖star (MulOpposite.unop (fibreCutoffCoefficient f e) s)‖ *
              ‖MulOpposite.unop ⟪x, x⟫_(C(X, B)ᵐᵒᵖ) s‖ *
                ‖MulOpposite.unop (fibreCutoffCoefficient f e) s‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1 * r ^ 2 * 1 := by
          rw [norm_star]
          exact mul_le_mul (mul_le_mul hwi (hlocal s hz)
            (norm_nonneg _) zero_le_one) hwi (norm_nonneg _)
              (mul_nonneg zero_le_one (sq_nonneg r))
        _ = r ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr (by decide : (2 : ℕ) ≠ 0)).mp hsq

omit [CompleteSpace M] in
/-- Every form-quotient class has representatives in the original module
whose ambient norms approach its evaluated-form norm. -/
theorem exists_fibreQuotient_representative_norm_lt (t : X) (x : M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : M,
      hilbertModuleFibreQuotientMk (B := B) t y =
        hilbertModuleFibreQuotientMk (B := B) t x ∧
      ‖y‖ < ‖hilbertModuleFibreQuotientMk (B := B) t x‖ + ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let q := hilbertModuleFibreQuotientMk (B := B) (M := M) t
  let r : ℝ := ‖q x‖ + δ
  have hr : 0 < r := by dsimp [r]; positivity
  let a : C(X, B) := MulOpposite.unop ⟪x, x⟫_(C(X, B)ᵐᵒᵖ)
  let V : Set X := {s | ‖a s‖ < r ^ 2}
  have hV : IsOpen V := isOpen_lt a.continuous.norm continuous_const
  have htV : t ∈ V := by
    have hq : ‖q x‖ ^ 2 = ‖a t‖ := by
      rw [hilbertModuleFibreQuotientMk_apply, PositiveModuleQuotient.norm_mk]
      change (Real.sqrt ‖a t‖) ^ 2 = ‖a t‖
      exact Real.sq_sqrt (norm_nonneg _)
    change ‖a t‖ < r ^ 2
    dsimp [r]
    nlinarith [norm_nonneg (q x)]
  obtain ⟨f, hft, _, hfV, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (isCompact_singleton (x := t)) hV (Set.singleton_subset_iff.mpr htV)
  obtain ⟨e, he, _, herr⟩ :=
    exists_selfadjoint_contraction_smul_approx
      (D := C(X, B)ᵐᵒᵖ) x δ hδ
  let w := fibreCutoffCoefficient f e
  have hwt : MulOpposite.unop w t = MulOpposite.unop e t := by
    change f t • MulOpposite.unop e t = _
    rw [hft (Set.mem_singleton t), Pi.one_apply, one_smul]
  have hw : ‖w • x‖ ≤ r := by
    apply norm_fibreCutoffCoefficient_smul_le x e he f hf r hr.le
    intro s hs
    exact (hfV (subset_tsupport f (Function.mem_support.mpr hs))).le
  refine ⟨x - e • x + w • x, ?_, ?_⟩
  · rw [map_add, map_sub,
      hilbertModuleFibreQuotientMk_smul_eq t w e hwt, sub_add_cancel]
  · calc
      _ ≤ ‖x - e • x‖ + ‖w • x‖ := norm_add_le _ _
      _ < δ + r := add_lt_add_of_lt_of_le herr hw
      _ < ‖q x‖ + ε := by dsimp [r, δ]; linarith

/-- The ambient Banach quotient by the closed evaluated radical. -/
abbrev HilbertModuleBanachFibre (B M : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [NormedAddCommGroup M] [NormedSpace ℂ M]
    [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M]
    [CompleteSpace M] (t : X) :=
  M ⧸ hilbertModuleFibreNullSubmodule (B := B) (M := M) t

omit [CompleteSpace M] in
/-- The evaluated-form norm agrees with the actual Banach quotient norm.
Completeness and fibre surjectivity are consequences of this equality. -/
theorem hilbertModuleBanachFibre_norm_mk (t : X) (x : M) :
    ‖(Submodule.Quotient.mk x : HilbertModuleBanachFibre B M t)‖ =
      ‖hilbertModuleFibreQuotientMk (B := B) t x‖ := by
  let N := hilbertModuleFibreNullSubmodule (B := B) (M := M) t
  let q := hilbertModuleFibreQuotientMk (B := B) (M := M) t
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y, hy, hnorm⟩ := exists_fibreQuotient_representative_norm_lt (B := B) t x ε hε
    have hclass : (Submodule.Quotient.mk y : M ⧸ N) = Submodule.Quotient.mk x := by
      apply (Submodule.Quotient.eq N).mpr
      change q (y - x) = 0
      rw [map_sub, hy, sub_self]
    calc
      _ = ‖(Submodule.Quotient.mk y : M ⧸ N)‖ := congrArg norm hclass.symm
      _ ≤ ‖y‖ := Submodule.Quotient.norm_mk_le N y
      _ ≤ ‖q x‖ + ε := hnorm.le
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt
      (Submodule.Quotient.mk x : M ⧸ N) hε
    have hq : q y = q x := by
      have hm := (Submodule.Quotient.eq N).mp hy
      have hz : q (y - x) = 0 := hm
      simpa only [map_sub, sub_eq_zero] using hz
    calc
      _ = ‖q y‖ := congrArg norm hq.symm
      _ ≤ ‖y‖ := evaluatedModule_formNorm_le (B := B) t
        (evaluatedModuleOfOriginal B t y)
      _ ≤ ‖(Submodule.Quotient.mk x : M ⧸ N)‖ + ε := hnorm.le

/-- The two quotient models are genuinely linearly isometric. -/
def hilbertModuleBanachFibreEquiv (t : X) :
    HilbertModuleBanachFibre B M t ≃ₗᵢ[ℂ]
      PositiveModuleQuotient B (EvaluatedModuleSpace B M t) where
  __ := (hilbertModuleFibreQuotientMk (B := B) (M := M) t).toLinearMap.quotKerEquivOfSurjective
    (hilbertModuleFibreQuotientMk_surjective (B := B) t)
  norm_map' z := by
    obtain ⟨x, rfl⟩ := (hilbertModuleFibreNullSubmodule (B := B) (M := M) t).mkQ_surjective z
    exact (hilbertModuleBanachFibre_norm_mk (B := B) t x).symm

/-- For compact Hausdorff parameters the evaluated radical quotient is
already complete, by the proved isometry with the ambient Banach quotient. -/
instance evaluatedModuleQuotient_completeSpace (t : X) :
    CompleteSpace (PositiveModuleQuotient B (EvaluatedModuleSpace B M t)) :=
  (hilbertModuleBanachFibreEquiv (B := B) (M := M) t).symm.toIsometryEquiv.completeSpace

/-- The actual canonical fibre map is surjective for arbitrary complete
continuous-coefficient modules; this is proved rather than assumed. -/
theorem hilbertModuleFibreMk_surjective (t : X) :
    Function.Surjective (hilbertModuleFibreMk (B := B) (M := M) t) := by
  let Q := PositiveModuleQuotient B (EvaluatedModuleSpace B M t)
  have hclosed : IsClosed (Set.range (fun q : Q => (q : Completion Q))) :=
    (Completion.toComplₗᵢ : Q →ₗᵢ[ℂ] Completion Q).isometry.isClosedEmbedding.isClosed_range
  have hsurj : Function.Surjective (fun q : Q => (q : Completion Q)) := by
    rw [← Set.range_eq_univ]
    exact hclosed.closure_eq ▸ Completion.denseRange_coe.closure_range
  intro z
  obtain ⟨q, rfl⟩ := hsurj z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreQuotientMk_surjective (B := B) (M := M) t q
  exact ⟨x, rfl⟩

end BC4lean.KKTheory
