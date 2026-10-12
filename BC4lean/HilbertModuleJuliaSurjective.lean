import BC4lean.HilbertModuleJuliaSynthesis

/-! # Exact finite preimages and the countable Julia unitary

Backward application of the actual Julia inverse, with terminal residual zero,
constructs an exact finitely supported input for every finite output. The
completed synthesis is an isometry, hence has closed range. Since that range
contains all genuine finite vectors, it is the whole completed countable sum.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

def countableModuleCons (v : F) (h : CountableModuleVectors F) : CountableModuleVectors F :=
  Finsupp.single 0 v + h.embDomain ⟨Nat.succ, Nat.succ_injective⟩

omit [NormedSpace ℂ F] [CompleteSpace F] in
@[simp] theorem countableModuleCons_zero (v : F) (h : CountableModuleVectors F) :
    countableModuleCons v h 0 = v := by
  simp only [countableModuleCons, Finsupp.add_apply, Finsupp.single_eq_same]
  rw [Finsupp.embDomain_of_notMem_range]
  · exact add_zero v
  · rintro ⟨n, hn⟩
    exact Nat.noConfusion hn

omit [NormedSpace ℂ F] [CompleteSpace F] in
@[simp] theorem countableModuleCons_succ (v : F) (h : CountableModuleVectors F) (n : ℕ) :
    countableModuleCons v h (n + 1) = h n := by
  simp only [countableModuleCons, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (Nat.succ_ne_zero n), zero_add]
  exact Finsupp.embDomain_apply_self ⟨Nat.succ, Nat.succ_injective⟩ h n

omit [CompleteSpace F] in
theorem juliaResidual_cons_shift (T : AdjointableMap B F E) (e e' : E)
    (v : F) (h : CountableModuleVectors F) (hFirst : juliaTargetDefect T e + T v = e') (n : ℕ) :
    juliaResidual T e (countableModuleCons v h) (n + 1) = juliaResidual T e' h n := by
  induction n with
  | zero => simpa only [juliaResidual_succ, juliaResidual_zero, countableModuleCons_zero] using hFirst
  | succ n ih =>
    change juliaTargetDefect T (juliaResidual T e (countableModuleCons v h) (n + 1)) +
      T (countableModuleCons v h (n + 1)) = juliaTargetDefect T (juliaResidual T e' h n) + T (h n)
    rw [ih, countableModuleCons_succ]

theorem juliaOutput_cons_shift (T : AdjointableMap B F E) (e e' : E)
    (v : F) (h : CountableModuleVectors F) (hFirst : juliaTargetDefect T e + T v = e') (n : ℕ) :
    juliaOutput T e (countableModuleCons v h) (n + 1) = juliaOutput T e' h n := by
  rw [juliaOutput, juliaOutput, juliaResidual_cons_shift T e e' v h hFirst,
    countableModuleCons_succ]

/-- Backward Julia inversion constructs exact finite-input preimages of every
sequence that vanishes beyond a finite index. -/
theorem juliaOutput_finite_preimage (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (N : ℕ) (y : ℕ → F) (hTail : ∀ n ≥ N, y n = 0) :
    ∃ e : E, ∃ h : CountableModuleVectors F, ∀ n, juliaOutput T e h n = y n := by
  induction N generalizing y with
  | zero =>
    refine ⟨0, 0, ?_⟩
    intro n
    have hr : juliaResidual T (0 : E) (0 : CountableModuleVectors F) n = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [juliaResidual_succ, ih, Finsupp.zero_apply, map_zero, add_zero]
    simp only [juliaOutput, hr, Finsupp.zero_apply, map_zero, neg_zero, add_zero,
      hTail n (Nat.zero_le n)]
  | succ N ih =>
    obtain ⟨e', h', hh'⟩ := ih (fun n => y (n + 1)) (fun n hn => hTail (n + 1) (by omega))
    let J := contractiveJuliaEquiv T hT
    let u := J.symm (sumMk e' (y 0))
    have hu : J u = sumMk e' (y 0) := J.apply_symm_apply _
    have hFirst : juliaTargetDefect T u.fst + T u.snd = e' := by
      have hf := congrArg (fun x : HilbertModuleSum B E F => x.fst) hu
      simpa only [J, contractiveJuliaEquiv_apply, sumMk_fst] using hf
    have hOutput : -T.adjoint u.fst + juliaSourceDefect T u.snd = y 0 := by
      have hf := congrArg (fun x : HilbertModuleSum B E F => x.snd) hu
      simpa only [J, contractiveJuliaEquiv_apply, sumMk_snd] using hf
    refine ⟨u.fst, countableModuleCons u.snd h', ?_⟩
    intro n
    cases n with
    | zero => simpa only [juliaOutput, juliaResidual_zero, countableModuleCons_zero] using hOutput
    | succ n => rw [juliaOutput_cons_shift T u.fst e' u.snd h' hFirst, hh']

theorem juliaCountableSynthesisCLM_finite_preimage (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (y : CountableModuleVectors F) :
    ∃ x : HilbertModuleSum B E (CountableHilbertModuleSum B F),
      juliaCountableSynthesisCLM T hT hDense x = countableModuleMk (B := B) y := by
  have hy : ∀ n ≥ y.support.sup Nat.succ, y n = 0 := by
    intro n hn
    apply Finsupp.notMem_support_iff.mp
    intro hs
    have hh : n + 1 ≤ y.support.sup Nat.succ := Finset.le_sup (f := Nat.succ) hs
    omega
  obtain ⟨e, h, hh⟩ := juliaOutput_finite_preimage T hT (y.support.sup Nat.succ) y hy
  refine ⟨sumMk e (countableModuleMk (B := B) h), ?_⟩
  rw [juliaCountableSynthesisCLM_finite]
  apply countableModule_ext_eval
  intro n
  rw [juliaFiniteSynthesis_evaluation, countableModuleEvaluation_mk, hh]

/-- The completed synthesis is onto: its isometric range is closed and contains
every finite vector, whose range is genuinely dense. -/
theorem juliaCountableSynthesisCLM_surjective (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) : Function.Surjective (juliaCountableSynthesisCLM T hT hDense) := by
  have hi : Isometry (juliaCountableSynthesisCLM T hT hDense) :=
    AddMonoidHomClass.isometry_of_norm _ (juliaCountableSynthesisCLM_norm T hT hDense)
  have hc : IsClosed (Set.range (juliaCountableSynthesisCLM T hT hDense)) :=
    hi.isClosedEmbedding.isClosed_range
  have hd : Dense (Set.range (juliaCountableSynthesisCLM T hT hDense)) :=
    (countableModuleMk_denseRange (B := B) (E := F)).mono (by
      rintro y ⟨v, rfl⟩
      exact juliaCountableSynthesisCLM_finite_preimage T hT hDense v)
  have hu : Set.range (juliaCountableSynthesisCLM T hT hDense) = Set.univ := by
    rw [← hc.closure_eq]
    exact hd.closure_eq
  exact Set.range_eq_univ.mp hu

/-- The actual countable Julia unitary E ⊕ F^∞ ≅ F^∞. -/
def countableJuliaEquiv (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) (hDense : DenseRange T) :
    HilbertModuleEquiv B (HilbertModuleSum B E (CountableHilbertModuleSum B F))
      (CountableHilbertModuleSum B F) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective
    { toLinearMap := (juliaCountableSynthesisCLM T hT hDense).toLinearMap
      norm_map' := juliaCountableSynthesisCLM_norm T hT hDense }
    (juliaCountableSynthesisCLM_surjective T hT hDense)
  inner_map := juliaCountableSynthesisCLM_inner T hT hDense

end BC4lean.KKTheory
