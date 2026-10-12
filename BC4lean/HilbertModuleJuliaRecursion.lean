import BC4lean.HilbertModuleJuliaDecay
import BC4lean.CountableHilbertModuleSum

/-! # Actual Julia recurrence and coefficient telescoping

At each step the actual Julia unitary emits one vector of F and retains one
residual vector of E. The coefficient-valued inner products telescope exactly,
including mixed inner products of two different inputs. For finitely supported
input sequences, the residual eventually follows powers of D and tends to zero
by the proved strong Julia decay. These are the finite identities needed to
complete the countable isometry; the completed stabilization unitary remains a
separate construction.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

def juliaResidual (T : AdjointableMap B F E) (e : E) (h : ℕ → F) : ℕ → E
  | 0 => e
  | n + 1 => juliaTargetDefect T (juliaResidual T e h n) + T (h n)

omit [CompleteSpace F] in
@[simp] theorem juliaResidual_zero (T : AdjointableMap B F E) (e : E) (h : ℕ → F) :
    juliaResidual T e h 0 = e := rfl

omit [CompleteSpace F] in
@[simp] theorem juliaResidual_succ (T : AdjointableMap B F E) (e : E) (h : ℕ → F) (n : ℕ) :
    juliaResidual T e h (n + 1) = juliaTargetDefect T (juliaResidual T e h n) + T (h n) := rfl

def juliaOutput (T : AdjointableMap B F E) (e : E) (h : ℕ → F) (n : ℕ) : F :=
  -T.adjoint (juliaResidual T e h n) + juliaSourceDefect T (h n)

omit [CompleteSpace F] in
theorem juliaResidual_add (T : AdjointableMap B F E) (e e' : E) (h h' : ℕ → F) (n : ℕ) :
    juliaResidual T (e + e') (h + h') n = juliaResidual T e h n + juliaResidual T e' h' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [juliaResidual_succ, ih, Pi.add_apply, map_add]
    abel

omit [CompleteSpace F] in
theorem juliaResidual_smul (T : AdjointableMap B F E) (c : ℂ) (e : E) (h : ℕ → F) (n : ℕ) :
    juliaResidual T (c • e) (c • h) n = c • juliaResidual T e h n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [juliaResidual_succ, ih, Pi.smul_apply, map_smul, smul_add]

def juliaResidualLinear (T : AdjointableMap B F E) (n : ℕ) : (E × (ℕ → F)) →ₗ[ℂ] E where
  toFun p := juliaResidual T p.1 p.2 n
  map_add' p q := juliaResidual_add T p.1 q.1 p.2 q.2 n
  map_smul' c p := juliaResidual_smul T c p.1 p.2 n

def juliaOutputLinear (T : AdjointableMap B F E) (n : ℕ) : (E × (ℕ → F)) →ₗ[ℂ] F :=
  -T.adjoint.toCLM.toLinearMap.comp (juliaResidualLinear T n) +
    (juliaSourceDefect T).toCLM.toLinearMap.comp
      ((LinearMap.proj n).comp (LinearMap.snd ℂ E (ℕ → F)))

@[simp] theorem juliaOutputLinear_apply (T : AdjointableMap B F E) (n : ℕ) (p : E × (ℕ → F)) :
    juliaOutputLinear T n p = juliaOutput T p.1 p.2 n := rfl

/-- Every actual Julia step preserves mixed coefficient inner products. -/
theorem juliaResidual_output_inner_step (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (e e' : E) (h h' : ℕ → F) (n : ℕ) :
    ⟪juliaResidual T e h (n + 1), juliaResidual T e' h' (n + 1)⟫_(Bᵐᵒᵖ) +
      ⟪juliaOutput T e h n, juliaOutput T e' h' n⟫_(Bᵐᵒᵖ) =
      ⟪juliaResidual T e h n, juliaResidual T e' h' n⟫_(Bᵐᵒᵖ) + ⟪h n, h' n⟫_(Bᵐᵒᵖ) := by
  have hh := (contractiveJuliaEquiv T hT).inner_map
    (sumMk (juliaResidual T e h n) (h n)) (sumMk (juliaResidual T e' h' n) (h' n))
  simpa only [contractiveJuliaEquiv_apply, inner_sum, sumMk_fst, sumMk_snd,
    juliaResidual_succ, juliaOutput] using hh

/-- The emitted mixed coefficient squares telescope with the actual residual. -/
theorem juliaOutput_inner_telescope (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (e e' : E) (h h' : ℕ → F) (n : ℕ) :
    (∑ i ∈ Finset.range n, ⟪juliaOutput T e h i, juliaOutput T e' h' i⟫_(Bᵐᵒᵖ)) +
      ⟪juliaResidual T e h n, juliaResidual T e' h' n⟫_(Bᵐᵒᵖ) =
      ⟪e, e'⟫_(Bᵐᵒᵖ) + ∑ i ∈ Finset.range n, ⟪h i, h' i⟫_(Bᵐᵒᵖ) := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, juliaResidual_zero, zero_add, add_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hs := juliaResidual_output_inner_step T hT e e' h h' n
    calc
      _ = (∑ i ∈ Finset.range n, ⟪juliaOutput T e h i, juliaOutput T e' h' i⟫_(Bᵐᵒᵖ)) +
          (⟪juliaResidual T e h n, juliaResidual T e' h' n⟫_(Bᵐᵒᵖ) + ⟪h n, h' n⟫_(Bᵐᵒᵖ)) := by
        rw [← hs]
        abel
      _ = _ := by rw [← add_assoc, ih]; abel

omit [CompleteSpace F] in
theorem juliaResidual_after_input_tail (T : AdjointableMap B F E) (e : E) (h : ℕ → F)
    (N : ℕ) (hTail : ∀ n ≥ N, h n = 0) (k : ℕ) :
    juliaResidual T e h (N + k) = (juliaTargetDefect T ^ k) (juliaResidual T e h N) := by
  induction k with
  | zero => simp only [Nat.add_zero, pow_zero, AdjointableMap.one_apply]
  | succ k ih =>
    rw [Nat.add_succ, juliaResidual_succ, hTail (N + k) (Nat.le_add_right N k), map_zero, add_zero, ih,
      pow_succ', AdjointableMap.mul_apply]

omit [NormedSpace ℂ F] [CompleteSpace F] in
private theorem countableModuleVector_eventually_zero (h : CountableModuleVectors F) :
    ∃ N : ℕ, ∀ n ≥ N, h n = 0 := by
  refine ⟨h.support.sup Nat.succ, ?_⟩
  intro n hn
  apply Finsupp.notMem_support_iff.mp
  intro hs
  have hh : n + 1 ≤ h.support.sup Nat.succ := Finset.le_sup (f := Nat.succ) hs
  omega

/-- Finite inputs have actual strongly vanishing residuals. -/
theorem juliaResidual_finite_tendsto_zero (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (e : E) (h : CountableModuleVectors F) :
    Tendsto (juliaResidual T e h) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := countableModuleVector_eventually_zero h
  have ht : Tendsto (fun k : ℕ => juliaResidual T e h (N + k)) atTop (𝓝 0) := by
    simpa only [juliaResidual_after_input_tail T e h N hN] using
      juliaTargetDefect_power_tendsto_zero T hT hDense (juliaResidual T e h N)
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [Nat.add_comm] using ht

omit [StarOrderedRing B] [CompleteSpace F] in
/-- Finite input coefficient partial sums eventually equal the actual finite form. -/
theorem countableModuleFinite_partial_inner_tendsto (h h' : CountableModuleVectors F) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ⟪h i, h' i⟫_(Bᵐᵒᵖ)) atTop
      (𝓝 (countableModuleFiniteInner (B := B) h h')) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (h.support.sup Nat.succ)] with n hn
  apply countableModuleFiniteInner_eq_sum
  intro i hi
  apply Finset.mem_range.mpr
  have hh : i + 1 ≤ h.support.sup Nat.succ := Finset.le_sup (f := Nat.succ) hi
  omega

/-- The output mixed coefficient partial sums converge to the actual input form.
This is the coefficient convergence needed by the true countable sum. -/
theorem juliaOutput_finite_inner_tendsto (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (hDense : DenseRange T) (e e' : E) (h h' : CountableModuleVectors F) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      ⟪juliaOutput T e h i, juliaOutput T e' h' i⟫_(Bᵐᵒᵖ)) atTop
      (𝓝 (⟪e, e'⟫_(Bᵐᵒᵖ) + countableModuleFiniteInner (B := B) h h')) := by
  have hr := (CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := E)).tendsto ((0 : E), (0 : E)) |>.comp
    ((juliaResidual_finite_tendsto_zero T hT hDense e h).prodMk_nhds
      (juliaResidual_finite_tendsto_zero T hT hDense e' h'))
  simp only [Function.comp_def, CStarModule.inner_zero_left] at hr
  have ht := ((tendsto_const_nhds (x := ⟪e, e'⟫_(Bᵐᵒᵖ))).add (countableModuleFinite_partial_inner_tendsto h h')).sub hr
  simp only [sub_zero] at ht
  convert ht using 1
  ext n
  exact eq_sub_iff_add_eq.mpr (juliaOutput_inner_telescope T hT e e' h h' n)

end BC4lean.KKTheory
