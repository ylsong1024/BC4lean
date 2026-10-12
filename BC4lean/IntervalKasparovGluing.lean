import BC4lean.IntervalModuleFibreNorm
import BC4lean.HilbertModuleCountableGenerationSeparable
import BC4lean.IntervalCoefficientGluing
import Mathlib.Topology.Algebra.Module.Basic

/-! # Matched-pair foundations for interval-module gluing

The underlying space for joining two arbitrary interval Hilbert modules is
their closed endpoint-matching subspace, with its actual product maximum norm.
Continuous coefficient functions are joined by the ordinary path concatenation.
The piecewise form gives an actual Hilbert module with the maximum norm,
and its half-interval fibres recover the original completed evaluated fibres.
Compatible adjointable maps restrict diagonally. Countable generation is proved
in the source's separable-coefficient setting. The compact pullback and the full
cycle gluing construction are supplied in separate modules.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {M N : Type*}
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, B)ᵐᵒᵖ M] [CStarModule C(unitInterval, B)ᵐᵒᵖ M]
  [NormedAddCommGroup N] [NormedSpace ℂ N]
  [SMul C(unitInterval, B)ᵐᵒᵖ N] [CStarModule C(unitInterval, B)ᵐᵒᵖ N]

/-- The continuous boundary mismatch on the actual product Banach space. -/
def intervalBoundaryMismatch
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    M × N →L[ℂ] HilbertModuleFibre B N (0 : unitInterval) :=
  (U.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((hilbertModuleFibreMk (B := B) (M := M) (1 : unitInterval)).comp
      (ContinuousLinearMap.fst ℂ M N))) -
    (hilbertModuleFibreMk (B := B) (M := N) (0 : unitInterval)).comp
      (ContinuousLinearMap.snd ℂ M N)

/-- Matched vectors are the genuine kernel of the continuous boundary mismatch. -/
def intervalMatchedSubmodule
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) : Submodule ℂ (M × N) :=
  (intervalBoundaryMismatch U).ker

@[simp] theorem mem_intervalMatchedSubmodule
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (z : M × N) :
    z ∈ intervalMatchedSubmodule U ↔
      U (hilbertModuleFibreMk (B := B) (1 : unitInterval) z.1) =
        hilbertModuleFibreMk (B := B) (0 : unitInterval) z.2 := by
  change U (hilbertModuleFibreMk (B := B) (1 : unitInterval) z.1) -
    hilbertModuleFibreMk (B := B) (0 : unitInterval) z.2 = 0 ↔ _
  exact sub_eq_zero

/-- The matching space is closed for the actual product maximum norm. -/
theorem intervalMatchedSubmodule_isClosed
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    IsClosed (intervalMatchedSubmodule U : Set (M × N)) :=
  (intervalBoundaryMismatch U).isClosed_ker

/-- The actual carrier of the interval gluing construction. -/
abbrev IntervalMatchedModule
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) := intervalMatchedSubmodule U

instance intervalMatchedModule_completeSpace [CompleteSpace M] [CompleteSpace N]
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    CompleteSpace (IntervalMatchedModule U) :=
  (intervalMatchedSubmodule_isClosed U).completeSpace_coe

/-- The inherited norm is exactly the maximum of the two vector norms. -/
@[simp] theorem intervalMatchedModule_norm
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (z : IntervalMatchedModule U) :
    ‖z‖ = max ‖z.val.1‖ ‖z.val.2‖ := rfl

/-- The first projection is surjective: the actual second endpoint quotient
supplies a vector with the required boundary value. -/
theorem intervalMatchedModule_fst_surjective [CompleteSpace N]
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    Function.Surjective (fun z : IntervalMatchedModule U => z.val.1) := by
  intro x
  obtain ⟨y, hy⟩ := hilbertModuleFibreMk_surjective (B := B) (M := N)
    (0 : unitInterval) (U (hilbertModuleFibreMk (B := B) (1 : unitInterval) x))
  exact ⟨⟨(x, y), (mem_intervalMatchedSubmodule U (x, y)).mpr hy.symm⟩, rfl⟩

/-- The second projection is surjective: the inverse boundary unitary and
the actual first endpoint quotient supply its matched partner. -/
theorem intervalMatchedModule_snd_surjective [CompleteSpace M]
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    Function.Surjective (fun z : IntervalMatchedModule U => z.val.2) := by
  intro y
  obtain ⟨x, hx⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M)
    (1 : unitInterval) (U.symm (hilbertModuleFibreMk (B := B) (0 : unitInterval) y))
  refine ⟨⟨(x, y), (mem_intervalMatchedSubmodule U (x, y)).mpr ?_⟩, rfl⟩
  rw [hx, U.apply_symm_apply]

/-- Matching vectors have matching coefficient-valued inner products at the
seam because the actual boundary unitary preserves the fibre inner product. -/
theorem intervalMatchedModule_inner_endpoint
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x y : IntervalMatchedModule U) :
    MulOpposite.unop ⟪x.val.1, y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) 1 =
      MulOpposite.unop ⟪x.val.2, y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) 0 := by
  have hx := (mem_intervalMatchedSubmodule U x.val).mp x.property
  have hy := (mem_intervalMatchedSubmodule U y.val).mp y.property
  have hinner := U.inner_map
    (hilbertModuleFibreMk (B := B) (1 : unitInterval) x.val.1)
    (hilbertModuleFibreMk (B := B) (1 : unitInterval) y.val.1)
  rw [hx, hy, hilbertModuleFibre_inner_mk, hilbertModuleFibre_inner_mk] at hinner
  exact congrArg MulOpposite.unop hinner.symm

/-- The actual piecewise coefficient-valued inner product of matched pairs. -/
def intervalMatchedInner
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x y : IntervalMatchedModule U) :
    C(unitInterval, B)ᵐᵒᵖ :=
  MulOpposite.op (intervalCoefficientJoin
    (MulOpposite.unop ⟪x.val.1, y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ))
    (MulOpposite.unop ⟪x.val.2, y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ))
    (intervalMatchedModule_inner_endpoint U x y))

@[simp] theorem intervalMatchedInner_leftHalf
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x y : IntervalMatchedModule U)
    (t : unitInterval) :
    MulOpposite.unop (intervalMatchedInner U x y) (intervalLeftHalf t) =
      MulOpposite.unop ⟪x.val.1, y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) t :=
  intervalCoefficientJoin_leftHalf _ _ (intervalMatchedModule_inner_endpoint U x y) t

@[simp] theorem intervalMatchedInner_rightHalf
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x y : IntervalMatchedModule U)
    (t : unitInterval) :
    MulOpposite.unop (intervalMatchedInner U x y) (intervalRightHalf t) =
      MulOpposite.unop ⟪x.val.2, y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) t :=
  intervalCoefficientJoin_rightHalf _ _ (intervalMatchedModule_inner_endpoint U x y) t

/-- Restriction of a coefficient to the first half, with the correct opposite. -/
def intervalLeftCoefficient (a : C(unitInterval, B)ᵐᵒᵖ) : C(unitInterval, B)ᵐᵒᵖ :=
  MulOpposite.op ((MulOpposite.unop a).comp intervalLeftHalf)

/-- Restriction of a coefficient to the second half, with the correct opposite. -/
def intervalRightCoefficient (a : C(unitInterval, B)ᵐᵒᵖ) : C(unitInterval, B)ᵐᵒᵖ :=
  MulOpposite.op ((MulOpposite.unop a).comp intervalRightHalf)

omit [PartialOrder B] [StarOrderedRing B] in
theorem intervalHalfCoefficient_endpoint (a : C(unitInterval, B)ᵐᵒᵖ) :
    MulOpposite.unop (intervalLeftCoefficient a) 1 =
      MulOpposite.unop (intervalRightCoefficient a) 0 := by
  change MulOpposite.unop a (intervalLeftHalf 1) =
    MulOpposite.unop a (intervalRightHalf 0)
  congr 1
  apply Subtype.ext
  norm_num [intervalLeftHalf, intervalRightHalf]

/-- The coefficient action uses the two half-interval restrictions and
preserves matching by the genuine coefficient compatibility of the fibre maps. -/
instance intervalMatchedModule_smul
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    SMul C(unitInterval, B)ᵐᵒᵖ (IntervalMatchedModule U) where
  smul a z := ⟨(intervalLeftCoefficient a • z.val.1,
    intervalRightCoefficient a • z.val.2), by
      apply (mem_intervalMatchedSubmodule U _).mpr
      rw [hilbertModuleFibreMk_op_smul, hilbertModuleFibreMk_op_smul,
        U.map_op_smul, (mem_intervalMatchedSubmodule U z.val).mp z.property,
        intervalHalfCoefficient_endpoint]⟩

/-- The joined coefficient inner product has the actual maximum diagonal norm. -/
theorem intervalMatchedInner_norm_self
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x : IntervalMatchedModule U) :
    ‖intervalMatchedInner U x x‖ = max
      ‖⟪x.val.1, x.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ)‖
      ‖⟪x.val.2, x.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ)‖ :=
  intervalCoefficientJoin_norm _ _ (intervalMatchedModule_inner_endpoint U x x)

/-- The inherited product norm is the norm induced by the actual joined form. -/
theorem intervalMatchedModule_norm_eq_sqrt_inner
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x : IntervalMatchedModule U) :
    ‖x‖ = Real.sqrt ‖intervalMatchedInner U x x‖ := by
  rw [intervalMatchedModule_norm, intervalMatchedInner_norm_self]
  rcases le_total ‖x.val.1‖ ‖x.val.2‖ with h | h
  · rw [max_eq_right h]
    have hinner : ‖⟪x.val.1, x.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ)‖ ≤
        ‖⟪x.val.2, x.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ)‖ := by
      rw [← CStarModule.norm_sq_eq (C(unitInterval, B)ᵐᵒᵖ),
        ← CStarModule.norm_sq_eq (C(unitInterval, B)ᵐᵒᵖ)]
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [max_eq_right hinner]
    exact CStarModule.norm_eq_sqrt_norm_inner_self _
  · rw [max_eq_left h]
    have hinner : ‖⟪x.val.2, x.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ)‖ ≤
        ‖⟪x.val.1, x.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ)‖ := by
      rw [← CStarModule.norm_sq_eq (C(unitInterval, B)ᵐᵒᵖ),
        ← CStarModule.norm_sq_eq (C(unitInterval, B)ᵐᵒᵖ)]
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [max_eq_left hinner]
    exact CStarModule.norm_eq_sqrt_norm_inner_self _

/-- The closed matched-pair space with its piecewise form is an actual Hilbert
continuous-coefficient module, with its inherited maximum norm. -/
instance intervalMatchedModule_cstarModule
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    CStarModule C(unitInterval, B)ᵐᵒᵖ (IntervalMatchedModule U) where
  inner := intervalMatchedInner U
  inner_add_right := by
    intro x y z
    apply MulOpposite.unop_injective
    apply continuousIntervalHalves_ext
    · intro t
      simp only [intervalMatchedInner_leftHalf, MulOpposite.unop_add, ContinuousMap.add_apply]
      change MulOpposite.unop
        ⟪x.val.1, y.val.1 + z.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) t = _
      rw [CStarModule.inner_add_right]
      rfl
    · intro t
      simp only [intervalMatchedInner_rightHalf, MulOpposite.unop_add, ContinuousMap.add_apply]
      change MulOpposite.unop
        ⟪x.val.2, y.val.2 + z.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) t = _
      rw [CStarModule.inner_add_right]
      rfl
  inner_self_nonneg := by
    intro x
    change ∀ t, 0 ≤ intervalCoefficientJoin
      (MulOpposite.unop ⟪x.val.1, x.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ))
      (MulOpposite.unop ⟪x.val.2, x.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ))
      (intervalMatchedModule_inner_endpoint U x x) t
    intro t
    rw [intervalCoefficientJoin_apply]
    split_ifs
    · have h := CStarModule.inner_self_nonneg
        (A := C(unitInterval, B)ᵐᵒᵖ) (x := x.val.1)
      change ∀ s, 0 ≤ MulOpposite.unop
        ⟪x.val.1, x.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) s at h
      exact h _
    · have h := CStarModule.inner_self_nonneg
        (A := C(unitInterval, B)ᵐᵒᵖ) (x := x.val.2)
      change ∀ s, 0 ≤ MulOpposite.unop
        ⟪x.val.2, x.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) s at h
      exact h _
  inner_self := by
    intro x
    constructor
    · intro hx
      have hn := intervalMatchedModule_norm_eq_sqrt_inner U x
      rw [hx, norm_zero, Real.sqrt_zero] at hn
      exact norm_eq_zero.mp hn
    · rintro rfl
      apply MulOpposite.unop_injective
      apply continuousIntervalHalves_ext <;> intro t
      · simp only [intervalMatchedInner_leftHalf]
        change MulOpposite.unop
          ⟪(0 : M), (0 : M)⟫_(C(unitInterval, B)ᵐᵒᵖ) t = 0
        simp
      · simp only [intervalMatchedInner_rightHalf]
        change MulOpposite.unop
          ⟪(0 : N), (0 : N)⟫_(C(unitInterval, B)ᵐᵒᵖ) t = 0
        simp
  inner_op_smul_right := by
    intro a x y
    apply MulOpposite.unop_injective
    apply continuousIntervalHalves_ext
    · intro t
      simp only [intervalMatchedInner_leftHalf, MulOpposite.unop_mul,
        ContinuousMap.mul_apply]
      change MulOpposite.unop
        ⟪x.val.1, intervalLeftCoefficient a • y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) t = _
      rw [CStarModule.inner_op_smul_right]
      rfl
    · intro t
      simp only [intervalMatchedInner_rightHalf, MulOpposite.unop_mul,
        ContinuousMap.mul_apply]
      change MulOpposite.unop
        ⟪x.val.2, intervalRightCoefficient a • y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) t = _
      rw [CStarModule.inner_op_smul_right]
      rfl
  inner_smul_right_complex := by
    intro c x y
    apply MulOpposite.unop_injective
    apply continuousIntervalHalves_ext
    · intro t
      simp only [intervalMatchedInner_leftHalf, MulOpposite.unop_smul,
        ContinuousMap.smul_apply]
      change MulOpposite.unop
        ⟪x.val.1, c • y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) t = _
      rw [CStarModule.inner_smul_right_complex]
      rfl
    · intro t
      simp only [intervalMatchedInner_rightHalf, MulOpposite.unop_smul,
        ContinuousMap.smul_apply]
      change MulOpposite.unop
        ⟪x.val.2, c • y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) t = _
      rw [CStarModule.inner_smul_right_complex]
      rfl
  star_inner := by
    intro x y
    apply MulOpposite.unop_injective
    apply continuousIntervalHalves_ext
    · intro t
      simp only [MulOpposite.unop_star, ContinuousMap.star_apply,
        intervalMatchedInner_leftHalf]
      rw [← ContinuousMap.star_apply, ← MulOpposite.unop_star, CStarModule.star_inner]
    · intro t
      simp only [MulOpposite.unop_star, ContinuousMap.star_apply,
        intervalMatchedInner_rightHalf]
      rw [← ContinuousMap.star_apply, ← MulOpposite.unop_star, CStarModule.star_inner]
  norm_eq_sqrt_norm_inner_self := intervalMatchedModule_norm_eq_sqrt_inner U

@[simp] theorem intervalMatchedModule_inner_leftHalf
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x y : IntervalMatchedModule U)
    (t : unitInterval) :
    MulOpposite.unop ⟪x, y⟫_(C(unitInterval, B)ᵐᵒᵖ) (intervalLeftHalf t) =
      MulOpposite.unop ⟪x.val.1, y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) t :=
  intervalMatchedInner_leftHalf U x y t

@[simp] theorem intervalMatchedModule_inner_rightHalf
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (x y : IntervalMatchedModule U)
    (t : unitInterval) :
    MulOpposite.unop ⟪x, y⟫_(C(unitInterval, B)ᵐᵒᵖ) (intervalRightHalf t) =
      MulOpposite.unop ⟪x.val.2, y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) t :=
  intervalMatchedInner_rightHalf U x y t

variable [CompleteSpace M] [CompleteSpace N]

/-- Compatibility of the two actual endpoint operators through the boundary
unitary. This is an exact intertwining identity on the completed fibres. -/
def IntervalMatchedOperatorCompatible
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N) : Prop :=
  ∀ z, U (hilbertModuleFibreOperator (B := B) (1 : unitInterval) T z) =
    hilbertModuleFibreOperator (B := B) (0 : unitInterval) S (U z)

/-- Exact boundary compatibility implies the same compatibility for adjoints,
by conjugation through the actual boundary Hilbert-module unitary. -/
theorem IntervalMatchedOperatorCompatible.adjoint
    {U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))}
    {T : AdjointableMap C(unitInterval, B) M M}
    {S : AdjointableMap C(unitInterval, B) N N}
    (h : IntervalMatchedOperatorCompatible U T S) :
    IntervalMatchedOperatorCompatible U T.adjoint S.adjoint := by
  have heq : U.transport (hilbertModuleFibreOperator (B := B) (1 : unitInterval) T) =
      hilbertModuleFibreOperator (B := B) (0 : unitInterval) S := by
    ext z
    rw [HilbertModuleEquiv.transport_apply, h, U.apply_symm_apply]
  have hstar := congrArg star heq
  rw [← HilbertModuleEquiv.transport_star, ← hilbertModuleFibreOperator_star,
    ← hilbertModuleFibreOperator_star] at hstar
  intro z
  have hpoint := congrArg (fun R => R (U z)) hstar
  simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply,
    AdjointableMap.star_eq_adjoint]
    using hpoint

/-- A compatible diagonal pair preserves the actual closed matching space. -/
theorem IntervalMatchedOperatorCompatible.mapsTo
    {U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))}
    {T : AdjointableMap C(unitInterval, B) M M}
    {S : AdjointableMap C(unitInterval, B) N N}
    (h : IntervalMatchedOperatorCompatible U T S) :
    ∀ z ∈ intervalMatchedSubmodule U,
      (T.toCLM.prodMap S.toCLM) z ∈ intervalMatchedSubmodule U := by
  intro z hz
  apply (mem_intervalMatchedSubmodule U _).mpr
  change U (hilbertModuleFibreMk (B := B) (1 : unitInterval) (T z.1)) =
    hilbertModuleFibreMk (B := B) (0 : unitInterval) (S z.2)
  rw [← hilbertModuleFibreOperator_mk, h,
    (mem_intervalMatchedSubmodule U z).mp hz, hilbertModuleFibreOperator_mk]

theorem IntervalMatchedOperatorCompatible.zero
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    IntervalMatchedOperatorCompatible U 0 0 := by
  intro z
  simp only [hilbertModuleFibreOperator_zero, AdjointableMap.coe_zero_apply, U.map_zero]

theorem IntervalMatchedOperatorCompatible.one
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    IntervalMatchedOperatorCompatible U 1 1 := by
  intro z
  simp only [hilbertModuleFibreOperator_one, AdjointableMap.one_apply]

theorem IntervalMatchedOperatorCompatible.add
    {U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))}
    {T V : AdjointableMap C(unitInterval, B) M M}
    {S W : AdjointableMap C(unitInterval, B) N N}
    (h : IntervalMatchedOperatorCompatible U T S)
    (k : IntervalMatchedOperatorCompatible U V W) :
    IntervalMatchedOperatorCompatible U (T + V) (S + W) := by
  intro z
  simp only [hilbertModuleFibreOperator_add, AdjointableMap.coe_add_apply, U.map_add]
  rw [h z, k z]

theorem IntervalMatchedOperatorCompatible.sub
    {U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))}
    {T V : AdjointableMap C(unitInterval, B) M M}
    {S W : AdjointableMap C(unitInterval, B) N N}
    (h : IntervalMatchedOperatorCompatible U T S)
    (k : IntervalMatchedOperatorCompatible U V W) :
    IntervalMatchedOperatorCompatible U (T - V) (S - W) := by
  intro z
  simp only [hilbertModuleFibreOperator_sub, AdjointableMap.coe_sub_apply, U.map_sub]
  rw [h z, k z]

theorem IntervalMatchedOperatorCompatible.mul
    {U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))}
    {T V : AdjointableMap C(unitInterval, B) M M}
    {S W : AdjointableMap C(unitInterval, B) N N}
    (h : IntervalMatchedOperatorCompatible U T S)
    (k : IntervalMatchedOperatorCompatible U V W) :
    IntervalMatchedOperatorCompatible U (T * V) (S * W) := by
  intro z
  simp only [hilbertModuleFibreOperator_mul, AdjointableMap.mul_apply]
  rw [h _, k z]

theorem IntervalMatchedOperatorCompatible.smul
    {U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))}
    {T : AdjointableMap C(unitInterval, B) M M}
    {S : AdjointableMap C(unitInterval, B) N N}
    (h : IntervalMatchedOperatorCompatible U T S) (a : ℂ) :
    IntervalMatchedOperatorCompatible U (a • T) (a • S) := by
  intro z
  simp only [hilbertModuleFibreOperator_smul, AdjointableMap.coe_smul_apply, U.map_smul]
  rw [h z]

/-- The actual restriction of a compatible diagonal adjoint pair, whose
adjoint is the restriction of the actual component adjoints. -/
def intervalMatchedOperator
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N)
    (h : IntervalMatchedOperatorCompatible U T S) :
    AdjointableMap C(unitInterval, B) (IntervalMatchedModule U) (IntervalMatchedModule U) where
  toCLM := (T.toCLM.prodMap S.toCLM).restrict h.mapsTo
  adjointCLM := (T.adjointCLM.prodMap S.adjointCLM).restrict h.adjoint.mapsTo
  adjoint_identity x y := by
    apply MulOpposite.unop_injective
    apply continuousIntervalHalves_ext
    · intro t
      rw [intervalMatchedModule_inner_leftHalf, intervalMatchedModule_inner_leftHalf]
      change MulOpposite.unop
        ⟪T x.val.1, y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) t =
        MulOpposite.unop ⟪x.val.1, T.adjoint y.val.1⟫_(C(unitInterval, B)ᵐᵒᵖ) t
      exact congrArg (fun a : C(unitInterval, B)ᵐᵒᵖ => MulOpposite.unop a t)
        (T.adjoint_identity _ _)
    · intro t
      rw [intervalMatchedModule_inner_rightHalf, intervalMatchedModule_inner_rightHalf]
      change MulOpposite.unop
        ⟪S x.val.2, y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) t =
        MulOpposite.unop ⟪x.val.2, S.adjoint y.val.2⟫_(C(unitInterval, B)ᵐᵒᵖ) t
      exact congrArg (fun a : C(unitInterval, B)ᵐᵒᵖ => MulOpposite.unop a t)
        (S.adjoint_identity _ _)

@[simp] theorem intervalMatchedOperator_fst
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N)
    (h : IntervalMatchedOperatorCompatible U T S) (x : IntervalMatchedModule U) :
    (intervalMatchedOperator U T S h x).val.1 = T x.val.1 := rfl

@[simp] theorem intervalMatchedOperator_snd
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N)
    (h : IntervalMatchedOperatorCompatible U T S) (x : IntervalMatchedModule U) :
    (intervalMatchedOperator U T S h x).val.2 = S x.val.2 := rfl

/-- The component adjoints agree exactly with the actual glued adjoint. -/
@[simp] theorem intervalMatchedOperator_adjoint
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N)
    (h : IntervalMatchedOperatorCompatible U T S) :
    (intervalMatchedOperator U T S h).adjoint =
      intervalMatchedOperator U T.adjoint S.adjoint h.adjoint := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem intervalMatchedOperator_zero
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    intervalMatchedOperator U 0 0 (IntervalMatchedOperatorCompatible.zero U) = 0 := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem intervalMatchedOperator_one
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) :
    intervalMatchedOperator U 1 1 (IntervalMatchedOperatorCompatible.one U) = 1 := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem intervalMatchedOperator_add
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T V : AdjointableMap C(unitInterval, B) M M)
    (S W : AdjointableMap C(unitInterval, B) N N) (h k) :
    intervalMatchedOperator U (T + V) (S + W) (h.add k) =
      intervalMatchedOperator U T S h + intervalMatchedOperator U V W k := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem intervalMatchedOperator_sub
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T V : AdjointableMap C(unitInterval, B) M M)
    (S W : AdjointableMap C(unitInterval, B) N N) (h k) :
    intervalMatchedOperator U (T - V) (S - W) (h.sub k) =
      intervalMatchedOperator U T S h - intervalMatchedOperator U V W k := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem intervalMatchedOperator_mul
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T V : AdjointableMap C(unitInterval, B) M M)
    (S W : AdjointableMap C(unitInterval, B) N N) (h k) :
    intervalMatchedOperator U (T * V) (S * W) (h.mul k) =
      intervalMatchedOperator U T S h * intervalMatchedOperator U V W k := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem intervalMatchedOperator_smul
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N) (h) (a : ℂ) :
    intervalMatchedOperator U (a • T) (a • S) (h.smul a) =
      a • intervalMatchedOperator U T S h := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- In the source's separable-coefficient setting, countable generation of
both original modules proves separability of their product, hence of the
actual closed matching space; the genuine coefficient approximate unit then
proves countable generation of that matching Hilbert module. -/
theorem intervalMatchedModule_countablyGenerated
    [TopologicalSpace.SeparableSpace B]
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (hM : IsCountablyGeneratedModule C(unitInterval, B) M)
    (hN : IsCountablyGeneratedModule C(unitInterval, B) N) :
    IsCountablyGeneratedModule C(unitInterval, B) (IntervalMatchedModule U) := by
  have : TopologicalSpace.SeparableSpace M := hM.separableSpace
  have : TopologicalSpace.SeparableSpace N := hN.separableSpace
  exact isCountablyGeneratedModule_of_separableSpace

/-- The continuous first coordinate projection on the actual matching space. -/
def intervalMatchedFirstProjection
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) : IntervalMatchedModule U →L[ℂ] M :=
  (ContinuousLinearMap.fst ℂ M N).comp (intervalMatchedSubmodule U).subtypeL

/-- The continuous second coordinate projection on the actual matching space. -/
def intervalMatchedSecondProjection
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) : IntervalMatchedModule U →L[ℂ] N :=
  (ContinuousLinearMap.snd ℂ M N).comp (intervalMatchedSubmodule U).subtypeL

/-- The joined module's first-half evaluated fibre is unitarily the original
first module's fibre. Both evaluation and matched projection surjectivity are
proved on the actual arbitrary continuous-coefficient modules. -/
def intervalMatchedLeftFibreEquiv
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (t : unitInterval) :
    HilbertModuleEquiv B
      (HilbertModuleFibre B (IntervalMatchedModule U) (intervalLeftHalf t))
      (HilbertModuleFibre B M t) :=
  hilbertModuleFibreEquivOfEvaluation (intervalLeftHalf t)
    ((hilbertModuleFibreMk (B := B) (M := M) t).comp (intervalMatchedFirstProjection U))
    (fun x y => by
      change ⟪hilbertModuleFibreMk (B := B) t x.val.1,
        hilbertModuleFibreMk (B := B) t y.val.1⟫_(Bᵐᵒᵖ) = _
      rw [hilbertModuleFibre_inner_mk, intervalMatchedModule_inner_leftHalf])
    ((hilbertModuleFibreMk_surjective (B := B) (M := M) t).comp
      (intervalMatchedModule_fst_surjective U))

/-- The joined module's second-half evaluated fibre is unitarily the original
second module's fibre through the actual second coordinate evaluation. -/
def intervalMatchedRightFibreEquiv
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (t : unitInterval) :
    HilbertModuleEquiv B
      (HilbertModuleFibre B (IntervalMatchedModule U) (intervalRightHalf t))
      (HilbertModuleFibre B N t) :=
  hilbertModuleFibreEquivOfEvaluation (intervalRightHalf t)
    ((hilbertModuleFibreMk (B := B) (M := N) t).comp (intervalMatchedSecondProjection U))
    (fun x y => by
      change ⟪hilbertModuleFibreMk (B := B) t x.val.2,
        hilbertModuleFibreMk (B := B) t y.val.2⟫_(Bᵐᵒᵖ) = _
      rw [hilbertModuleFibre_inner_mk, intervalMatchedModule_inner_rightHalf])
    ((hilbertModuleFibreMk_surjective (B := B) (M := N) t).comp
      (intervalMatchedModule_snd_surjective U))

@[simp] theorem intervalMatchedLeftFibreEquiv_mk
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (t : unitInterval)
    (x : IntervalMatchedModule U) :
    intervalMatchedLeftFibreEquiv U t
      (hilbertModuleFibreMk (B := B) (intervalLeftHalf t) x) =
      hilbertModuleFibreMk (B := B) t x.val.1 :=
  hilbertModuleFibreEquivOfEvaluation_mk (intervalLeftHalf t) _ _ _ x

@[simp] theorem intervalMatchedRightFibreEquiv_mk
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (t : unitInterval)
    (x : IntervalMatchedModule U) :
    intervalMatchedRightFibreEquiv U t
      (hilbertModuleFibreMk (B := B) (intervalRightHalf t) x) =
      hilbertModuleFibreMk (B := B) t x.val.2 :=
  hilbertModuleFibreEquivOfEvaluation_mk (intervalRightHalf t) _ _ _ x

/-- Every glued adjointable operator is identified on each first-half fibre
with the first original operator, through the actual fibre unitary. -/
theorem intervalMatchedLeftFibreEquiv_operator
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (t : unitInterval)
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N)
    (h : IntervalMatchedOperatorCompatible U T S)
    (z : HilbertModuleFibre B (IntervalMatchedModule U) (intervalLeftHalf t)) :
    intervalMatchedLeftFibreEquiv U t
      (hilbertModuleFibreOperator (intervalLeftHalf t) (intervalMatchedOperator U T S h) z) =
      hilbertModuleFibreOperator t T (intervalMatchedLeftFibreEquiv U t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
    (B := B) (M := IntervalMatchedModule U) (intervalLeftHalf t) z
  rw [hilbertModuleFibreOperator_mk, intervalMatchedLeftFibreEquiv_mk,
    intervalMatchedOperator_fst, intervalMatchedLeftFibreEquiv_mk,
    hilbertModuleFibreOperator_mk]

/-- The analogous identification of every second-half operator fibre. -/
theorem intervalMatchedRightFibreEquiv_operator
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))) (t : unitInterval)
    (T : AdjointableMap C(unitInterval, B) M M)
    (S : AdjointableMap C(unitInterval, B) N N)
    (h : IntervalMatchedOperatorCompatible U T S)
    (z : HilbertModuleFibre B (IntervalMatchedModule U) (intervalRightHalf t)) :
    intervalMatchedRightFibreEquiv U t
      (hilbertModuleFibreOperator (intervalRightHalf t) (intervalMatchedOperator U T S h) z) =
      hilbertModuleFibreOperator t S (intervalMatchedRightFibreEquiv U t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
    (B := B) (M := IntervalMatchedModule U) (intervalRightHalf t) z
  rw [hilbertModuleFibreOperator_mk, intervalMatchedRightFibreEquiv_mk,
    intervalMatchedOperator_snd, intervalMatchedRightFibreEquiv_mk,
    hilbertModuleFibreOperator_mk]

omit [CompleteSpace M] [CompleteSpace N] in
@[ext] theorem intervalMatchedModule_ext
    {U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval))}
    {x y : IntervalMatchedModule U} (hfirst : x.val.1 = y.val.1)
    (hsecond : x.val.2 = y.val.2) : x = y :=
  Subtype.ext (Prod.ext hfirst hsecond)

/-- A pair of actual complex-linear isometries preserving matching restricts
to an actual linear isometry of the matching space. -/
def intervalMatchedLinearIsometry
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (e : M →ₗᵢ[ℂ] M) (f : N →ₗᵢ[ℂ] N)
    (h : ∀ z ∈ intervalMatchedSubmodule U,
      (e z.1, f z.2) ∈ intervalMatchedSubmodule U) :
    IntervalMatchedModule U →ₗᵢ[ℂ] IntervalMatchedModule U where
  toFun z := ⟨(e z.val.1, f z.val.2), h z.val z.property⟩
  map_add' x y := by
    apply intervalMatchedModule_ext <;> exact map_add _ _ _
  map_smul' c x := by
    apply intervalMatchedModule_ext <;> exact map_smul _ _ _
  norm_map' z := by
    change max ‖e z.val.1‖ ‖f z.val.2‖ = max ‖z.val.1‖ ‖z.val.2‖
    rw [e.norm_map, f.norm_map]

/-- If both the pair and its inverse preserve matching, they give a genuine
complex-linear isometry equivalence on the closed matching space. -/
def intervalMatchedLinearIsometryEquiv
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (e : M ≃ₗᵢ[ℂ] M) (f : N ≃ₗᵢ[ℂ] N)
    (h : ∀ z ∈ intervalMatchedSubmodule U,
      (e z.1, f z.2) ∈ intervalMatchedSubmodule U)
    (hi : ∀ z ∈ intervalMatchedSubmodule U,
      (e.symm z.1, f.symm z.2) ∈ intervalMatchedSubmodule U) :
    IntervalMatchedModule U ≃ₗᵢ[ℂ] IntervalMatchedModule U :=
  LinearIsometryEquiv.ofLinearIsometry
    (intervalMatchedLinearIsometry U e.toLinearIsometry f.toLinearIsometry h)
    (intervalMatchedLinearIsometry U e.symm.toLinearIsometry f.symm.toLinearIsometry hi).toLinearMap
    (by
      apply LinearMap.ext
      intro z
      apply intervalMatchedModule_ext <;> exact LinearIsometryEquiv.apply_symm_apply _ _)
    (by
      apply LinearMap.ext
      intro z
      apply intervalMatchedModule_ext <;> exact LinearIsometryEquiv.symm_apply_apply _ _)

omit [CompleteSpace M] [CompleteSpace N] in
@[simp] theorem intervalMatchedLinearIsometryEquiv_fst
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (e : M ≃ₗᵢ[ℂ] M) (f : N ≃ₗᵢ[ℂ] N) (h hi)
    (z : IntervalMatchedModule U) :
    (intervalMatchedLinearIsometryEquiv U e f h hi z).val.1 = e z.val.1 := rfl

omit [CompleteSpace M] [CompleteSpace N] in
@[simp] theorem intervalMatchedLinearIsometryEquiv_snd
    (U : HilbertModuleEquiv B (HilbertModuleFibre B M (1 : unitInterval))
      (HilbertModuleFibre B N (0 : unitInterval)))
    (e : M ≃ₗᵢ[ℂ] M) (f : N ≃ₗᵢ[ℂ] N) (h hi)
    (z : IntervalMatchedModule U) :
    (intervalMatchedLinearIsometryEquiv U e f h hi z).val.2 = f z.val.2 := rfl

end BC4lean.KKTheory
