import BC4lean.IntervalModuleFibre
import BC4lean.HilbertModuleSum
import BC4lean.HilbertModuleEquiv

/-! # Genuine fibres commute with finite Hilbert-module direct sums

Coordinate maps are bounded for the evaluated coefficient inner products.
They therefore descend to the positive-form radical quotients, where inclusion
and projection are actual adjoint pairs. Their completions split the completed
fibre of a direct sum into the Hilbert direct sum of the completed fibres.
The inverse identities are proved on the genuine dense canonical images.
The resulting equivalence preserves the coefficient-valued inner product and
intertwines diagonal fibre operators; no ambient quotient norm is used.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B X M N : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul C(X, B)ᵐᵒᵖ N] [CStarModule C(X, B)ᵐᵒᵖ N]

/-- Evaluation of the actual sum inner product is the sum of the evaluated forms. -/
theorem evaluatedModuleSum_inner (t : X)
    (x y : EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t) :
    ⟪x, y⟫_(Bᵐᵒᵖ) =
      ⟪evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t x).fst,
        evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t y).fst⟫_(Bᵐᵒᵖ) +
      ⟪evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t x).snd,
        evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t y).snd⟫_(Bᵐᵒᵖ) := by
  simp only [evaluatedModule_inner, evaluatedModule_to_of, inner_sum, MulOpposite.unop_add, ContinuousMap.add_apply,
    MulOpposite.op_add]

/-- The first coordinate as a map of the evaluated vector spaces. -/
def evaluatedModuleSumFstLinear (t : X) :
    EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t →ₗ[ℂ] EvaluatedModuleSpace B M t :=
  (evaluatedModuleLinearEquiv (B := B) (M := M) t).symm.toLinearMap.comp
    ((sumFstCLM (B := C(X, B)) (E := M) (F := N)).toLinearMap.comp
      (evaluatedModuleLinearEquiv t).toLinearMap)

/-- The second coordinate as a map of the evaluated vector spaces. -/
def evaluatedModuleSumSndLinear (t : X) :
    EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t →ₗ[ℂ] EvaluatedModuleSpace B N t :=
  (evaluatedModuleLinearEquiv (B := B) (M := N) t).symm.toLinearMap.comp
    ((sumSndCLM (B := C(X, B)) (E := M) (F := N)).toLinearMap.comp
      (evaluatedModuleLinearEquiv t).toLinearMap)

/-- First-coordinate inclusion before removing the evaluated radical. -/
def evaluatedModuleSumInlLinear (t : X) :
    EvaluatedModuleSpace B M t →ₗ[ℂ] EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t :=
  (evaluatedModuleLinearEquiv (B := B) (M := HilbertModuleSum C(X, B) M N) t).symm.toLinearMap.comp
    ((sumInlCLM (B := C(X, B)) (E := M) (F := N)).toLinearMap.comp
      (evaluatedModuleLinearEquiv t).toLinearMap)

/-- Second-coordinate inclusion before removing the evaluated radical. -/
def evaluatedModuleSumInrLinear (t : X) :
    EvaluatedModuleSpace B N t →ₗ[ℂ] EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t :=
  (evaluatedModuleLinearEquiv (B := B) (M := HilbertModuleSum C(X, B) M N) t).symm.toLinearMap.comp
    ((sumInrCLM (B := C(X, B)) (E := M) (F := N)).toLinearMap.comp
      (evaluatedModuleLinearEquiv t).toLinearMap)

theorem evaluatedModuleSumFst_formNorm_le (t : X)
    (x : EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t) :
    PositiveModuleForm.formNorm (B := B) (evaluatedModuleSumFstLinear t x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  change Real.sqrt ‖⟪evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t x).fst,
    evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t x).fst⟫_(Bᵐᵒᵖ)‖ ≤
    1 * Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖
  rw [one_mul, evaluatedModuleSum_inner]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le PositiveModuleForm.inner_self_nonneg
    (le_add_of_nonneg_right PositiveModuleForm.inner_self_nonneg)

theorem evaluatedModuleSumSnd_formNorm_le (t : X)
    (x : EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t) :
    PositiveModuleForm.formNorm (B := B) (evaluatedModuleSumSndLinear t x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  change Real.sqrt ‖⟪evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t x).snd,
    evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t x).snd⟫_(Bᵐᵒᵖ)‖ ≤
    1 * Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖
  rw [one_mul, evaluatedModuleSum_inner]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le PositiveModuleForm.inner_self_nonneg
    (le_add_of_nonneg_left PositiveModuleForm.inner_self_nonneg)

theorem evaluatedModuleSumInl_formNorm_eq (t : X) (x : EvaluatedModuleSpace B M t) :
    PositiveModuleForm.formNorm (B := B) (evaluatedModuleSumInlLinear (N := N) t x) =
      PositiveModuleForm.formNorm (B := B) x := by
  unfold PositiveModuleForm.formNorm
  rw [evaluatedModuleSum_inner]
  change Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ) + ⟪(0 : EvaluatedModuleSpace B N t), 0⟫_(Bᵐᵒᵖ)‖ = _
  rw [PositiveModuleForm.inner_zero_left, add_zero]

theorem evaluatedModuleSumInr_formNorm_eq (t : X) (x : EvaluatedModuleSpace B N t) :
    PositiveModuleForm.formNorm (B := B) (evaluatedModuleSumInrLinear (M := M) t x) =
      PositiveModuleForm.formNorm (B := B) x := by
  unfold PositiveModuleForm.formNorm
  rw [evaluatedModuleSum_inner]
  change Real.sqrt ‖⟪(0 : EvaluatedModuleSpace B M t), 0⟫_(Bᵐᵒᵖ) + ⟪x, x⟫_(Bᵐᵒᵖ)‖ = _
  rw [PositiveModuleForm.inner_zero_left, zero_add]

/-- Inclusion and projection are an actual adjoint pair on the evaluated radical quotients. -/
def hilbertModuleFibreQuotientInl (t : X) :
    AdjointableMap B (PositiveModuleQuotient B (EvaluatedModuleSpace B M t))
      (PositiveModuleQuotient B (EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t)) where
  toCLM := positiveModuleQuotientLiftCLM (evaluatedModuleSumInlLinear t) (K := 1)
    (fun x => by rw [evaluatedModuleSumInl_formNorm_eq]; simp only [one_mul, le_refl])
  adjointCLM := positiveModuleQuotientLiftCLM (evaluatedModuleSumFstLinear t)
    (evaluatedModuleSumFst_formNorm_le t)
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk, evaluatedModuleSum_inner]
    change ⟪x, evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t y).fst⟫_(Bᵐᵒᵖ) +
      ⟪(0 : EvaluatedModuleSpace B N t), evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t y).snd⟫_(Bᵐᵒᵖ) = _
    simp only [PositiveModuleForm.inner_zero_left, add_zero]
    rfl

def hilbertModuleFibreQuotientInr (t : X) :
    AdjointableMap B (PositiveModuleQuotient B (EvaluatedModuleSpace B N t))
      (PositiveModuleQuotient B (EvaluatedModuleSpace B (HilbertModuleSum C(X, B) M N) t)) where
  toCLM := positiveModuleQuotientLiftCLM (evaluatedModuleSumInrLinear t) (K := 1)
    (fun x => by rw [evaluatedModuleSumInr_formNorm_eq]; simp only [one_mul, le_refl])
  adjointCLM := positiveModuleQuotientLiftCLM (evaluatedModuleSumSndLinear t)
    (evaluatedModuleSumSnd_formNorm_le t)
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk, evaluatedModuleSum_inner]
    change ⟪(0 : EvaluatedModuleSpace B M t), evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t y).fst⟫_(Bᵐᵒᵖ) +
      ⟪x, evaluatedModuleOfOriginal B t (evaluatedModuleToOriginal t y).snd⟫_(Bᵐᵒᵖ) = _
    simp only [PositiveModuleForm.inner_zero_left, zero_add]
    rfl

/-- The completed first-coordinate inclusion. -/
def hilbertModuleFibreInl (t : X) : AdjointableMap B (HilbertModuleFibre B M t)
    (HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t) :=
  (hilbertModuleFibreQuotientInl t).completion

/-- The completed second-coordinate inclusion. -/
def hilbertModuleFibreInr (t : X) : AdjointableMap B (HilbertModuleFibre B N t)
    (HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t) :=
  (hilbertModuleFibreQuotientInr t).completion

/-- The completed first-coordinate projection, as the proved inclusion adjoint. -/
def hilbertModuleFibreFst (t : X) : AdjointableMap B
    (HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t) (HilbertModuleFibre B M t) :=
  (hilbertModuleFibreInl t).adjoint

/-- The completed second-coordinate projection. -/
def hilbertModuleFibreSnd (t : X) : AdjointableMap B
    (HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t) (HilbertModuleFibre B N t) :=
  (hilbertModuleFibreInr t).adjoint

@[simp] theorem hilbertModuleFibreInl_mk (t : X) (x : M) :
    hilbertModuleFibreInl (N := N) t (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (sumMk (B := C(X, B)) x (0 : N)) := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreInl, AdjointableMap.completion_apply_coe,
    hilbertModuleFibreMk_apply]
  rfl

@[simp] theorem hilbertModuleFibreInr_mk (t : X) (y : N) :
    hilbertModuleFibreInr (M := M) t (hilbertModuleFibreMk (B := B) t y) =
      hilbertModuleFibreMk (B := B) t (sumMk (B := C(X, B)) (0 : M) y) := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreInr, AdjointableMap.completion_apply_coe,
    hilbertModuleFibreMk_apply]
  rfl

@[simp] theorem hilbertModuleFibreFst_mk (t : X) (x : HilbertModuleSum C(X, B) M N) :
    hilbertModuleFibreFst t (hilbertModuleFibreMk (B := B) t x) = hilbertModuleFibreMk (B := B) t x.fst := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreFst, hilbertModuleFibreInl,
    AdjointableMap.completion_adjoint, AdjointableMap.completion_apply_coe, hilbertModuleFibreMk_apply]
  rfl

@[simp] theorem hilbertModuleFibreSnd_mk (t : X) (x : HilbertModuleSum C(X, B) M N) :
    hilbertModuleFibreSnd t (hilbertModuleFibreMk (B := B) t x) = hilbertModuleFibreMk (B := B) t x.snd := by
  rw [hilbertModuleFibreMk_apply, hilbertModuleFibreSnd, hilbertModuleFibreInr,
    AdjointableMap.completion_adjoint, AdjointableMap.completion_apply_coe, hilbertModuleFibreMk_apply]
  rfl

/-- Split the completed direct-sum fibre by the proved coordinate maps. -/
def hilbertModuleFibreSplit (t : X) : AdjointableMap B
    (HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t)
    (HilbertModuleSum B (HilbertModuleFibre B M t) (HilbertModuleFibre B N t)) :=
  sumInl.comp (hilbertModuleFibreFst t) + sumInr.comp (hilbertModuleFibreSnd t)

/-- Join the completed fibres through their actual completed coordinate inclusions. -/
def hilbertModuleFibreJoin (t : X) : AdjointableMap B
    (HilbertModuleSum B (HilbertModuleFibre B M t) (HilbertModuleFibre B N t))
    (HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t) :=
  (hilbertModuleFibreInl t).comp sumFst + (hilbertModuleFibreInr t).comp sumSnd

@[simp] theorem hilbertModuleFibreSplit_adjoint (t : X) :
    (hilbertModuleFibreSplit (B := B) (M := M) (N := N) t).adjoint = hilbertModuleFibreJoin t := rfl

@[simp] theorem hilbertModuleFibreSplit_mk (t : X) (x : HilbertModuleSum C(X, B) M N) :
    hilbertModuleFibreSplit t (hilbertModuleFibreMk (B := B) t x) =
      sumMk (hilbertModuleFibreMk (B := B) t x.fst) (hilbertModuleFibreMk (B := B) t x.snd) := by
  simp only [hilbertModuleFibreSplit, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
    hilbertModuleFibreFst_mk, hilbertModuleFibreSnd_mk, sumInl_apply, sumInr_apply, sumMk_add,
    zero_add, add_zero]

@[simp] theorem hilbertModuleFibreJoin_mk (t : X) (x : M) (y : N) :
    hilbertModuleFibreJoin t (sumMk (hilbertModuleFibreMk (B := B) t x)
      (hilbertModuleFibreMk (B := B) t y)) =
      hilbertModuleFibreMk (B := B) t (sumMk (B := C(X, B)) x y) := by
  simp only [hilbertModuleFibreJoin, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
    sumFst_apply, sumSnd_apply, sumMk_fst, sumMk_snd, hilbertModuleFibreInl_mk, hilbertModuleFibreInr_mk]
  rw [← map_add, sumMk_add]
  simp only [add_zero, zero_add]

theorem hilbertModuleFibreJoin_comp_split (t : X) :
    (hilbertModuleFibreJoin (B := B) (M := M) (N := N) t).comp (hilbertModuleFibreSplit t) = AdjointableMap.id := by
  apply AdjointableMap.ext
  intro z
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := HilbertModuleSum C(X, B) M N) t).induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  simp only [AdjointableMap.comp_apply, hilbertModuleFibreSplit_mk, hilbertModuleFibreJoin_mk,
    sumMk_eta, AdjointableMap.id_apply]

/-- Canonical pairs have dense image in the genuine direct sum of the completed fibres. -/
theorem hilbertModuleFibreSumMk_denseRange (t : X) :
    DenseRange (fun p : M × N => sumMk (B := B) (hilbertModuleFibreMk (B := B) t p.1)
      (hilbertModuleFibreMk (B := B) t p.2)) := by
  let e := (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ)
    (E := HilbertModuleFibre B M t × HilbertModuleFibre B N t)).symm
  exact e.surjective.denseRange.comp
    ((hilbertModuleFibreMk_denseRange (B := B) (M := M) t).prodMap
      (hilbertModuleFibreMk_denseRange (B := B) (M := N) t)) e.continuous

theorem hilbertModuleFibreSplit_comp_join (t : X) :
    (hilbertModuleFibreSplit (B := B) (M := M) (N := N) t).comp (hilbertModuleFibreJoin t) = AdjointableMap.id := by
  apply AdjointableMap.ext
  intro z
  refine (hilbertModuleFibreSumMk_denseRange (B := B) (M := M) (N := N) t).induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro p
  simp only [AdjointableMap.comp_apply, hilbertModuleFibreJoin_mk, hilbertModuleFibreSplit_mk,
    sumMk_fst, sumMk_snd, AdjointableMap.id_apply]

theorem hilbertModuleFibreSplit_inner (t : X)
    (x y : HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t) :
    ⟪hilbertModuleFibreSplit t x, hilbertModuleFibreSplit t y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(hilbertModuleFibreSplit (B := B) (M := M) (N := N) t).adjoint_identity]
  change ⟪x, hilbertModuleFibreJoin t (hilbertModuleFibreSplit t y)⟫_(Bᵐᵒᵖ) = _
  rw [← AdjointableMap.comp_apply, hilbertModuleFibreJoin_comp_split, AdjointableMap.id_apply]

/-- The actual fibre of a sum is unitarily the genuine sum of the actual fibres. -/
def hilbertModuleFibreSumEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t)
      (HilbertModuleSum B (HilbertModuleFibre B M t) (HilbertModuleFibre B N t)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := hilbertModuleFibreSplit t
          invFun := hilbertModuleFibreJoin t
          left_inv := fun x => by simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg (fun T => T x) (hilbertModuleFibreJoin_comp_split t)
          right_inv := fun x => by simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg (fun T => T x) (hilbertModuleFibreSplit_comp_join t)
          map_add' := (hilbertModuleFibreSplit t).toCLM.map_add
          map_smul' := (hilbertModuleFibreSplit t).toCLM.map_smul }
      norm_map' x := by
        change ‖hilbertModuleFibreSplit t x‖ = ‖x‖
        calc
          ‖hilbertModuleFibreSplit t x‖ = Real.sqrt ‖⟪hilbertModuleFibreSplit t x, hilbertModuleFibreSplit t x⟫_(Bᵐᵒᵖ)‖ := CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) _
          _ = Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ := by rw [hilbertModuleFibreSplit_inner]
          _ = ‖x‖ := (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := hilbertModuleFibreSplit_inner t

@[simp] theorem hilbertModuleFibreSumEquiv_mk (t : X) (x : HilbertModuleSum C(X, B) M N) :
    hilbertModuleFibreSumEquiv t (hilbertModuleFibreMk (B := B) t x) =
      sumMk (hilbertModuleFibreMk (B := B) t x.fst) (hilbertModuleFibreMk (B := B) t x.snd) :=
  hilbertModuleFibreSplit_mk t x

@[simp] theorem hilbertModuleFibreSumEquiv_symm_mk (t : X) (x : M) (y : N) :
    (hilbertModuleFibreSumEquiv (B := B) t).symm
      (sumMk (hilbertModuleFibreMk (B := B) t x) (hilbertModuleFibreMk (B := B) t y)) =
      hilbertModuleFibreMk (B := B) t (sumMk (B := C(X, B)) x y) :=
  hilbertModuleFibreJoin_mk t x y

variable [CompleteSpace M] [CompleteSpace N]

/-- The unitary intertwines actual diagonal operators after fibre descent. -/
theorem hilbertModuleFibreSumEquiv_operator_intertwine (t : X)
    (S : AdjointableMap C(X, B) M M) (T : AdjointableMap C(X, B) N N)
    (x : HilbertModuleFibre B (HilbertModuleSum C(X, B) M N) t) :
    hilbertModuleFibreSumEquiv t (hilbertModuleFibreOperator (B := B) t (sumMap S T) x) =
      sumMap (hilbertModuleFibreOperator (B := B) t S) (hilbertModuleFibreOperator (B := B) t T)
        (hilbertModuleFibreSumEquiv t x) := by
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := HilbertModuleSum C(X, B) M N) t).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro y
  simp only [hilbertModuleFibreOperator_mk, hilbertModuleFibreSumEquiv_mk,
    sumMap_apply, sumMk_fst, sumMk_snd]

/-- Conjugation by the genuine sum-fibre unitary gives the diagonal fibre operator. -/
theorem hilbertModuleFibreSumEquiv_transport_operator (t : X)
    (S : AdjointableMap C(X, B) M M) (T : AdjointableMap C(X, B) N N) :
    (hilbertModuleFibreSumEquiv (B := B) (M := M) (N := N) t).transport
        (hilbertModuleFibreOperator (B := B) t (sumMap S T)) =
      sumMap (hilbertModuleFibreOperator (B := B) t S) (hilbertModuleFibreOperator (B := B) t T) := by
  ext x
  rw [HilbertModuleEquiv.transport_apply, hilbertModuleFibreSumEquiv_operator_intertwine,
    HilbertModuleEquiv.apply_symm_apply]

end BC4lean.KKTheory
