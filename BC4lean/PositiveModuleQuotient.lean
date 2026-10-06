import BC4lean.PositiveModuleForm
import Mathlib.Analysis.Normed.Operator.Basic

/-! # The normed quotient of a positive module form

The null radical of an actual positive semidefinite form is removed by a
complex module quotient. Its inner product and coefficient action are lifted
from the original vectors, and its norm is the square root of the diagonal
form norm. No norm on the original vector space is used.

The quotient has an actual normed complex space and C⋆-module structure.
Form-bounded complex linear maps descend to continuous linear maps between
these quotients, with the same proved bound.
-/

noncomputable section

namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E] [PositiveModuleForm B E]

/-- A separate type for the radical quotient, equipped below with the norm
defined by the form rather than any ambient quotient norm. -/
def PositiveModuleQuotient (B E : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E]
    [PositiveModuleForm B E] :=
  E ⧸ PositiveModuleForm.nullRadical (B := B) (E := E)

namespace PositiveModuleQuotient

instance instAddCommGroup : AddCommGroup (PositiveModuleQuotient B E) :=
  inferInstanceAs (AddCommGroup (E ⧸ PositiveModuleForm.nullRadical (B := B) (E := E)))

instance instModule : Module ℂ (PositiveModuleQuotient B E) :=
  inferInstanceAs (Module ℂ (E ⧸ PositiveModuleForm.nullRadical (B := B) (E := E)))

end PositiveModuleQuotient

/-- The actual quotient map onto the radical quotient. -/
def positiveModuleQuotientMk : E →ₗ[ℂ] PositiveModuleQuotient B E :=
  (PositiveModuleForm.nullRadical (B := B) (E := E)).mkQ

theorem positiveModuleQuotientMk_surjective :
    Function.Surjective (positiveModuleQuotientMk (B := B) (E := E)) :=
  (PositiveModuleForm.nullRadical (B := B) (E := E)).mkQ_surjective

namespace PositiveModuleQuotient

local notation "N" => PositiveModuleForm.nullRadical (B := B) (E := E)
local notation "Q" => PositiveModuleQuotient B E
local notation "mk" => positiveModuleQuotientMk (B := B) (E := E)

@[simp] theorem mk_eq_zero (x : E) : mk x = 0 ↔ x ∈ N :=
  Submodule.Quotient.mk_eq_zero N

theorem mk_eq_mk (x y : E) : mk x = mk y ↔ x - y ∈ N :=
  Submodule.Quotient.eq N

/-- The original coefficient action descends because it preserves radical
cosets; no distributivity assumption on the original action is needed. -/
instance instSMul : SMul Bᵐᵒᵖ Q where
  smul a q := Quotient.liftOn q (fun x => mk (a • x)) fun x x' hx => by
    apply (mk_eq_mk _ _).mpr
    exact PositiveModuleForm.op_smul_sub_mem_nullRadical a
      ((Submodule.quotientRel_def N).mp hx)

@[simp] theorem op_smul_mk (a : Bᵐᵒᵖ) (x : E) : a • mk x = mk (a • x) := rfl

/-- The form on the quotient is its actual representative-independent lift. -/
instance instInner : Inner Bᵐᵒᵖ Q where
  inner q r := Quotient.liftOn₂ q r (fun x y => inner Bᵐᵒᵖ x y)
    fun _x _y _x' _y' hx hy =>
      (PositiveModuleForm.inner_eq_of_sub_mem_left
        ((Submodule.quotientRel_def N).mp hx)).trans
      (PositiveModuleForm.inner_eq_of_sub_mem_right
        ((Submodule.quotientRel_def N).mp hy))

@[simp] theorem inner_mk (x y : E) :
    inner Bᵐᵒᵖ (mk x) (mk y) = inner Bᵐᵒᵖ x y := rfl

instance instPositiveModuleForm : PositiveModuleForm B Q where
  inner := inner Bᵐᵒᵖ
  inner_add_right := by
    intro q r s
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    obtain ⟨z, rfl⟩ := positiveModuleQuotientMk_surjective s
    rw [← (positiveModuleQuotientMk (B := B) (E := E)).map_add, inner_mk, inner_mk, inner_mk]
    exact PositiveModuleForm.inner_add_right
  inner_self_nonneg := by
    intro q
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    rw [inner_mk]
    exact PositiveModuleForm.inner_self_nonneg
  inner_op_smul_right := by
    intro a q r
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [op_smul_mk, inner_mk, inner_mk]
    exact PositiveModuleForm.inner_op_smul_right
  inner_smul_right_complex := by
    intro c q r
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [← (positiveModuleQuotientMk (B := B) (E := E)).map_smul, inner_mk, inner_mk]
    exact PositiveModuleForm.inner_smul_right_complex
  star_inner := by
    intro q r
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [inner_mk, inner_mk]
    exact PositiveModuleForm.star_inner x y

/-- Removing the actual null radical makes the descended form definite. -/
theorem inner_self_eq_zero_iff (q : Q) : inner Bᵐᵒᵖ q q = 0 ↔ q = 0 := by
  obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
  rw [inner_mk, mk_eq_zero, PositiveModuleForm.mem_nullRadical]

instance instNorm : Norm Q where
  norm := PositiveModuleForm.formNorm (B := B)

theorem norm_eq_formNorm (q : Q) : ‖q‖ = PositiveModuleForm.formNorm (B := B) q := rfl

/-- The normed-space core follows from proved semidefinite Cauchy–Schwarz and
the proved definiteness of the quotient form. -/
theorem normedSpaceCore : NormedSpace.Core ℂ Q :=
  PositiveModuleForm.normedSpaceCore norm_eq_formNorm
    (fun q => (inner_self_eq_zero_iff q).mp)

instance instNormedAddCommGroup : NormedAddCommGroup Q :=
  NormedAddCommGroup.ofCore (normedSpaceCore (B := B) (E := E))

instance instNormedSpace : NormedSpace ℂ Q :=
  NormedSpace.ofCore (normedSpaceCore (B := B) (E := E))

instance instCStarModule : CStarModule Bᵐᵒᵖ Q :=
  PositiveModuleForm.toCStarModule norm_eq_formNorm
    (fun q => (inner_self_eq_zero_iff q).mp)

@[simp] theorem norm_mk (x : E) : ‖mk x‖ = PositiveModuleForm.formNorm (B := B) x := rfl

end PositiveModuleQuotient

section LinearDescent

variable {C F : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [AddCommGroup F] [Module ℂ F] [SMul Cᵐᵒᵖ F] [PositiveModuleForm C F]

/-- A form-bounded complex linear map necessarily preserves the null radical. -/
theorem map_mem_nullRadical_of_formNorm_le (f : E →ₗ[ℂ] F) {K : ℝ}
    (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) {x : E}
    (hx : x ∈ PositiveModuleForm.nullRadical (B := B) (E := E)) :
    f x ∈ PositiveModuleForm.nullRadical (B := C) (E := F) := by
  apply (PositiveModuleForm.formNorm_eq_zero_iff (f x)).mp
  apply le_antisymm
  · simpa [(PositiveModuleForm.formNorm_eq_zero_iff x).mpr hx] using hf x
  · exact PositiveModuleForm.formNorm_nonneg _

/-- Linear descent to the actual radical quotients. -/
def positiveModuleQuotientLift (f : E →ₗ[ℂ] F) {K : ℝ}
    (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) :
    PositiveModuleQuotient B E →ₗ[ℂ] PositiveModuleQuotient C F :=
  (PositiveModuleForm.nullRadical (B := B) (E := E)).liftQ
    ((positiveModuleQuotientMk (B := C)).comp f) fun _x hx =>
      (PositiveModuleQuotient.mk_eq_zero _).mpr
        (map_mem_nullRadical_of_formNorm_le f hf hx)

@[simp] theorem positiveModuleQuotientLift_mk (f : E →ₗ[ℂ] F) {K : ℝ}
    (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) (x : E) :
    positiveModuleQuotientLift f hf (positiveModuleQuotientMk (B := B) x) =
      positiveModuleQuotientMk (B := C) (f x) := rfl

theorem positiveModuleQuotientLift_norm_le (f : E →ₗ[ℂ] F) {K : ℝ}
    (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) (q : PositiveModuleQuotient B E) :
    ‖positiveModuleQuotientLift f hf q‖ ≤ K * ‖q‖ := by
  obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
  simpa only [positiveModuleQuotientLift_mk, PositiveModuleQuotient.norm_mk] using hf x

/-- The form bound gives a genuine continuous linear map between the normed
quotients, without requiring a norm or topology on the original vectors. -/
def positiveModuleQuotientLiftCLM (f : E →ₗ[ℂ] F) {K : ℝ}
    (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) :
    PositiveModuleQuotient B E →L[ℂ] PositiveModuleQuotient C F :=
  (positiveModuleQuotientLift f hf).mkContinuous K
    (positiveModuleQuotientLift_norm_le f hf)

@[simp] theorem positiveModuleQuotientLiftCLM_mk (f : E →ₗ[ℂ] F) {K : ℝ}
    (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) (x : E) :
    positiveModuleQuotientLiftCLM f hf (positiveModuleQuotientMk (B := B) x) =
      positiveModuleQuotientMk (B := C) (f x) := rfl

theorem positiveModuleQuotientLiftCLM_norm_le (f : E →ₗ[ℂ] F) {K : ℝ}
    (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) (q : PositiveModuleQuotient B E) :
    ‖positiveModuleQuotientLiftCLM f hf q‖ ≤ K * ‖q‖ :=
  positiveModuleQuotientLift_norm_le f hf q

theorem norm_positiveModuleQuotientLiftCLM_le (f : E →ₗ[ℂ] F) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x, PositiveModuleForm.formNorm (B := C) (f x) ≤
      K * PositiveModuleForm.formNorm (B := B) x) :
    ‖positiveModuleQuotientLiftCLM f hf‖ ≤ K :=
  (positiveModuleQuotientLift f hf).mkContinuous_norm_le hK
    (positiveModuleQuotientLift_norm_le f hf)

end LinearDescent

end BC4lean.KKTheory
