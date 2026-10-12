import BC4lean.OddFredholmCompactUnitaryPullback

/-! # Actual coordinatewise unitaries of completed countable row modules

The genuine coefficient form is preserved on finite row vectors. The maps
descend through the actual null quotients and extend to their completions,
with their actual inverses as adjoints. No scalar Hilbert tensor product or
operator-valued amplification identification is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace CStarAlgebra

variable {B E N : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N]

def oddKTheoryCountableRowEquivLinear (u : HilbertModuleEquiv B E N) :
    CountableModuleVectors E →ₗ[ℂ] CountableModuleVectors N :=
  Finsupp.mapRange.linearMap u.toAdjointable.toCLM.toLinearMap

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace N] in
@[simp] theorem oddKTheoryCountableRowEquivLinear_apply (u : HilbertModuleEquiv B E N)
    (x : CountableModuleVectors E) (i : ℕ) : oddKTheoryCountableRowEquivLinear u x i = u (x i) := rfl

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace N] in
theorem oddKTheoryCountableRowEquivLinear_support (u : HilbertModuleEquiv B E N)
    (x : CountableModuleVectors E) : (oddKTheoryCountableRowEquivLinear u x).support ⊆ x.support :=
  Finsupp.support_mapRange (hf := map_zero u.toAdjointable.toCLM.toLinearMap)

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace N] in
theorem oddKTheoryCountableRowEquivLinear_inner (u : HilbertModuleEquiv B E N)
    (x : CountableModuleVectors E) (y : CountableModuleVectors N) :
    countableModuleFiniteInner (B := B) (oddKTheoryCountableRowEquivLinear u x) y =
      countableModuleFiniteInner (B := B) x (oddKTheoryCountableRowEquivLinear u.symm y) := by
  rw [countableModuleFiniteInner_eq_sum _ _ x.support (oddKTheoryCountableRowEquivLinear_support u x),
    countableModuleFiniteInner_eq_sum _ _ x.support Finset.Subset.rfl]
  exact Finset.sum_congr rfl (fun i _ => u.inner_left (x i) (y i))

omit [CompleteSpace E] [CompleteSpace N] in
theorem oddKTheoryCountableRowEquivLinear_formNorm (u : HilbertModuleEquiv B E N)
    (x : CountableModuleVectors E) :
    PositiveModuleForm.formNorm (B := B) (oddKTheoryCountableRowEquivLinear u x) =
      PositiveModuleForm.formNorm (B := B) x := by
  have hi : oddKTheoryCountableRowEquivLinear u.symm (oddKTheoryCountableRowEquivLinear u x) = x := by
    ext i
    exact u.symm_apply_apply (x i)
  simp only [PositiveModuleForm.formNorm, countableModuleFinite_inner]
  rw [oddKTheoryCountableRowEquivLinear_inner, hi]

def oddKTheoryCountableRowEquivQuotient (u : HilbertModuleEquiv B E N) :
    AdjointableMap B (CountableHilbertModulePreSum B E) (CountableHilbertModulePreSum B N) where
  toCLM := positiveModuleQuotientLiftCLM (oddKTheoryCountableRowEquivLinear u) (K := 1)
    (fun x => by rw [oddKTheoryCountableRowEquivLinear_formNorm, one_mul])
  adjointCLM := positiveModuleQuotientLiftCLM (oddKTheoryCountableRowEquivLinear u.symm) (K := 1)
    (fun x => by rw [oddKTheoryCountableRowEquivLinear_formNorm, one_mul])
  adjoint_identity x y := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective x
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective y
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    exact oddKTheoryCountableRowEquivLinear_inner u x y

def oddKTheoryCountableRowEquivMap (u : HilbertModuleEquiv B E N) :
    AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B N) :=
  (oddKTheoryCountableRowEquivQuotient u).completion

omit [CompleteSpace E] [CompleteSpace N] in
@[simp] theorem oddKTheoryCountableRowEquivMap_mk (u : HilbertModuleEquiv B E N)
    (x : CountableModuleVectors E) :
    oddKTheoryCountableRowEquivMap u (countableModuleMk (B := B) x) =
      countableModuleMk (B := B) (oddKTheoryCountableRowEquivLinear u x) := by
  rw [oddKTheoryCountableRowEquivMap, countableModuleMk_apply, AdjointableMap.completion_apply_coe,
    countableModuleMk_apply]
  rfl

omit [CompleteSpace E] [CompleteSpace N] in
@[simp] theorem oddKTheoryCountableRowEquivMap_adjoint (u : HilbertModuleEquiv B E N) :
    (oddKTheoryCountableRowEquivMap u).adjoint = oddKTheoryCountableRowEquivMap u.symm := by
  rw [oddKTheoryCountableRowEquivMap, AdjointableMap.completion_adjoint]
  rfl

omit [CompleteSpace E] [CompleteSpace N] in
theorem oddKTheoryCountableRowEquivMap_inverse (u : HilbertModuleEquiv B E N) :
    (oddKTheoryCountableRowEquivMap u.symm).comp (oddKTheoryCountableRowEquivMap u) = AdjointableMap.id := by
  ext z
  refine countableModuleMk_denseRange.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  simp only [AdjointableMap.comp_apply, oddKTheoryCountableRowEquivMap_mk, AdjointableMap.id_apply]
  congr 1
  ext i
  exact u.symm_apply_apply (x i)

omit [CompleteSpace E] [CompleteSpace N] in
theorem oddKTheoryCountableRowEquivMap_inner (u : HilbertModuleEquiv B E N)
    (x y : CountableHilbertModuleSum B E) :
    ⟪oddKTheoryCountableRowEquivMap u x, oddKTheoryCountableRowEquivMap u y⟫_(Bᵐᵒᵖ) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(oddKTheoryCountableRowEquivMap u).adjoint_identity]
  change ⟪x, (oddKTheoryCountableRowEquivMap u).adjoint (oddKTheoryCountableRowEquivMap u y)⟫_(Bᵐᵒᵖ) = _
  rw [oddKTheoryCountableRowEquivMap_adjoint, ← AdjointableMap.comp_apply,
    oddKTheoryCountableRowEquivMap_inverse, AdjointableMap.id_apply]

/-- The actual whole coordinatewise unitary of genuine completed row modules. -/
def oddKTheoryCountableRowEquiv (u : HilbertModuleEquiv B E N) :
    HilbertModuleEquiv B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B N) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := oddKTheoryCountableRowEquivMap u
          invFun := oddKTheoryCountableRowEquivMap u.symm
          left_inv x := by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
              congrArg (fun T => T x) (oddKTheoryCountableRowEquivMap_inverse u)
          right_inv x := by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply,
              HilbertModuleEquiv.symm_symm] using
              congrArg (fun T => T x) (oddKTheoryCountableRowEquivMap_inverse u.symm)
          map_add' := (oddKTheoryCountableRowEquivMap u).toCLM.map_add
          map_smul' := (oddKTheoryCountableRowEquivMap u).toCLM.map_smul }
      norm_map' x := by
        change ‖oddKTheoryCountableRowEquivMap u x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), oddKTheoryCountableRowEquivMap_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := oddKTheoryCountableRowEquivMap_inner u

@[simp] theorem oddKTheoryCountableRowEquiv_inclusion (u : HilbertModuleEquiv B E N)
    (i : ℕ) (x : E) :
    oddKTheoryCountableRowEquiv u (countableModuleInclusion i x) = countableModuleInclusion i (u x) := by
  change oddKTheoryCountableRowEquivMap u (countableModuleInclusion i x) =
    countableModuleInclusion i (u x)
  simp only [countableModuleInclusion_apply, oddKTheoryCountableRowEquivMap_mk]
  apply congrArg (countableModuleMk (B := B) (E := N))
  ext j
  by_cases h : i = j <;>
    simp [oddKTheoryCountableRowEquivLinear_apply, h]

end BC4lean.KKTheory
