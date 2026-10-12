import BC4lean.IntervalModuleFibreNorm

/-! # Evaluated-form descent without an assumed surjectivity law

An actual continuous linear evaluation preserving the entire evaluated
coefficient pairing gives an isometry from the genuine completed fibre.
Surjectivity is a separate conclusion, proved where the pure tensor range
is shown dense.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaFibreEvaluation
open scoped InnerProductSpace

variable {B X M H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [CompleteSpace H]
  (t : X) (f : M →L[ℂ] H)
  (hf : ∀ x y : M, ⟪f x, f y⟫_(Bᵐᵒᵖ) =
    MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t))

def quotientLinear : PositiveModuleQuotient B (EvaluatedModuleSpace B M t) →ₗ[ℂ] H :=
  (PositiveModuleForm.nullRadical (B := B) (E := EvaluatedModuleSpace B M t)).liftQ
    (f.toLinearMap.comp (evaluatedModuleLinearEquiv (B := B) (M := M) t).toLinearMap)
    (fun x hx => by
      apply (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp
      change ⟪f (evaluatedModuleToOriginal t x), f (evaluatedModuleToOriginal t x)⟫_(Bᵐᵒᵖ) = 0
      rw [hf]
      exact (PositiveModuleForm.mem_nullRadical x).mp hx)

omit [CompleteSpace M] [CompleteSpace H] in
theorem quotientLinear_norm (q : PositiveModuleQuotient B (EvaluatedModuleSpace B M t)) :
    ‖quotientLinear t f hf q‖ = ‖q‖ := by
  obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
  change ‖f (evaluatedModuleToOriginal t x)‖ = ‖positiveModuleQuotientMk (B := B) x‖
  rw [PositiveModuleQuotient.norm_mk,
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), hf]
  rfl

def quotientCLM : PositiveModuleQuotient B (EvaluatedModuleSpace B M t) →L[ℂ] H :=
  (quotientLinear t f hf).mkContinuous 1
    (fun q => by simpa only [one_mul] using (quotientLinear_norm t f hf q).le)

def completedCLM : HilbertModuleFibre B M t →L[ℂ] H := (quotientCLM t f hf).fromCompletion

omit [CompleteSpace M] in
@[simp] theorem completedCLM_mk (x : M) :
    completedCLM t f hf (hilbertModuleFibreMk (B := B) t x) = f x := by
  rw [hilbertModuleFibreMk_apply, completedCLM,
    ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

omit [CompleteSpace M] in
theorem completedCLM_norm (z : HilbertModuleFibre B M t) :
    ‖completedCLM t f hf z‖ = ‖z‖ := by
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_norm
  · intro x
    rw [completedCLM_mk, hilbertModuleFibre_norm_mk,
      CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), hf]
    rfl

def completedIsometry : HilbertModuleFibre B M t →ₗᵢ[ℂ] H where
  toLinearMap := (completedCLM t f hf).toLinearMap
  norm_map' := completedCLM_norm t f hf

omit [CompleteSpace M] in
@[simp] theorem completedIsometry_mk (x : M) :
    completedIsometry t f hf (hilbertModuleFibreMk (B := B) t x) = f x :=
  completedCLM_mk t f hf x

omit [CompleteSpace M] in
theorem completedIsometry_inner (x y : HilbertModuleFibre B M t) :
    ⟪completedIsometry t f hf x, completedIsometry t f hf y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  refine ((hilbertModuleFibreMk_denseRange (B := B) (M := M) t).prodMap
    (hilbertModuleFibreMk_denseRange (B := B) (M := M) t)).induction_on
      (p := fun z : HilbertModuleFibre B M t × HilbertModuleFibre B M t =>
        ⟪completedIsometry t f hf z.1, completedIsometry t f hf z.2⟫_(Bᵐᵒᵖ) =
          ⟪z.1, z.2⟫_(Bᵐᵒᵖ)) (x, y) ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro p
    change ⟪completedIsometry t f hf (hilbertModuleFibreMk (B := B) t p.1),
      completedIsometry t f hf (hilbertModuleFibreMk (B := B) t p.2)⟫_(Bᵐᵒᵖ) =
        ⟪hilbertModuleFibreMk (B := B) t p.1,
          hilbertModuleFibreMk (B := B) t p.2⟫_(Bᵐᵒᵖ)
    simp only [completedIsometry_mk, hilbertModuleFibre_inner_mk]
    exact hf p.1 p.2

end BC4lean.KKTheory.GradedMatrixMoritaFibreEvaluation
