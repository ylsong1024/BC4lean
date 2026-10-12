import BC4lean.HomogeneousModuleParsevalFrame
import BC4lean.InteriorModuleTensorFrameColumn
import BC4lean.CountableModuleGrading
import BC4lean.CountableModuleRectangularDefect
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # Actual connections for general coefficient gradings

A proved homogeneous Parseval frame constructs `W diag((-1)^p_n S) W*`.
The countable sum carries the genuine signed semilinear grading, W is even,
and the diagonal is odd. Every homogeneous connection defect is compact by
the actual creation-column norm tails and the graded coefficient commutator.
Both adjoint defects follow from the true graded adjoint commutator identity.
No first-factor semilinear grading is tensored alone or assumed B-linear.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {δB : CStarGrading B} {δC : CStarGrading C}

omit [StarOrderedRing B] [CompleteSpace E] in
/-- The coefficient of two homogeneous module vectors has the actual
coefficient degree determined by their two signs. -/
theorem homogeneous_module_coefficient_grade (J : GradedHilbertModule δB E)
    (x y : E) (p q : Bool)
    (hx : J.grading x = if p then -x else x)
    (hy : J.grading y = if q then -y else y) :
    δB.automorphism (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) =
      if p = q then MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)
      else -MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ) := by
  have h := congrArg MulOpposite.unop (J.inner_grading x y).symm
  rw [hx, hy] at h
  cases p <;> cases q <;>
    simpa only [if_true, if_false, Bool.false_eq_true, Bool.true_eq_false,
      CStarModule.inner_neg_left, CStarModule.inner_neg_right, neg_neg,
      MulOpposite.unop_neg, opStarAlgEquiv_apply, MulOpposite.unop_op] using h

omit [CompleteSpace F] in
/-- Adjointing the graded commutator at δ(star b) gives the genuine graded
commutator for S*, without discarding the coefficient grading. -/
theorem graded_coefficient_commutator_adjoint_compact
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (S : AdjointableMap C F F)
    (hS : ∀ b, IsModuleCompact (S * φ b - φ (δB.automorphism b) * S)) (b : B) :
    IsModuleCompact (S.adjoint * φ b - φ (δB.automorphism b) * S.adjoint) := by
  have h := (hS (δB.automorphism (star b))).adjoint.neg
  change IsModuleCompact (-(star (S * φ (δB.automorphism (star b)) -
    φ (δB.automorphism (δB.automorphism (star b))) * S))) at h
  change IsModuleCompact (star S * φ b - φ (δB.automorphism b) * star S)
  simpa only [star_sub, star_mul, map_star, star_star,
    CStarGrading.automorphism_sq, neg_sub] using h

namespace ModuleParsevalFrame

variable {ξ : ℕ → E}

/-- The homogeneous-frame compression on the actual interior tensor. -/
def gradedConnection (P : ModuleParsevalFrame (B := B) ξ)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (p : ℕ → Bool) (S : AdjointableMap C F F) :
    AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) :=
  (P.tensorSynthesis φ).comp ((countableModuleSignedDiagonal p S).comp (P.tensorSynthesis φ).adjoint)

@[simp] theorem gradedConnection_adjoint (P : ModuleParsevalFrame (B := B) ξ)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (p : ℕ → Bool) (S : AdjointableMap C F F) :
    (P.gradedConnection φ p S).adjoint = P.gradedConnection φ p S.adjoint := by
  simp only [gradedConnection, AdjointableMap.adjoint_comp,
    AdjointableMap.adjoint_adjoint, countableModuleSignedDiagonal_adjoint,
    AdjointableMap.comp_assoc]

theorem tensorSynthesis_isEven (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K) (p : ℕ → Bool)
    (hξ : ∀ n, J.grading (ξ n) = if p n then -ξ n else ξ n) :
    (signedCountableModuleGrading K p).IsEven (J.interiorTensor K hφ) (P.tensorSynthesis φ) := by
  let L := (J.interiorTensor K hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let M := (signedCountableModuleGrading K p).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have heq : L.comp (P.tensorSynthesis φ).toCLM = (P.tensorSynthesis φ).toCLM.comp M := by
    apply countableModule_clm_ext_inclusion
    intro n y
    change (J.interiorTensor K hφ).grading
        (P.tensorSynthesis φ (countableModuleInclusion (B := C) n y)) =
      P.tensorSynthesis φ ((signedCountableModuleGrading K p).grading
        (countableModuleInclusion (B := C) n y))
    rw [P.tensorSynthesis_inclusion φ, signedCountableModuleGrading_inclusion,
      P.tensorSynthesis_inclusion φ]
    change (J.interiorTensor K hφ).grading (interiorModuleTensorMk φ (ξ n) y) = _
    rw [GradedHilbertModule.interiorTensor_grading_mk, hξ]
    change interiorModuleTensorMk φ (if p n then -ξ n else ξ n) (K.grading y) =
      interiorModuleTensorMk φ (ξ n) (if p n then -K.grading y else K.grading y)
    cases p n
    · simp only [Bool.false_eq_true, if_false]
    · simp only [if_true]
      exact (((interiorModuleTensorMk φ).flip (K.grading y)).map_neg (ξ n)).trans
        ((interiorModuleTensorMk φ (ξ n)).map_neg (K.grading y)).symm
  exact fun u => DFunLike.congr_fun heq u

/-- The constructed graded connection is genuinely odd for the actual total
tensor grading, including when both coefficient gradings are nontrivial. -/
theorem gradedConnection_isOdd (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K) (p : ℕ → Bool)
    (hξ : ∀ n, J.grading (ξ n) = if p n then -ξ n else ξ n)
    {S : AdjointableMap C F F} (hS : K.IsOdd K S) :
    (J.interiorTensor K hφ).IsOdd (J.interiorTensor K hφ) (P.gradedConnection φ p S) :=
  (P.tensorSynthesis_isEven J K φ hφ p hξ).comp_odd
    ((countableModuleSignedDiagonal_isOdd K p hS).comp_even
      (P.tensorSynthesis_isEven J K φ hφ p hξ).adjoint)

/-- Actual homogeneous-frame compression preserves the exact selfadjointness
of the second operator. -/
theorem gradedConnection_selfadjoint (P : ModuleParsevalFrame (B := B) ξ)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (p : ℕ → Bool)
    {S : AdjointableMap C F F} (hS : IsSelfAdjoint S) :
    IsSelfAdjoint (P.gradedConnection φ p S) := by
  change (P.gradedConnection φ p S).adjoint = P.gradedConnection φ p S
  rw [P.gradedConnection_adjoint]
  exact congrArg (P.gradedConnection φ p) hS.star_eq

/-- The actual coisometric compression is bounded by the original second
operator norm; it introduces no global Fredholm-defect assumption. -/
theorem norm_gradedConnection_le (P : ModuleParsevalFrame (B := B) ξ)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (p : ℕ → Bool) (S : AdjointableMap C F F) :
    ‖P.gradedConnection φ p S‖ ≤ ‖S‖ := by
  calc
    _ ≤ ‖P.tensorSynthesis φ‖ *
        (‖countableModuleSignedDiagonal p S‖ * ‖(P.tensorSynthesis φ).adjoint‖) :=
      (AdjointableMap.norm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (AdjointableMap.norm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖S‖ * 1) := by
      gcongr
      · exact P.norm_tensorSynthesis_le_one φ
      · exact norm_countableModuleSignedDiagonal_le p S
      · change ‖(P.tensorSynthesis φ).adjoint.toCLM‖ ≤ 1
        rw [AdjointableMap.norm_adjoint_toCLM]
        exact P.norm_tensorSynthesis_le_one φ
    _ = ‖S‖ := by simp only [one_mul, mul_one]

/-- Each signed column coordinate is the actual graded coefficient
commutator, up to the proved homogeneous frame sign. -/
theorem gradedConnection_coordinate_defect_compact (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (p : ℕ → Bool) (hξ : ∀ n, J.grading (ξ n) = if p n then -ξ n else ξ n)
    (S : AdjointableMap C F F)
    (hS : ∀ b, IsModuleCompact (S * φ b - φ (δB.automorphism b) * S))
    (x : E) (q : Bool) (hx : J.grading x = if q then -x else x) (n : ℕ) :
    IsModuleCompact ((countableModuleEvaluation (B := C) n).comp
      ((countableModuleSignedDiagonal p S).comp (P.tensorCreationColumn φ x) -
        (P.tensorCreationColumn φ x).comp (if q then -S else S))) := by
  let b := MulOpposite.unop ⟪ξ n, x⟫_(Bᵐᵒᵖ)
  have hgrade : δB.automorphism b = if p n = q then b else -b :=
    homogeneous_module_coefficient_grade J (ξ n) x (p n) q (hξ n) hx
  have hcomm := hS b
  rw [hgrade] at hcomm
  have heq : (countableModuleEvaluation (B := C) n).comp
      ((countableModuleSignedDiagonal p S).comp (P.tensorCreationColumn φ x) -
        (P.tensorCreationColumn φ x).comp (if q then -S else S)) =
      (if p n then -S else S).comp (φ b) - (φ b).comp (if q then -S else S) := by
    ext y
    have hv := congrArg (fun R => R y) (P.evaluation_tensorCreationColumn φ n x)
    have hvs := congrArg (fun R => R ((if q then -S else S) y))
      (P.evaluation_tensorCreationColumn φ n x)
    simp only [AdjointableMap.comp_apply] at hv hvs
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub,
      countableModuleEvaluation_signedDiagonal]
    rw [hv, hvs]
    cases p n
    · rfl
    · simp only [b, if_true, AdjointableMap.coe_neg_apply]
  rw [heq]
  change IsModuleCompact ((if p n then -S else S) * φ b - φ b * (if q then -S else S))
  cases hp : p n <;> cases hq : q
  · simpa only [hp, hq, Bool.false_eq_true, if_false, if_true] using hcomm
  · simpa only [hp, hq, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
      map_neg, neg_mul, mul_neg, sub_neg_eq_add] using hcomm
  · convert hcomm.neg using 1
    ext y
    simp only [hp, hq, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
      map_neg, AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_neg_apply]
    abel
  · convert hcomm.neg using 1
    ext y
    simp only [hp, hq, if_true, map_neg, AdjointableMap.mul_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply]
    abel

/-- The full homogeneous connection defect is compact by the proved actual
column norm tails, rather than by assuming the creation maps compact. -/
theorem gradedConnection_comp_creation_sub_compact (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (p : ℕ → Bool) (hξ : ∀ n, J.grading (ξ n) = if p n then -ξ n else ξ n)
    (S : AdjointableMap C F F)
    (hS : ∀ b, IsModuleCompact (S * φ b - φ (δB.automorphism b) * S))
    (x : E) (q : Bool) (hx : J.grading x = if q then -x else x) :
    IsModuleCompact ((P.gradedConnection φ p S).comp (moduleCreationMap φ x) -
      (moduleCreationMap φ x).comp (if q then -S else S)) := by
  let V := P.tensorCreationColumn φ x
  have hdef : IsModuleCompact ((countableModuleSignedDiagonal p S).comp V -
      V.comp (if q then -S else S)) :=
    moduleCompact_countable_rectangular_defect _ _ V
      (countableModuleSignedDiagonal_comp_cutoff p S)
      (P.gradedConnection_coordinate_defect_compact J φ p hξ S hS x q hx)
      (P.tensorCreationColumn_norm_tail_tendsto_zero φ x)
  have heq : (P.gradedConnection φ p S).comp (moduleCreationMap φ x) -
      (moduleCreationMap φ x).comp (if q then -S else S) =
      (P.tensorSynthesis φ).comp ((countableModuleSignedDiagonal p S).comp V -
        V.comp (if q then -S else S)) := by
    ext y
    simp only [gradedConnection, AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply]
    change P.tensorSynthesis φ (countableModuleSignedDiagonal p S
      ((P.tensorSynthesis φ).adjoint (moduleCreationMap φ x y))) -
      moduleCreationMap φ x ((if q then -S else S) y) =
      P.tensorSynthesis φ (countableModuleSignedDiagonal p S (V y) -
        V ((if q then -S else S) y))
    rw [map_sub]
    have hWV := congrArg (fun R => R (moduleCreationMap φ x ((if q then -S else S) y)))
      (P.tensorSynthesis_comp_adjoint φ)
    rw [show P.tensorSynthesis φ (V ((if q then -S else S) y)) =
      moduleCreationMap φ x ((if q then -S else S) y) from hWV]
    rfl
  rw [heq]
  exact hdef.comp_left (P.tensorSynthesis φ)

end ModuleParsevalFrame
end BC4lean.KKTheory
