import BC4lean.ReducedSourceTensorEmbedding
import BC4lean.AlgebraicCrossedRepresentation
import BC4lean.ModuleOperatorPositivity
import BC4lean.ModuleTensorOperator
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-! # The actual finite source regular action is reduced-norm contractive



The finite action on the genuine coefficient-norm indexed module is defined
coordinatewise.  The bound is proved using the canonical source tensor
embedding on localized vectors, then a contractive approximate identity.
The original representation may be degenerate.  In particular, the proof
uses a*e → a and never assumes π(e)x → x.
-/

noncomputable section
namespace BC4lean.KKTheory.ReducedSourceRegular
open scoped InnerProductSpace CStarAlgebra
open Filter Topology

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (α : CStarAlgebraAction Γ A)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)

local instance : DecidableEq Γ := Classical.decEq Γ

/-- The original represented coefficient acts at the actual twisted coordinate. -/
def finiteDiagonal (a : A) : IndexedHilbertModule.Vectors E Γ →ₗ[ℂ]
    IndexedHilbertModule.Vectors E Γ :=
  Finsupp.lsum ℂ fun t => (Finsupp.lsingle t).comp
    (π (α.automorphism t⁻¹ a)).toCLM.toLinearMap

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteDiagonal_single (a : A) (t : Γ) (x : E) :
    finiteDiagonal α π a (Finsupp.single t x) =
      Finsupp.single t (π (α.automorphism t⁻¹ a) x) :=
  Finsupp.lsum_single ℂ _ t x

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteDiagonal_apply (a : A)
    (ξ : IndexedHilbertModule.Vectors E Γ) (t : Γ) :
    finiteDiagonal α π a ξ t = π (α.automorphism t⁻¹ a) (ξ t) := by
  induction ξ using Finsupp.induction_linear with
  | zero => simp
  | add ξ η hξ hη => simp [hξ, hη]
  | single s x =>
    by_cases h : s = t
    · subst s; simp
    · simp [h]

/-- Actual left translation on finite E-valued vectors. -/
def finiteTranslate (g : Γ) : IndexedHilbertModule.Vectors E Γ →ₗ[ℂ]
    IndexedHilbertModule.Vectors E Γ :=
  Finsupp.lmapDomain E ℂ (Equiv.mulLeft g).toEmbedding

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteTranslate_single (g t : Γ) (x : E) :
    finiteTranslate g (Finsupp.single t x) = Finsupp.single (g * t) x := by
  change Finsupp.mapDomain (fun s : Γ => g * s) (Finsupp.single t x) = _
  exact Finsupp.mapDomain_single

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteTranslate_apply (g : Γ)
    (ξ : IndexedHilbertModule.Vectors E Γ) (t : Γ) :
    finiteTranslate g ξ t = ξ (g⁻¹ * t) := by
  change Finsupp.mapDomain (fun s : Γ => g * s) ξ t = _
  have h := Finsupp.mapDomain_apply (Equiv.mulLeft g).injective ξ (g⁻¹ * t)
  change Finsupp.mapDomain (fun s : Γ => g * s) ξ (g * (g⁻¹ * t)) = _ at h
  simpa only [mul_inv_cancel_left] using h

/-- The genuine finite regular generator π(a)λ(g). -/
def finiteGenerator (a : A) (g : Γ) : IndexedHilbertModule.Vectors E Γ →ₗ[ℂ]
    IndexedHilbertModule.Vectors E Γ :=
  (finiteDiagonal α π a).comp (finiteTranslate g)

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteGenerator_apply (a : A) (g : Γ)
    (ξ : IndexedHilbertModule.Vectors E Γ) (t : Γ) :
    finiteGenerator α π a g ξ t =
      π (α.automorphism t⁻¹ a) (ξ (g⁻¹ * t)) := by
  rw [finiteGenerator, LinearMap.comp_apply, finiteDiagonal_apply, finiteTranslate_apply]

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finiteGenerator_single (a : A) (g t : Γ) (x : E) :
    finiteGenerator α π a g (Finsupp.single t x) =
      Finsupp.single (g * t) (π (α.automorphism (g * t)⁻¹ a) x) := by
  rw [finiteGenerator, LinearMap.comp_apply, finiteTranslate_single, finiteDiagonal_single]

def finiteGeneratorCoefficientLinear (g : Γ) : A →ₗ[ℂ]
    (IndexedHilbertModule.Vectors E Γ →ₗ[ℂ] IndexedHilbertModule.Vectors E Γ) where
  toFun a := finiteGenerator α π a g
  map_add' a b := by
    apply LinearMap.ext
    intro ξ
    ext t
    simp only [finiteGenerator_apply, map_add, LinearMap.add_apply,
      Finsupp.add_apply, AdjointableMap.coe_add_apply]
  map_smul' z a := by
    apply LinearMap.ext
    intro ξ
    ext t
    simp only [finiteGenerator_apply, map_smul, LinearMap.smul_apply,
      Finsupp.smul_apply, AdjointableMap.coe_smul_apply, RingHom.id_apply]

/-- The actual finite integrated regular representation before its norm bound. -/
def finiteActionLinear : AlgebraicCrossedProduct α →ₗ[ℂ]
    (IndexedHilbertModule.Vectors E Γ →ₗ[ℂ] IndexedHilbertModule.Vectors E Γ) :=
  (Finsupp.lsum ℂ (finiteGeneratorCoefficientLinear α π)).comp
    (AlgebraicCrossedProduct.coeffLinearEquiv α).toLinearMap

def finiteAction (f : AlgebraicCrossedProduct α) :
    IndexedHilbertModule.Vectors E Γ →ₗ[ℂ] IndexedHilbertModule.Vectors E Γ :=
  finiteActionLinear α π f

@[simp] theorem finiteAction_zero : finiteAction α π 0 = 0 :=
  map_zero (finiteActionLinear α π)

@[simp] theorem finiteAction_add (f h : AlgebraicCrossedProduct α) :
    finiteAction α π (f + h) = finiteAction α π f + finiteAction α π h :=
  map_add (finiteActionLinear α π) f h

@[simp] theorem finiteAction_single (g : Γ) (a : A) :
    finiteAction α π (AlgebraicCrossedProduct.single α g a) =
      finiteGenerator α π a g := by
  change Finsupp.lsum ℂ (finiteGeneratorCoefficientLinear α π)
    (Finsupp.single g a) = _
  exact Finsupp.lsum_single ℂ (finiteGeneratorCoefficientLinear α π) g a

theorem finiteAction_eq_sum (f : AlgebraicCrossedProduct α) :
    finiteAction α π f = ∑ g ∈ (AlgebraicCrossedProduct.coeff α f).support,
      finiteGenerator α π (AlgebraicCrossedProduct.coeff α f g) g := rfl

theorem finiteAction_apply (f : AlgebraicCrossedProduct α)
    (ξ : IndexedHilbertModule.Vectors E Γ) (t : Γ) :
    finiteAction α π f ξ t =
      ∑ g ∈ (AlgebraicCrossedProduct.coeff α f).support,
        π (α.automorphism t⁻¹ (AlgebraicCrossedProduct.coeff α f g))
          (ξ (g⁻¹ * t)) := by
  rw [finiteAction_eq_sum]
  simp only [LinearMap.sum_apply, Finsupp.finsetSum_apply, finiteGenerator_apply]

/-- An actual regular coefficient generator sends an elementary coordinate to
its translated and twisted elementary coordinate. -/
theorem regularGenerator_inclusion (a : A) (g t : Γ) (c : Aᵐᵒᵖ) :
    reducedCrossedGenerator α a g (reducedCrossedInclusion t c) =
      reducedCrossedInclusion (g * t)
        (MulOpposite.op (α.automorphism (g * t)⁻¹ a * MulOpposite.unop c)) := by
  have htranslate : reducedCrossedRegular g (reducedCrossedInclusion t c) =
      reducedCrossedInclusion (g * t) c := by
    simp only [reducedCrossedInclusion_apply, reducedCrossedRegular_mk,
      reducedCrossedEmbeddingLinear, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rfl
  change reducedCrossedCoefficient α a
    (reducedCrossedRegular g (reducedCrossedInclusion t c)) = _
  rw [htranslate, reducedCrossedCoefficient_inclusion]

/-- The tensor embedding intertwines an original regular generator on every
actual localized finite preimage. -/
theorem canonical_generator_localizePreimage (a e : A) (g : Γ)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    ReducedSourceTensorEmbedding.canonical π
        (interiorModuleTensorOperator π (reducedCrossedGenerator α a g)
          (ReducedSourceTensorEmbedding.localizePreimage π e ξ)) =
      IndexedHilbertModule.mk (B := B)
        (finiteGenerator α π a g (ReducedSourceTensorEmbedding.localizeVector π e ξ)) := by
  let L := (ReducedSourceTensorEmbedding.canonical (Γ := Γ) π).toLinearMap.comp
    ((interiorModuleTensorOperator π (reducedCrossedGenerator α a g)).toCLM.toLinearMap.comp
      (ReducedSourceTensorEmbedding.localizePreimageLinear π e))
  let R := (IndexedHilbertModule.mk (B := B)).comp
    ((finiteGenerator α π a g).comp (ReducedSourceTensorEmbedding.localizeVector π e))
  change L ξ = R ξ
  induction ξ using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη]
  | single t x =>
    change ReducedSourceTensorEmbedding.canonical π
      (interiorModuleTensorOperator π (reducedCrossedGenerator α a g)
        (ReducedSourceTensorEmbedding.localizePreimage π e (Finsupp.single t x))) = _
    simp only [ReducedSourceTensorEmbedding.localizePreimage_single,
      interiorModuleTensorOperator_mk, regularGenerator_inclusion,
      ReducedSourceTensorEmbedding.canonical_mk_inclusion, MulOpposite.unop_op,
      ReducedSourceTensorEmbedding.localizeVector_single, finiteGenerator_single,
      map_mul, AdjointableMap.mul_apply, IndexedHilbertModule.inclusion_apply, R,
      LinearMap.comp_apply]

/-- This equality uses only actual finite sums, the canonical pairing isometry,
and the original coefficient representation. -/
theorem canonical_action_localizePreimage (f : AlgebraicCrossedProduct α) (e : A)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    ReducedSourceTensorEmbedding.canonical π
        (interiorModuleTensorOperator π (algebraicCrossedOperatorHom α f)
          (ReducedSourceTensorEmbedding.localizePreimage π e ξ)) =
      IndexedHilbertModule.mk (B := B)
        (finiteAction α π f (ReducedSourceTensorEmbedding.localizeVector π e ξ)) := by
  change ReducedSourceTensorEmbedding.canonical π
    (interiorModuleTensorOperatorHom π (algebraicCrossedOperatorHom α f)
      (ReducedSourceTensorEmbedding.localizePreimage π e ξ)) = _
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero =>
    simp only [map_zero, AdjointableMap.coe_zero_apply, finiteAction_zero,
      LinearMap.zero_apply]
  | single g a =>
    simpa only [algebraicCrossedOperatorHom_single, interiorModuleTensorOperatorHom_apply,
      finiteAction_single] using canonical_generator_localizePreimage α π a e g ξ
  | add f h hf hh =>
    simp only [map_add, AdjointableMap.coe_add_apply, finiteAction_add,
      LinearMap.add_apply, hf, hh]

omit [Group Γ] [PartialOrder A] [StarOrderedRing A] in
/-- Every actual contractive coefficient operator acts contractively on the
finite coefficient-form sum, by the coefficient-order operator inequality. -/
theorem localizeVector_inner_le (e : A) (he : ‖e‖ ≤ 1)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    IndexedHilbertModule.finiteInner (B := B)
        (ReducedSourceTensorEmbedding.localizeVector π e ξ)
        (ReducedSourceTensorEmbedding.localizeVector π e ξ) ≤
      IndexedHilbertModule.finiteInner (B := B) ξ ξ := by
  have hs : (ReducedSourceTensorEmbedding.localizeVector π e ξ).support ⊆ ξ.support :=
    Finsupp.support_mapRange (hf := map_zero (π e).toCLM.toLinearMap)
  rw [IndexedHilbertModule.finiteInner_eq_sum _ _ ξ.support hs,
    IndexedHilbertModule.finiteInner_eq_sum ξ ξ ξ.support Finset.Subset.rfl]
  apply Finset.sum_le_sum
  intro t _
  rw [ReducedSourceTensorEmbedding.localizeVector_apply]
  have hπ : ‖π e‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le π e).trans he
  have hsq : ‖π e‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (π e)]
  calc
    _ ≤ ‖π e‖ ^ 2 • ⟪ξ t, ξ t⟫_(Bᵐᵒᵖ) :=
      AdjointableMap.inner_self_apply_le (π e) (ξ t)
    _ ≤ 1 • ⟪ξ t, ξ t⟫_(Bᵐᵒᵖ) :=
      smul_le_smul_of_nonneg_right hsq CStarModule.inner_self_nonneg
    _ = _ := one_smul ℝ _

omit [Group Γ] [PartialOrder A] [StarOrderedRing A] in
theorem localizeVector_norm_le (e : A) (he : ‖e‖ ≤ 1)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    ‖IndexedHilbertModule.mk (B := B)
        (ReducedSourceTensorEmbedding.localizeVector π e ξ)‖ ≤
      ‖IndexedHilbertModule.mk (B := B) ξ‖ := by
  rw [IndexedHilbertModule.mk_norm_eq_formNorm, IndexedHilbertModule.mk_norm_eq_formNorm]
  apply Real.sqrt_le_sqrt
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (PositiveModuleForm.inner_self_nonneg (B := B)
      (x := ReducedSourceTensorEmbedding.localizeVector π e ξ))
    (localizeVector_inner_le π e he ξ)

/-- The desired reduced-norm estimate is already true on actual localized
vectors, without any nondegeneracy premise on π. -/
theorem finiteAction_localize_norm_le (f : AlgebraicCrossedProduct α) (e : A)
    (he : ‖e‖ ≤ 1) (ξ : IndexedHilbertModule.Vectors E Γ) :
    ‖IndexedHilbertModule.mk (B := B)
        (finiteAction α π f (ReducedSourceTensorEmbedding.localizeVector π e ξ))‖ ≤
      ‖algebraicCrossedOperatorHom α f‖ * ‖IndexedHilbertModule.mk (B := B) ξ‖ := by
  rw [← canonical_action_localizePreimage α π f e ξ,
    (ReducedSourceTensorEmbedding.canonical π).norm_map]
  calc
    _ ≤ ‖interiorModuleTensorOperator π (algebraicCrossedOperatorHom α f)‖ *
        ‖ReducedSourceTensorEmbedding.localizePreimage π e ξ‖ :=
      AdjointableMap.norm_apply_le _ _
    _ ≤ ‖algebraicCrossedOperatorHom α f‖ *
        ‖ReducedSourceTensorEmbedding.localizePreimage π e ξ‖ :=
      mul_le_mul_of_nonneg_right (interiorModuleTensorOperator_norm_le π _)
        (norm_nonneg _)
    _ = ‖algebraicCrossedOperatorHom α f‖ *
        ‖IndexedHilbertModule.mk (B := B)
          (ReducedSourceTensorEmbedding.localizeVector π e ξ)‖ := by
      rw [← ReducedSourceTensorEmbedding.canonical_localizePreimage,
        (ReducedSourceTensorEmbedding.canonical π).norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_left (localizeVector_norm_le π e he ξ) (norm_nonneg _)

omit [PartialOrder A] [StarOrderedRing A] in
/-- A fixed coefficient operator may be evaluated continuously in its
original C*-algebra coefficient, including for a degenerate representation. -/
theorem continuous_coefficient_apply (x : E) : Continuous (fun a : A => π a x) :=
  ((AdjointableMap.toCLMContinuousLinearMap (B := B) (E := E) (F := E)).continuous.comp
    (map_continuous π)).clm_apply continuous_const

/-- Approximation is used only after an actual source coefficient, where
right approximate-unit convergence is valid without nondegeneracy. -/
theorem finiteGenerator_localize_tendsto (a : A) (g : Γ)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    Tendsto (fun e : A => IndexedHilbertModule.mk (B := B)
      (finiteGenerator α π a g (ReducedSourceTensorEmbedding.localizeVector π e ξ)))
      (CStarAlgebra.approximateUnit A)
      (𝓝 (IndexedHilbertModule.mk (B := B) (finiteGenerator α π a g ξ))) := by
  induction ξ using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using tendsto_const_nhds
  | add ξ η hξ hη => simpa only [map_add] using hξ.add hη
  | single t x =>
    let c := α.automorphism (g * t)⁻¹ a
    have h := ((IndexedHilbertModule.inclusion (B := B) (g * t)).toCLM.continuous.tendsto
      (π c x)).comp (((continuous_coefficient_apply π x).tendsto c).comp
        ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left c))
    simpa only [Function.comp_def, ReducedSourceTensorEmbedding.localizeVector_single, finiteGenerator_single,
      map_mul, AdjointableMap.mul_apply, IndexedHilbertModule.inclusion_apply, c] using h

/-- Finite convolution of localized vectors converges in the actual module
norm.  Only finitely many represented products a*e occur. -/
theorem finiteAction_localize_tendsto (f : AlgebraicCrossedProduct α)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    Tendsto (fun e : A => IndexedHilbertModule.mk (B := B)
      (finiteAction α π f (ReducedSourceTensorEmbedding.localizeVector π e ξ)))
      (CStarAlgebra.approximateUnit A)
      (𝓝 (IndexedHilbertModule.mk (B := B) (finiteAction α π f ξ))) := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simpa only [finiteAction_zero, LinearMap.zero_apply, map_zero]
      using tendsto_const_nhds
  | single g a => simpa only [finiteAction_single]
      using finiteGenerator_localize_tendsto α π a g ξ
  | add f h hf hh =>
    simpa only [finiteAction_add, LinearMap.add_apply, map_add] using hf.add hh

/-- The actual finite regular source action is bounded by the original
concrete reduced norm.  No faithful or nondegenerate representation premise
and no reduced-norm/factorization conclusion is assumed. -/
theorem finiteAction_norm_le (f : AlgebraicCrossedProduct α)
    (ξ : IndexedHilbertModule.Vectors E Γ) :
    ‖IndexedHilbertModule.mk (B := B) (finiteAction α π f ξ)‖ ≤
      ‖algebraicCrossedOperatorHom α f‖ * ‖IndexedHilbertModule.mk (B := B) ξ‖ := by
  apply le_of_tendsto (finiteAction_localize_tendsto α π f ξ).norm
  filter_upwards [(CStarAlgebra.increasingApproximateUnit A).eventually_norm] with e he
  exact finiteAction_localize_norm_le α π f e he ξ

end BC4lean.KKTheory.ReducedSourceRegular
