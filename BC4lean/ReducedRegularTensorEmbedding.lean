import BC4lean.ArbitraryHilbertModuleSum
import BC4lean.KasparovDescentModule
import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.HilbertModuleApproximateUnit
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # The twisted regular tensor embeds in the actual indexed module

For the original equivariant right Hilbert module,
the actual pairing isometry E ⊗_B ℓ²(Γ,B) → ℓ²(Γ,E) sends
x ⊗ δ_t(c) to δ_t(U_(t⁻¹)(x) c).  The left B action in the tensor is the
already constructed twisted regular coefficient representation.  Every finite
pairing identity, bound, quotient descent and completion map is proved here.
Surjectivity is unnecessary for the reduced-norm estimate and is not claimed.
-/

noncomputable section
namespace BC4lean.KKTheory.ReducedRegularTensorEmbedding
open UniformSpace
open scoped InnerProductSpace

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {β : CStarAlgebraAction Γ B} (U : EquivariantHilbertModule β E)

local instance : DecidableEq Γ := Classical.decEq Γ

omit [StarOrderedRing B] [CompleteSpace E] in
private theorem coefficient_zero_smul (x : E) : (0 : Bᵐᵒᵖ) • x = 0 :=
  (moduleCoefficientVectorCLM x).map_zero

/-- The actual finite-vector formula in the regular tensor embedding. -/
def finite (x : E) : ReducedCrossedVectors B Γ →ₗ[ℂ]
    IndexedHilbertModule.Vectors E Γ :=
  Finsupp.lsum ℂ fun t => (Finsupp.lsingle t).comp
    (moduleCoefficientVectorCLM (U.action t⁻¹ x)).toLinearMap

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finite_single (x : E) (t : Γ) (c : Bᵐᵒᵖ) :
    finite U x (Finsupp.single t c) = Finsupp.single t (c • U.action t⁻¹ x) :=
  Finsupp.lsum_single ℂ _ t c

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem finite_apply (x : E) (f : ReducedCrossedVectors B Γ) (t : Γ) :
    finite U x f t = f t • U.action t⁻¹ x := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply, coefficient_zero_smul]
  | add f h hf hh => simp only [map_add, Finsupp.add_apply, hf, hh, module_add_smul]
  | single s c =>
    by_cases h : s = t
    · subst s
      simp
    · simp [h, coefficient_zero_smul]

omit [StarOrderedRing B] [CompleteSpace E] in
theorem finite_support (x : E) (f : ReducedCrossedVectors B Γ) :
    (finite U x f).support ⊆ f.support := by
  intro t ht
  by_contra h
  have hz : f t = 0 := Finsupp.notMem_support_iff.mp h
  exact Finsupp.mem_support_iff.mp ht (by rw [finite_apply, hz, coefficient_zero_smul])

omit [StarOrderedRing B] [CompleteSpace E] in
theorem finite_add_first (x y : E) (f : ReducedCrossedVectors B Γ) :
    finite U (x + y) f = finite U x f + finite U y f := by
  ext t
  simp only [finite_apply, map_add, Finsupp.add_apply, module_smul_add]

omit [StarOrderedRing B] [CompleteSpace E] in
theorem finite_smul_first (z : ℂ) (x : E) (f : ReducedCrossedVectors B Γ) :
    finite U (z • x) f = z • finite U x f := by
  ext t
  simp only [finite_apply, map_smul, Finsupp.smul_apply]
  apply module_inner_ext_right (B := B)
  intro y
  simp only [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex,
    mul_smul_comm]

omit [CompleteSpace E] in
/-- The complete finite pairing agrees exactly with the genuine regular
coefficient representation in the interior-tensor pairing. -/
theorem finite_inner (x y : E) (f h : ReducedCrossedVectors B Γ) :
    IndexedHilbertModule.finiteInner (B := B) (finite U x f) (finite U y h) =
      ⟪reducedCrossedMk f,
        reducedCrossedCoefficient β (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ))
          (reducedCrossedMk h)⟫_(Bᵐᵒᵖ) := by
  rw [IndexedHilbertModule.finiteInner_eq_sum _ _ f.support (finite_support U x f),
    reducedCrossedCoefficient_mk, reducedCrossedMk_inner,
    reducedCrossedFiniteInner_eq_sum _ _ f.support (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro t _
  simp only [finite_apply, reducedCrossedFiniteDiagonal_apply,
    CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
    U.inner_action, opStarAlgEquiv_apply]
  change h t * (MulOpposite.op (β.automorphism t⁻¹
    (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ))) * star (f t)) =
    MulOpposite.op (star (MulOpposite.unop (f t)) *
      (β.automorphism t⁻¹ (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) * MulOpposite.unop (h t)))
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_star]
  exact mul_assoc _ _ _

/-- Finite images have the same norm as the corresponding actual pure tensor. -/
theorem finite_norm (x : E) (f : ReducedCrossedVectors B Γ) :
    ‖IndexedHilbertModule.mk (B := B) (finite U x f)‖ =
      ‖interiorModuleTensorMk (reducedCrossedCoefficientHom β) x (reducedCrossedMk f)‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
    IndexedHilbertModule.mk_inner, finite_inner,
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
      (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x (reducedCrossedMk f)),
    interiorModuleTensorInner_mk_mk]
  rfl

def preFactor (x : E) : ReducedCrossedPreModule B Γ →ₗ[ℂ]
    IndexedHilbertModule.Module B E Γ :=
  (PositiveModuleForm.nullRadical (B := B) (E := ReducedCrossedVectors B Γ)).liftQ
    ((IndexedHilbertModule.mk (B := B)).comp (finite U x)) (fun f hf => by
      rw [reducedCrossedFinite_nullRadical_eq_bot, Submodule.mem_bot] at hf
      subst f
      exact (LinearMap.ker _).zero_mem)

omit [CompleteSpace E] in
@[simp] theorem preFactor_mk (x : E) (f : ReducedCrossedVectors B Γ) :
    preFactor U x (positiveModuleQuotientMk (B := B) f) =
      IndexedHilbertModule.mk (B := B) (finite U x f) := rfl

theorem preFactor_norm_le (x : E) (q : ReducedCrossedPreModule B Γ) :
    ‖preFactor U x q‖ ≤ ‖x‖ * ‖q‖ := by
  obtain ⟨f, rfl⟩ := positiveModuleQuotientMk_surjective q
  rw [preFactor_mk, finite_norm]
  simpa only [reducedCrossedMk_apply, Completion.norm_coe] using
    interiorModuleTensorMk_norm_le (reducedCrossedCoefficientHom β) x (reducedCrossedMk f)

/-- Extend the proved finite formula in its regular-module variable. -/
def factor (x : E) : ReducedCrossedHilbertModule B Γ →L[ℂ]
    IndexedHilbertModule.Module B E Γ :=
  ((preFactor U x).mkContinuous ‖x‖ (preFactor_norm_le U x)).fromCompletion

@[simp] theorem factor_mk (x : E) (f : ReducedCrossedVectors B Γ) :
    factor U x (reducedCrossedMk f) =
      IndexedHilbertModule.mk (B := B) (finite U x f) := by
  rw [reducedCrossedMk_apply, factor, ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

theorem factor_add (x y : E) : factor U (x + y) = factor U x + factor U y := by
  apply ContinuousLinearMap.ext
  intro z
  refine reducedCrossedMk_denseRange.induction_on z
    (isClosed_eq (factor U (x + y)).continuous
      ((factor U x).continuous.add (factor U y).continuous)) ?_
  intro f
  simp only [factor_mk, finite_add_first, map_add, add_apply]

theorem factor_smul (z : ℂ) (x : E) : factor U (z • x) = z • factor U x := by
  apply ContinuousLinearMap.ext
  intro y
  refine reducedCrossedMk_denseRange.induction_on y
    (isClosed_eq (factor U (z • x)).continuous
      ((factor U x).continuous.const_smul z)) ?_
  intro f
  simp only [factor_mk, finite_smul_first, map_smul, smul_apply]

def bilinear : E →ₗ[ℂ] ReducedCrossedHilbertModule B Γ →ₗ[ℂ]
    IndexedHilbertModule.Module B E Γ where
  toFun x := (factor U x).toLinearMap
  map_add' x y := congrArg ContinuousLinearMap.toLinearMap (factor_add U x y)
  map_smul' z x := congrArg ContinuousLinearMap.toLinearMap (factor_smul U z x)

theorem bilinear_balance (b : B) (x : E) (z : ReducedCrossedHilbertModule B Γ) :
    bilinear U (MulOpposite.op b • x) z =
      bilinear U x (reducedCrossedCoefficientHom β b z) := by
  refine reducedCrossedMk_denseRange.induction_on z
    (isClosed_eq (factor U (MulOpposite.op b • x)).continuous
      ((factor U x).continuous.comp (reducedCrossedCoefficientHom β b).toCLM.continuous)) ?_
  intro f
  change factor U (MulOpposite.op b • x) (reducedCrossedMk f) =
    factor U x (reducedCrossedCoefficient β b (reducedCrossedMk f))
  rw [reducedCrossedCoefficient_mk, factor_mk, factor_mk]
  congr 1
  ext t
  simp only [finite_apply, reducedCrossedFiniteDiagonal_apply,
    U.map_op_smul, opStarAlgEquiv_apply, MulOpposite.unop_op]
  rw [← module_mul_smul]
  rfl

theorem factor_inner (x y : E) (z w : ReducedCrossedHilbertModule B Γ) :
    ⟪factor U x z, factor U y w⟫_(Bᵐᵒᵖ) =
      ⟪z, reducedCrossedCoefficientHom β (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) w⟫_(Bᵐᵒᵖ) := by
  refine (reducedCrossedMk_denseRange.prodMap reducedCrossedMk_denseRange).induction_on
    (p := fun q : ReducedCrossedHilbertModule B Γ × ReducedCrossedHilbertModule B Γ =>
      ⟪factor U x q.1, factor U y q.2⟫_(Bᵐᵒᵖ) =
        ⟪q.1, reducedCrossedCoefficientHom β (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) q.2⟫_(Bᵐᵒᵖ))
    (z, w) (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro p
  change ⟪factor U x (reducedCrossedMk p.1), factor U y (reducedCrossedMk p.2)⟫_(Bᵐᵒᵖ) = _
  rw [factor_mk, factor_mk, IndexedHilbertModule.mk_inner]
  exact finite_inner U x y p.1 p.2

def balancedMap : BalancedModuleTensor (E := E) (reducedCrossedCoefficientHom β)
    →ₗ[ℂ] IndexedHilbertModule.Module B E Γ :=
  moduleTensorLift (reducedCrossedCoefficientHom β) (bilinear U) (bilinear_balance U)

@[simp] theorem balancedMap_mk (x : E) (z : ReducedCrossedHilbertModule B Γ) :
    balancedMap U (moduleTensorMk (reducedCrossedCoefficientHom β) x z) = factor U x z := rfl

theorem balancedMap_inner
    (u v : BalancedModuleTensor (E := E) (reducedCrossedCoefficientHom β)) :
    ⟪balancedMap U u, balancedMap U v⟫_(Bᵐᵒᵖ) =
      moduleTensorInner (reducedCrossedCoefficientHom β) u v := by
  revert v
  refine moduleTensor_induction (reducedCrossedCoefficientHom β) u ?_ ?_ ?_
  · intro v
    simp only [map_zero, LinearMap.zero_apply]
    exact CStarModule.inner_zero_left (A := Bᵐᵒᵖ)
      (E := IndexedHilbertModule.Module B E Γ)
  · intro x z v
    refine moduleTensor_induction (reducedCrossedCoefficientHom β) v ?_ ?_ ?_
    · simp only [map_zero]
      exact CStarModule.inner_zero_right (A := Bᵐᵒᵖ)
        (E := IndexedHilbertModule.Module B E Γ)
    · intro y w
      rw [balancedMap_mk, balancedMap_mk, moduleTensorInner_mk_mk]
      exact factor_inner U x y z w
    · intro v w hv hw
      simp only [map_add]
      rw [CStarModule.inner_add_right (A := Bᵐᵒᵖ)
        (E := IndexedHilbertModule.Module B E Γ), hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply]
    rw [CStarModule.inner_add_left (A := Bᵐᵒᵖ)
      (E := IndexedHilbertModule.Module B E Γ), hu w, hv w]

/-- The actual twisted regular tensor pairing isometry, on the completion. -/
def isometry : InteriorModuleTensor (E := E) (reducedCrossedCoefficientHom β)
    →ₗᵢ[ℂ] IndexedHilbertModule.Module B E Γ :=
  InteriorModuleTensorFormCompletion.completedIsometry (reducedCrossedCoefficientHom β)
    (balancedMap U) (balancedMap_inner U)

@[simp] theorem isometry_mk (x : E) (z : ReducedCrossedHilbertModule B Γ) :
    isometry U (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x z) = factor U x z :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk (reducedCrossedCoefficientHom β)
    (balancedMap U) (balancedMap_inner U) x z

@[simp] theorem isometry_mk_finite (x : E) (f : ReducedCrossedVectors B Γ) :
    isometry U (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x (reducedCrossedMk f)) =
      IndexedHilbertModule.mk (B := B) (finite U x f) := by
  rw [isometry_mk, factor_mk]

theorem isometry_inner
    (u v : InteriorModuleTensor (E := E) (reducedCrossedCoefficientHom β)) :
    ⟪isometry U u, isometry U v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) :=
  InteriorModuleTensorFormCompletion.completedIsometry_inner (reducedCrossedCoefficientHom β)
    (balancedMap U) (balancedMap_inner U) u v

@[simp] theorem isometry_mk_single (x : E) (t : Γ) (c : Bᵐᵒᵖ) :
    isometry U (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x
      (reducedCrossedInclusion t c)) =
      IndexedHilbertModule.inclusion (B := B) t (c • U.action t⁻¹ x) := by
  rw [reducedCrossedInclusion_apply, isometry_mk_finite, finite_single]
  rfl

end BC4lean.KKTheory.ReducedRegularTensorEmbedding
