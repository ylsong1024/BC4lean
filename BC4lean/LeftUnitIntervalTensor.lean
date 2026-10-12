import BC4lean.LeftUnitIntervalRepresentation
import BC4lean.InteriorModuleTensorCountableGeneration
import BC4lean.GradedMatrixMoritaEvaluatedTensorExtension

/-! # The actual tensor and endpoint modules for the nonunital left unit

K is J ⊗_{C(I,Unitization A)} C(I,E), with the actual unital extension of
the original (possibly degenerate) representation. Endpoint zero evaluates
j⊗s to φ̃(j(0))s(0). Endpoint one evaluates to j(1).snd⊗s(1) in A⊗_A E.
Both maps descend through balancing and the actual null space, preserve the
whole evaluated pairing and extend to genuine completed fibres. Onto-ness
uses the scalar ramp at zero and pure-tensor density at one.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {A B E : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

abbrev LeftUnitIntervalTensor (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :=
  InteriorModuleTensor (E := LeftUnitIntervalIdeal A) (leftUnitIntervalSectionRepresentation φ)

theorem leftUnitIntervalTensor_countablyGenerated [TopologicalSpace.SeparableSpace A]
    (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule C(unitInterval, B) (LeftUnitIntervalTensor φ) :=
  (leftUnitIntervalIdeal_countablyGenerated (A := A)).interiorTensor
    (continuousSection_isCountablyGenerated hE) (leftUnitIntervalSectionRepresentation φ)

namespace LeftUnitIntervalTensor
variable (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E)

def zeroBilinear : LeftUnitIntervalIdeal A →ₗ[ℂ] C(unitInterval, E) →ₗ[ℂ] E where
  toFun j := (leftUnitExtendedRepresentation φ
    (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0)).toCLM.toLinearMap.comp
      (continuousSectionEvaluation (E := E) 0).toLinearMap
  map_add' j k := by
    apply LinearMap.ext
    intro s
    change leftUnitExtendedRepresentation φ
      (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0 +
        MulOpposite.unop (k : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (s 0) = _
    rw [map_add]
    rfl
  map_smul' z j := by
    apply LinearMap.ext
    intro s
    change leftUnitExtendedRepresentation φ
      (z • MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (s 0) = _
    rw [map_smul]
    rfl

theorem zeroBilinear_balance (b : C(unitInterval, Unitization ℂ A))
    (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    zeroBilinear φ (MulOpposite.op b • j) s =
      zeroBilinear φ j (leftUnitIntervalSectionRepresentation φ b s) := by
  change leftUnitExtendedRepresentation φ
    (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0 * b 0) (s 0) =
      leftUnitExtendedRepresentation φ
        (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0)
          (leftUnitExtendedRepresentation φ (b 0) (s 0))
  rw [map_mul, AdjointableMap.mul_apply]

def zeroBalanced : BalancedModuleTensor (E := LeftUnitIntervalIdeal A)
    (leftUnitIntervalSectionRepresentation φ) →ₗ[ℂ] E :=
  moduleTensorLift _ (zeroBilinear φ) (zeroBilinear_balance φ)

@[simp] theorem zeroBalanced_mk (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    zeroBalanced φ (moduleTensorMk _ j s) = leftUnitExtendedRepresentation φ
      (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (s 0) := rfl

theorem zeroBalanced_inner (u v : BalancedModuleTensor (E := LeftUnitIntervalIdeal A)
    (leftUnitIntervalSectionRepresentation φ)) :
    ⟪zeroBalanced φ u, zeroBalanced φ v⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop
        (moduleTensorInner (leftUnitIntervalSectionRepresentation φ) u v) 0) := by
  revert v
  refine moduleTensor_induction _ u ?_ ?_ ?_
  · intro v; simp
  · intro j s v
    refine moduleTensor_induction _ v ?_ ?_ ?_
    · simp
    · intro k r
      rw [zeroBalanced_mk, zeroBalanced_mk, moduleTensorInner_mk_mk]
      change ⟪leftUnitExtendedRepresentation φ
          (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (s 0),
        leftUnitExtendedRepresentation φ
          (MulOpposite.unop (k : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (r 0)⟫_(Bᵐᵒᵖ) =
        ⟪s 0, leftUnitExtendedRepresentation φ
          (star (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) *
            MulOpposite.unop (k : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (r 0)⟫_(Bᵐᵒᵖ)
      rw [AdjointableMap.adjoint_identity, map_mul, map_star, AdjointableMap.mul_apply]
      rfl
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right,
        MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left,
      MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hu, hw]

def zeroEvaluation : LeftUnitIntervalTensor φ →L[ℂ] E :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM
    (leftUnitIntervalSectionRepresentation φ) 0 (zeroBalanced φ) (zeroBalanced_inner φ)

@[simp] theorem zeroEvaluation_mk (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    zeroEvaluation φ (interiorModuleTensorMk _ j s) = leftUnitExtendedRepresentation φ
      (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (s 0) :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM_mk _ _ _ _ j s

theorem zeroEvaluation_inner (u v : LeftUnitIntervalTensor φ) :
    ⟪zeroEvaluation φ u, zeroEvaluation φ v⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪u, v⟫_(C(unitInterval, B)ᵐᵒᵖ) 0) :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM_inner _ _ _ _ u v

def zeroFibreIsometry : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor φ) 0 →ₗᵢ[ℂ] E :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry
    (B := B) (X := unitInterval) (M := LeftUnitIntervalTensor φ) (H := E)
    0 (zeroEvaluation φ) (zeroEvaluation_inner φ)

@[simp] theorem zeroFibreIsometry_mk (u : LeftUnitIntervalTensor φ) :
    zeroFibreIsometry φ (hilbertModuleFibreMk (B := B) (X := unitInterval) 0 u) = zeroEvaluation φ u := by
  let : CStarModule C(unitInterval, B)ᵐᵒᵖ
      (PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ)) :=
    preModuleTensorCStarModule (E := LeftUnitIntervalIdeal A)
      (leftUnitIntervalSectionRepresentation φ)
  let : CStarModule C(unitInterval, B)ᵐᵒᵖ (LeftUnitIntervalTensor φ) :=
    completionCStarModule (B := C(unitInterval, B))
      (E := PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ))
  exact GradedMatrixMoritaFibreEvaluation.completedIsometry_mk
    (B := B) (X := unitInterval) (M := LeftUnitIntervalTensor φ) (H := E)
    0 (zeroEvaluation φ) (zeroEvaluation_inner φ) u

theorem zeroFibreIsometry_surjective : Function.Surjective (zeroFibreIsometry φ) := by
  intro y
  refine ⟨hilbertModuleFibreMk (B := B) (X := unitInterval) 0
    (interiorModuleTensorMk _ (leftUnitIntervalRamp (MulOpposite.op (1 : Unitization ℂ A)))
      (ContinuousMap.const unitInterval y)), ?_⟩
  rw [zeroFibreIsometry_mk, zeroEvaluation_mk]
  have h := leftUnitIntervalEvaluation_zero_ramp (MulOpposite.op (1 : Unitization ℂ A))
  have hu := congrArg MulOpposite.unop h
  change MulOpposite.unop (leftUnitIntervalRamp (MulOpposite.op (1 : Unitization ℂ A)) :
    C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0 = 1 at hu
  rw [hu, leftUnitExtendedRepresentation_one, AdjointableMap.one_apply]
  rfl

def zeroFibreEquiv : HilbertModuleEquiv B
    (HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor φ) 0) E where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (zeroFibreIsometry φ)
    (zeroFibreIsometry_surjective φ)
  inner_map := by
    let : CStarModule C(unitInterval, B)ᵐᵒᵖ
        (PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
          (leftUnitIntervalSectionRepresentation φ)) :=
      preModuleTensorCStarModule (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ)
    let : CStarModule C(unitInterval, B)ᵐᵒᵖ (LeftUnitIntervalTensor φ) :=
      completionCStarModule (B := C(unitInterval, B))
        (E := PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
          (leftUnitIntervalSectionRepresentation φ))
    exact GradedMatrixMoritaFibreEvaluation.completedIsometry_inner
      (B := B) (X := unitInterval) (M := LeftUnitIntervalTensor φ) (H := E)
      0 (zeroEvaluation φ) (zeroEvaluation_inner φ)

@[simp] theorem zeroFibreEquiv_mk (u : LeftUnitIntervalTensor φ) :
    zeroFibreEquiv φ (hilbertModuleFibreMk (B := B) (X := unitInterval) 0 u) = zeroEvaluation φ u :=
  zeroFibreIsometry_mk φ u

@[simp] theorem zeroFibreEquiv_tensor_mk (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    zeroFibreEquiv φ (hilbertModuleFibreMk (B := B) (X := unitInterval) 0 (interiorModuleTensorMk _ j s)) =
      leftUnitExtendedRepresentation φ
        (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 0) (s 0) := by
  exact (zeroFibreIsometry_mk φ _).trans (zeroEvaluation_mk φ j s)

def oneCoefficient : LeftUnitIntervalIdeal A →ₗ[ℂ] Aᵐᵒᵖ :=
  leftUnitCoefficientIdealInr.symm.toLinearEquiv.toLinearMap.comp
    leftUnitIntervalEvaluationOne.toLinearMap

@[simp] theorem oneCoefficient_apply (j : LeftUnitIntervalIdeal A) :
    oneCoefficient j = MulOpposite.op
      (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 1).snd := rfl

theorem oneCoefficient_smul (b : C(unitInterval, Unitization ℂ A)) (j : LeftUnitIntervalIdeal A) :
    oneCoefficient (MulOpposite.op b • j) =
      (b 1).fst • oneCoefficient j + MulOpposite.op (b 1).snd • oneCoefficient j := by
  apply MulOpposite.unop_injective
  change (MulOpposite.unop (j : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 1 * b 1).snd = _
  rw [Unitization.snd_mul, leftUnitIntervalIdeal_scalar_one, zero_smul, zero_add]
  rfl

theorem oneCoefficient_inner (j k : LeftUnitIntervalIdeal A) :
    ((MulOpposite.unop ⟪oneCoefficient j, oneCoefficient k⟫_(Aᵐᵒᵖ) : A) : Unitization ℂ A) =
      MulOpposite.unop ⟪j, k⟫_(C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 1 := by
  have h := leftUnitCoefficientIdealInr_inner (oneCoefficient j) (oneCoefficient k)
  have hj : leftUnitCoefficientIdealInr (oneCoefficient j) = leftUnitIntervalEvaluationOne j :=
    leftUnitCoefficientIdealInr.apply_symm_apply _
  have hk : leftUnitCoefficientIdealInr (oneCoefficient k) = leftUnitIntervalEvaluationOne k :=
    leftUnitCoefficientIdealInr.apply_symm_apply _
  rw [hj, hk, leftUnitIntervalEvaluationOne_inner] at h
  exact congrArg MulOpposite.unop h.symm

def oneBilinear : LeftUnitIntervalIdeal A →ₗ[ℂ] C(unitInterval, E) →ₗ[ℂ]
    InteriorModuleTensor (E := Aᵐᵒᵖ) φ where
  toFun j := (interiorModuleTensorMk φ (oneCoefficient j)).comp
    (continuousSectionEvaluation (E := E) 1).toLinearMap
  map_add' j k := by
    apply LinearMap.ext
    intro s
    change interiorModuleTensorMk φ (oneCoefficient (j + k)) (s 1) =
      interiorModuleTensorMk φ (oneCoefficient j) (s 1) +
        interiorModuleTensorMk φ (oneCoefficient k) (s 1)
    rw [map_add]
    exact LinearMap.congr_fun
      ((interiorModuleTensorMk (E := Aᵐᵒᵖ) φ).map_add (oneCoefficient j) (oneCoefficient k)) (s 1)
  map_smul' z j := by
    apply LinearMap.ext
    intro s
    change interiorModuleTensorMk φ (oneCoefficient (z • j)) (s 1) =
      z • interiorModuleTensorMk φ (oneCoefficient j) (s 1)
    rw [map_smul]
    exact LinearMap.congr_fun
      ((interiorModuleTensorMk (E := Aᵐᵒᵖ) φ).map_smul z (oneCoefficient j)) (s 1)

theorem oneBilinear_balance (b : C(unitInterval, Unitization ℂ A))
    (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    oneBilinear φ (MulOpposite.op b • j) s =
      oneBilinear φ j (leftUnitIntervalSectionRepresentation φ b s) := by
  change interiorModuleTensorMk φ (oneCoefficient (MulOpposite.op b • j)) (s 1) =
    interiorModuleTensorMk φ (oneCoefficient j) (leftUnitExtendedRepresentation φ (b 1) (s 1))
  rw [oneCoefficient_smul, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    interiorModuleTensorMk_balance, leftUnitExtendedRepresentation_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    map_add, map_smul]

def oneBalanced : BalancedModuleTensor (E := LeftUnitIntervalIdeal A)
    (leftUnitIntervalSectionRepresentation φ) →ₗ[ℂ] InteriorModuleTensor (E := Aᵐᵒᵖ) φ :=
  moduleTensorLift _ (oneBilinear φ) (oneBilinear_balance φ)

@[simp] theorem oneBalanced_mk (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    oneBalanced φ (moduleTensorMk _ j s) =
      interiorModuleTensorMk φ (oneCoefficient j) (s 1) := rfl

theorem oneBalanced_inner (u v : BalancedModuleTensor (E := LeftUnitIntervalIdeal A)
    (leftUnitIntervalSectionRepresentation φ)) :
    ⟪oneBalanced φ u, oneBalanced φ v⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop
        (moduleTensorInner (leftUnitIntervalSectionRepresentation φ) u v) 1) := by
  revert v
  refine moduleTensor_induction _ u ?_ ?_ ?_
  · intro v
    simp [CStarModule.inner_zero_left (A := Bᵐᵒᵖ)
      (E := InteriorModuleTensor (E := Aᵐᵒᵖ) φ)]
  · intro j s v
    refine moduleTensor_induction _ v ?_ ?_ ?_
    · simp [CStarModule.inner_zero_right (A := Bᵐᵒᵖ)
        (E := InteriorModuleTensor (E := Aᵐᵒᵖ) φ)]
    · intro k r
      rw [oneBalanced_mk, oneBalanced_mk, interiorModuleTensorInner_mk_mk, moduleTensorInner_mk_mk]
      change ⟪s 1, φ (MulOpposite.unop ⟪oneCoefficient j, oneCoefficient k⟫_(Aᵐᵒᵖ)) (r 1)⟫_(Bᵐᵒᵖ) =
        ⟪s 1, leftUnitExtendedRepresentation φ
          (MulOpposite.unop ⟪j, k⟫_(C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) 1) (r 1)⟫_(Bᵐᵒᵖ)
      rw [← oneCoefficient_inner, leftUnitExtendedRepresentation_inr]
    · intro v w hv hw
      simp only [map_add,
        CStarModule.inner_add_right (A := Bᵐᵒᵖ)
          (E := InteriorModuleTensor (E := Aᵐᵒᵖ) φ),
        MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply,
      CStarModule.inner_add_left (A := Bᵐᵒᵖ)
        (E := InteriorModuleTensor (E := Aᵐᵒᵖ) φ),
      MulOpposite.unop_add, ContinuousMap.add_apply, MulOpposite.op_add, hu, hw]

def oneEvaluation : LeftUnitIntervalTensor φ →L[ℂ] InteriorModuleTensor (E := Aᵐᵒᵖ) φ :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM
    (leftUnitIntervalSectionRepresentation φ) 1 (oneBalanced φ) (oneBalanced_inner φ)

@[simp] theorem oneEvaluation_mk (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    oneEvaluation φ (interiorModuleTensorMk _ j s) =
      interiorModuleTensorMk φ (oneCoefficient j) (s 1) :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM_mk _ _ _ _ j s

theorem oneEvaluation_inner (u v : LeftUnitIntervalTensor φ) :
    ⟪oneEvaluation φ u, oneEvaluation φ v⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪u, v⟫_(C(unitInterval, B)ᵐᵒᵖ) 1) :=
  GradedMatrixMoritaEvaluatedTensorExtension.completedCLM_inner _ _ _ _ u v

def oneFibreIsometry : HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor φ) 1 →ₗᵢ[ℂ]
    InteriorModuleTensor (E := Aᵐᵒᵖ) φ :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry
    (B := B) (X := unitInterval) (M := LeftUnitIntervalTensor φ)
    (H := InteriorModuleTensor (E := Aᵐᵒᵖ) φ)
    1 (oneEvaluation φ) (oneEvaluation_inner φ)

@[simp] theorem oneFibreIsometry_mk (u : LeftUnitIntervalTensor φ) :
    oneFibreIsometry φ (hilbertModuleFibreMk (B := B) (X := unitInterval) 1 u) = oneEvaluation φ u := by
  let : CStarModule C(unitInterval, B)ᵐᵒᵖ
      (PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ)) :=
    preModuleTensorCStarModule (E := LeftUnitIntervalIdeal A)
      (leftUnitIntervalSectionRepresentation φ)
  let : CStarModule C(unitInterval, B)ᵐᵒᵖ (LeftUnitIntervalTensor φ) :=
    completionCStarModule (B := C(unitInterval, B))
      (E := PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ))
  exact GradedMatrixMoritaFibreEvaluation.completedIsometry_mk
    (B := B) (X := unitInterval) (M := LeftUnitIntervalTensor φ)
    (H := InteriorModuleTensor (E := Aᵐᵒᵖ) φ)
    1 (oneEvaluation φ) (oneEvaluation_inner φ) u

theorem oneFibreIsometry_surjective : Function.Surjective (oneFibreIsometry φ) := by
  let R := (oneFibreIsometry φ).toLinearMap.range
  have hR : IsClosed (R : Set (InteriorModuleTensor (E := Aᵐᵒᵖ) φ)) :=
    (oneFibreIsometry φ).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ (Set.range fun p : Aᵐᵒᵖ × E =>
      interiorModuleTensorMk φ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, y⟩, rfl⟩
    let j : LeftUnitIntervalIdeal A := leftUnitIntervalConstant (MulOpposite.unop a)
    let s : C(unitInterval, E) := ContinuousMap.const unitInterval y
    let u : LeftUnitIntervalTensor φ :=
      interiorModuleTensorMk (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ) j s
    refine ⟨hilbertModuleFibreMk (B := B) (X := unitInterval) 1 u, ?_⟩
    calc
      oneFibreIsometry φ (hilbertModuleFibreMk (B := B) (X := unitInterval) 1 u) =
          oneEvaluation φ u := by
        exact oneFibreIsometry_mk φ u
      _ = interiorModuleTensorMk (E := Aᵐᵒᵖ) φ (oneCoefficient j) (s 1) :=
        oneEvaluation_mk φ j s
      _ = interiorModuleTensorMk (E := Aᵐᵒᵖ) φ a y := rfl
  intro z
  change z ∈ R
  exact closure_minimal hspan hR
    (interiorModuleTensor_span_dense (E := Aᵐᵒᵖ) φ z)

def oneFibreEquiv : HilbertModuleEquiv B
    (HilbertModuleFibre (X := unitInterval) B (LeftUnitIntervalTensor φ) 1) (InteriorModuleTensor (E := Aᵐᵒᵖ) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (oneFibreIsometry φ)
    (oneFibreIsometry_surjective φ)
  inner_map := by
    let : CStarModule C(unitInterval, B)ᵐᵒᵖ
        (PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
          (leftUnitIntervalSectionRepresentation φ)) :=
      preModuleTensorCStarModule (E := LeftUnitIntervalIdeal A)
        (leftUnitIntervalSectionRepresentation φ)
    let : CStarModule C(unitInterval, B)ᵐᵒᵖ (LeftUnitIntervalTensor φ) :=
      completionCStarModule (B := C(unitInterval, B))
        (E := PreHilbertModuleTensor (E := LeftUnitIntervalIdeal A)
          (leftUnitIntervalSectionRepresentation φ))
    exact GradedMatrixMoritaFibreEvaluation.completedIsometry_inner
      (B := B) (X := unitInterval) (M := LeftUnitIntervalTensor φ)
      (H := InteriorModuleTensor (E := Aᵐᵒᵖ) φ)
      1 (oneEvaluation φ) (oneEvaluation_inner φ)

@[simp] theorem oneFibreEquiv_mk (u : LeftUnitIntervalTensor φ) :
    oneFibreEquiv φ (hilbertModuleFibreMk (B := B) (X := unitInterval) 1 u) = oneEvaluation φ u :=
  oneFibreIsometry_mk φ u

@[simp] theorem oneFibreEquiv_tensor_mk (j : LeftUnitIntervalIdeal A) (s : C(unitInterval, E)) :
    oneFibreEquiv φ (hilbertModuleFibreMk (B := B) (X := unitInterval) 1 (interiorModuleTensorMk _ j s)) =
      interiorModuleTensorMk φ (oneCoefficient j) (s 1) :=
  (oneFibreIsometry_mk φ _).trans (oneEvaluation_mk φ j s)

end LeftUnitIntervalTensor
end BC4lean.KKTheory
