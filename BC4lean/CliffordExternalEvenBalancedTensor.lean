import BC4lean.CliffordExternalEvenOperator
import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.ModuleCreationMap

/-! # The genuine balanced tensor for an odd first factor and an even second factor

The two coefficient copies of the first module are balanced against the
Koszul half-representations of the second module. The actual grading
projections split the second vectors. Their orthogonality proves the entire
coefficient-valued form identity before radical descent and completion.
Pure tensor density and the sum of the grading projections prove onto-ness,
without using a unit in either coefficient algebra.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenBalancedTensor
open scoped InnerProductSpace
open CliffordExternalEvenRepresentation

variable {B C H F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)
  (hφ : ∀ b, J.toAdjointable * φ b = φ b * J.toAdjointable)

abbrev SourceTensor := InteriorModuleTensor (E := CliffordPairModule B H) (representation φ J hφ)
abbrev TargetModule := CliffordPairModule C (InteriorModuleTensor (E := H) φ)

def plus : AdjointableMap C F F := CliffordOne.plusProjection J.toAdjointable
def minus : AdjointableMap C F F := CliffordOne.minusProjection J.toAdjointable

theorem plus_adjoint : (plus J).adjoint = plus J :=
  CliffordOne.plusProjection_star J.toAdjointable J.toAdjointable_adjoint
theorem minus_adjoint : (minus J).adjoint = minus J :=
  CliffordOne.minusProjection_star J.toAdjointable J.toAdjointable_adjoint
theorem plus_square : plus J * plus J = plus J :=
  CliffordOne.plusProjection_square J.toAdjointable J.toAdjointable_sq
theorem minus_square : minus J * minus J = minus J :=
  CliffordOne.minusProjection_square J.toAdjointable J.toAdjointable_sq
theorem plus_mul_minus : plus J * minus J = 0 :=
  CliffordOne.plus_mul_minus J.toAdjointable J.toAdjointable_sq
theorem minus_mul_plus : minus J * plus J = 0 :=
  CliffordOne.minus_mul_plus J.toAdjointable J.toAdjointable_sq
theorem plus_add_minus : plus J + minus J = 1 :=
  CliffordOne.plus_add_minus J.toAdjointable

include hφ in
omit [PartialOrder B] [StarOrderedRing B] in
theorem plus_commutes (b : B) : plus J * φ b = φ b * plus J := by
  simp only [plus, CliffordOne.plusProjection, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_add, one_mul, mul_one, hφ b]
include hφ in
omit [PartialOrder B] [StarOrderedRing B] in
theorem minus_commutes (b : B) : minus J * φ b = φ b * minus J := by
  simp only [minus, CliffordOne.minusProjection, smul_mul_assoc, mul_smul_comm,
    sub_mul, mul_sub, one_mul, mul_one, hφ b]

omit [PartialOrder B] [StarOrderedRing B] in
theorem plus_half (b : B × B) (y : F) :
    plus J (halfRepresentation φ J hφ b y) = φ b.1 (plus J y) := by
  have hh : plus J * halfRepresentation φ J hφ b = φ b.1 * plus J := by
    rw [halfRepresentation_eq]
    change plus J * (φ b.1 * plus J + φ b.2 * minus J) = _
    rw [mul_add, ← mul_assoc, plus_commutes φ J hφ, mul_assoc, plus_square,
      ← mul_assoc, plus_commutes φ J hφ, mul_assoc, plus_mul_minus, mul_zero, add_zero]
  exact congrArg (fun T : AdjointableMap C F F => T y) hh

omit [PartialOrder B] [StarOrderedRing B] in
theorem minus_half (b : B × B) (y : F) :
    minus J (halfRepresentation φ J hφ b y) = φ b.2 (minus J y) := by
  have hh : minus J * halfRepresentation φ J hφ b = φ b.2 * minus J := by
    rw [halfRepresentation_eq]
    change minus J * (φ b.1 * plus J + φ b.2 * minus J) = _
    rw [mul_add, ← mul_assoc, minus_commutes φ J hφ, mul_assoc, minus_mul_plus,
      mul_zero, zero_add, ← mul_assoc, minus_commutes φ J hφ, mul_assoc, minus_square]
  exact congrArg (fun T : AdjointableMap C F F => T y) hh

include hφ in
omit [PartialOrder B] [StarOrderedRing B] in
theorem inner_plus_plus (b : B) (y z : F) :
    ⟪plus J y, φ b (plus J z)⟫_(Cᵐᵒᵖ) = ⟪y, φ b (plus J z)⟫_(Cᵐᵒᵖ) := by
  have hh : plus J * φ b * plus J = φ b * plus J := by
    rw [plus_commutes φ J hφ, mul_assoc, plus_square]
  rw [(plus J).adjoint_identity]
  change ⟪y, (plus J).adjoint (φ b (plus J z))⟫_(Cᵐᵒᵖ) = _
  rw [plus_adjoint]
  exact congrArg (fun w : F => ⟪y, w⟫_(Cᵐᵒᵖ))
    (congrArg (fun T : AdjointableMap C F F => T z) hh)

include hφ in
omit [PartialOrder B] [StarOrderedRing B] in
theorem inner_plus_minus (b : B) (y z : F) :
    ⟪plus J y, φ b (minus J z)⟫_(Cᵐᵒᵖ) = 0 := by
  have hh : plus J * φ b * minus J = 0 := by
    rw [plus_commutes φ J hφ, mul_assoc, plus_mul_minus, mul_zero]
  rw [(plus J).adjoint_identity]
  change ⟪y, (plus J).adjoint (φ b (minus J z))⟫_(Cᵐᵒᵖ) = _
  rw [plus_adjoint]
  have hz : plus J (φ b (minus J z)) = 0 :=
    congrArg (fun T : AdjointableMap C F F => T z) hh
  rw [hz, CStarModule.inner_zero_right]

include hφ in
omit [PartialOrder B] [StarOrderedRing B] in
theorem inner_minus_plus (b : B) (y z : F) :
    ⟪minus J y, φ b (plus J z)⟫_(Cᵐᵒᵖ) = 0 := by
  have hh : minus J * φ b * plus J = 0 := by
    rw [minus_commutes φ J hφ, mul_assoc, minus_mul_plus, mul_zero]
  rw [(minus J).adjoint_identity]
  change ⟪y, (minus J).adjoint (φ b (plus J z))⟫_(Cᵐᵒᵖ) = _
  rw [minus_adjoint]
  have hz : minus J (φ b (plus J z)) = 0 :=
    congrArg (fun T : AdjointableMap C F F => T z) hh
  rw [hz, CStarModule.inner_zero_right]

include hφ in
omit [PartialOrder B] [StarOrderedRing B] in
theorem inner_minus_minus (b : B) (y z : F) :
    ⟪minus J y, φ b (minus J z)⟫_(Cᵐᵒᵖ) = ⟪y, φ b (minus J z)⟫_(Cᵐᵒᵖ) := by
  have hh : minus J * φ b * minus J = φ b * minus J := by
    rw [minus_commutes φ J hφ, mul_assoc, minus_square]
  rw [(minus J).adjoint_identity]
  change ⟪y, (minus J).adjoint (φ b (minus J z))⟫_(Cᵐᵒᵖ) = _
  rw [minus_adjoint]
  exact congrArg (fun w : F => ⟪y, w⟫_(Cᵐᵒᵖ))
    (congrArg (fun T : AdjointableMap C F F => T z) hh)

/-- The actual bilinear Koszul map on the two original module vectors. -/
def bilinear : CliffordPairModule B H →ₗ[ℂ]
    CliffordPairModule C F →ₗ[ℂ] TargetModule (H := H) φ where
  toFun x :=
    ((((interiorModuleTensorMk φ x.1).comp (plus J).toCLM.toLinearMap +
        (interiorModuleTensorMk φ x.2).comp (minus J).toCLM.toLinearMap).comp
          (LinearMap.fst ℂ F F)).prod
      (((interiorModuleTensorMk φ x.1).comp (minus J).toCLM.toLinearMap +
        (interiorModuleTensorMk φ x.2).comp (plus J).toCLM.toLinearMap).comp
          (LinearMap.snd ℂ F F)))
  map_add' x z := by
    apply LinearMap.ext
    intro y
    let x₁ : H := x.1
    let x₂ : H := x.2
    let z₁ : H := z.1
    let z₂ : H := z.2
    let y₁ : F := y.1
    let y₂ : F := y.2
    apply Prod.ext
    · change interiorModuleTensorMk φ (x₁ + z₁) (plus J y₁) +
        interiorModuleTensorMk φ (x₂ + z₂) (minus J y₁) =
        (interiorModuleTensorMk φ x₁ (plus J y₁) + interiorModuleTensorMk φ x₂ (minus J y₁)) +
        (interiorModuleTensorMk φ z₁ (plus J y₁) + interiorModuleTensorMk φ z₂ (minus J y₁))
      simp only [map_add, LinearMap.add_apply]
      abel
    · change interiorModuleTensorMk φ (x₁ + z₁) (minus J y₂) +
        interiorModuleTensorMk φ (x₂ + z₂) (plus J y₂) =
        (interiorModuleTensorMk φ x₁ (minus J y₂) + interiorModuleTensorMk φ x₂ (plus J y₂)) +
        (interiorModuleTensorMk φ z₁ (minus J y₂) + interiorModuleTensorMk φ z₂ (plus J y₂))
      simp only [map_add, LinearMap.add_apply]
      abel
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    let x₁ : H := x.1
    let x₂ : H := x.2
    let y₁ : F := y.1
    let y₂ : F := y.2
    apply Prod.ext
    · change interiorModuleTensorMk φ (a • x₁) (plus J y₁) +
        interiorModuleTensorMk φ (a • x₂) (minus J y₁) =
        a • (interiorModuleTensorMk φ x₁ (plus J y₁) + interiorModuleTensorMk φ x₂ (minus J y₁))
      simp only [map_smul, LinearMap.smul_apply, smul_add]
    · change interiorModuleTensorMk φ (a • x₁) (minus J y₂) +
        interiorModuleTensorMk φ (a • x₂) (plus J y₂) =
        a • (interiorModuleTensorMk φ x₁ (minus J y₂) + interiorModuleTensorMk φ x₂ (plus J y₂))
      simp only [map_smul, LinearMap.smul_apply, smul_add]

@[simp] theorem bilinear_apply (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    bilinear φ J x y = cliffordPairMk
      (interiorModuleTensorMk φ x.1 (plus J y.1) + interiorModuleTensorMk φ x.2 (minus J y.1))
      (interiorModuleTensorMk φ x.1 (minus J y.2) + interiorModuleTensorMk φ x.2 (plus J y.2)) := rfl

theorem bilinear_balance (b : B × B) (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    bilinear φ J (MulOpposite.op b • x) y = bilinear φ J x (representation φ J hφ b y) := by
  simp only [bilinear_apply, cliffordPair_smul, representation]
  apply Prod.ext
  · change interiorModuleTensorMk φ (MulOpposite.op b.1 • x.1) (plus J y.1) +
        interiorModuleTensorMk φ (MulOpposite.op b.2 • x.2) (minus J y.1) =
      interiorModuleTensorMk φ x.1 (plus J (halfRepresentation φ J hφ b y.1)) +
        interiorModuleTensorMk φ x.2 (minus J (halfRepresentation φ J hφ b y.1))
    rw [interiorModuleTensorMk_balance, interiorModuleTensorMk_balance,
      plus_half φ J hφ, minus_half φ J hφ]
  · change interiorModuleTensorMk φ (MulOpposite.op b.1 • x.1) (minus J y.2) +
        interiorModuleTensorMk φ (MulOpposite.op b.2 • x.2) (plus J y.2) =
      interiorModuleTensorMk φ x.1
        (minus J (halfRepresentation φ J hφ (cliffordCoefficientGrading.automorphism b) y.2)) +
      interiorModuleTensorMk φ x.2
        (plus J (halfRepresentation φ J hφ (cliffordCoefficientGrading.automorphism b) y.2))
    rw [interiorModuleTensorMk_balance, interiorModuleTensorMk_balance,
      minus_half φ J hφ, plus_half φ J hφ]; rfl

def balancedMap : BalancedModuleTensor (E := CliffordPairModule B H) (representation φ J hφ) →ₗ[ℂ]
    TargetModule (H := H) φ :=
  moduleTensorLift (representation φ J hφ) (bilinear φ J) (bilinear_balance φ J hφ)

@[simp] theorem balancedMap_mk (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    balancedMap φ J hφ (moduleTensorMk (representation φ J hφ) x y) = bilinear φ J x y := rfl

/-- Orthogonality proves both complete product-coefficient coordinates,
including every mixed term. -/
theorem bilinear_inner (x x' : CliffordPairModule B H) (y y' : CliffordPairModule C F) :
    ⟪bilinear φ J x y, bilinear φ J x' y'⟫_((C × C)ᵐᵒᵖ) =
      moduleTensorPureInner (representation φ J hφ) x y x' y' := by
  let x₁ : H := x.1
  let x₂ : H := x.2
  let x₁' : H := x'.1
  let x₂' : H := x'.2
  let y₁ : F := y.1
  let y₂ : F := y.2
  let y₁' : F := y'.1
  let y₂' : F := y'.2
  rw [bilinear_apply, bilinear_apply]
  apply MulOpposite.unop_injective
  apply Prod.ext
  · apply congrArg MulOpposite.unop
    change ⟪interiorModuleTensorMk φ x₁ (plus J y₁) +
        interiorModuleTensorMk φ x₂ (minus J y₁),
      interiorModuleTensorMk φ x₁' (plus J y₁') +
        interiorModuleTensorMk φ x₂' (minus J y₁')⟫_(Cᵐᵒᵖ) =
      ⟪y₁, halfRepresentation φ J hφ
        (MulOpposite.unop ⟪x₁, x₁'⟫_(Bᵐᵒᵖ), MulOpposite.unop ⟪x₂, x₂'⟫_(Bᵐᵒᵖ)) y₁'⟫_(Cᵐᵒᵖ)
    rw [CStarModule.inner_add_left (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := H) φ),
      CStarModule.inner_add_right (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := H) φ),
      CStarModule.inner_add_right (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := H) φ),
      halfRepresentation_eq]
    simp only [interiorModuleTensorInner_mk_mk, moduleTensorPureInner,
      inner_plus_plus φ J hφ, inner_plus_minus φ J hφ, inner_minus_plus φ J hφ,
      inner_minus_minus φ J hφ, add_zero, zero_add, AdjointableMap.coe_add_apply,
      AdjointableMap.mul_apply, CStarModule.inner_add_right]; rfl
  · apply congrArg MulOpposite.unop
    change ⟪interiorModuleTensorMk φ x₁ (minus J y₂) +
        interiorModuleTensorMk φ x₂ (plus J y₂),
      interiorModuleTensorMk φ x₁' (minus J y₂') +
        interiorModuleTensorMk φ x₂' (plus J y₂')⟫_(Cᵐᵒᵖ) =
      ⟪y₂, halfRepresentation φ J hφ
        (MulOpposite.unop ⟪x₂, x₂'⟫_(Bᵐᵒᵖ), MulOpposite.unop ⟪x₁, x₁'⟫_(Bᵐᵒᵖ)) y₂'⟫_(Cᵐᵒᵖ)
    rw [CStarModule.inner_add_left (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := H) φ),
      CStarModule.inner_add_right (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := H) φ),
      CStarModule.inner_add_right (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := H) φ),
      halfRepresentation_eq]
    simp only [interiorModuleTensorInner_mk_mk, moduleTensorPureInner,
      inner_plus_plus φ J hφ, inner_plus_minus φ J hφ, inner_minus_plus φ J hφ,
      inner_minus_minus φ J hφ, add_zero, zero_add, AdjointableMap.coe_add_apply,
      AdjointableMap.mul_apply, CStarModule.inner_add_right]; exact add_comm _ _

theorem balancedMap_inner
    (u v : BalancedModuleTensor (E := CliffordPairModule B H) (representation φ J hφ)) :
    ⟪balancedMap φ J hφ u, balancedMap φ J hφ v⟫_((C × C)ᵐᵒᵖ) =
      moduleTensorInner (representation φ J hφ) u v := by
  revert v
  refine moduleTensor_induction (representation φ J hφ) u ?_ ?_ ?_
  · intro v; simp
  · intro x y v
    refine moduleTensor_induction (representation φ J hφ) v ?_ ?_ ?_
    · simp
    · intro x' y'
      rw [balancedMap_mk, balancedMap_mk, moduleTensorInner_mk_mk]
      exact bilinear_inner φ J hφ x x' y y'
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u v hu hv w
    simp only [map_add, CStarModule.inner_add_left, hu, hv, LinearMap.add_apply]

/-- The full form-preserving balanced map descends through the actual null
radical and extends to the genuine Hilbert-module completion. -/
def isometry : SourceTensor (H := H) φ J hφ →ₗᵢ[ℂ] TargetModule (H := H) φ :=
  InteriorModuleTensorFormCompletion.completedIsometry (representation φ J hφ)
    (balancedMap φ J hφ) (balancedMap_inner φ J hφ)

@[simp] theorem isometry_mk (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    isometry φ J hφ (interiorModuleTensorMk (representation φ J hφ) x y) = bilinear φ J x y :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x y

theorem plus_add_minus_apply (y : F) : plus J y + minus J y = y := by
  have hh := congrArg (fun T : AdjointableMap C F F => T y) (plus_add_minus J)
  exact hh

theorem isometry_surjective : Function.Surjective (isometry (H := H) φ J hφ) := by
  let R : Submodule ℂ (TargetModule (H := H) φ) := (isometry (H := H) φ J hφ).toLinearMap.range
  have hR : IsClosed (R : Set (TargetModule (H := H) φ)) :=
    (isometry φ J hφ).isometry.isUniformInducing.isComplete_range.isClosed
  have hleft (z : InteriorModuleTensor (E := H) φ) :
      cliffordPairMk z (0 : InteriorModuleTensor (E := H) φ) ∈ R := by
    let L : InteriorModuleTensor (E := H) φ →L[ℂ] TargetModule (H := H) φ :=
      ContinuousLinearMap.inl ℂ _ _
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set (InteriorModuleTensor (E := H) φ)) := hR.preimage L.continuous
    have hspan : Submodule.span ℂ (Set.range fun p : H × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      refine ⟨interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk x 0) (cliffordPairMk y 0) +
        interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk 0 x) (cliffordPairMk y 0), ?_⟩
      change isometry (H := H) φ J hφ
        (interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk x 0) (cliffordPairMk y 0) +
          interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk 0 x) (cliffordPairMk y 0)) =
        cliffordPairMk (B := C) (interiorModuleTensorMk (E := H) φ x y) 0
      rw [map_add, isometry_mk, isometry_mk, bilinear_apply, bilinear_apply]
      apply Prod.ext
      · change interiorModuleTensorMk φ x (plus J y) + interiorModuleTensorMk φ 0 (minus J y) +
          (interiorModuleTensorMk φ 0 (plus J y) + interiorModuleTensorMk φ x (minus J y)) =
          interiorModuleTensorMk φ x y
        simp only [map_zero, LinearMap.zero_apply, add_zero, zero_add]
        rw [← map_add, plus_add_minus_apply]
      · change interiorModuleTensorMk (E := H) φ x (minus J 0) +
          interiorModuleTensorMk φ 0 (plus J 0) +
          (interiorModuleTensorMk φ 0 (minus J 0) + interiorModuleTensorMk φ x (plus J 0)) = 0
        simp only [map_zero, add_zero]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  have hright (z : InteriorModuleTensor (E := H) φ) :
      cliffordPairMk (0 : InteriorModuleTensor (E := H) φ) z ∈ R := by
    let L : InteriorModuleTensor (E := H) φ →L[ℂ] TargetModule (H := H) φ :=
      ContinuousLinearMap.inr ℂ _ _
    let P := R.comap L.toLinearMap
    have hP : IsClosed (P : Set (InteriorModuleTensor (E := H) φ)) := hR.preimage L.continuous
    have hspan : Submodule.span ℂ (Set.range fun p : H × F => interiorModuleTensorMk φ p.1 p.2) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      refine ⟨interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk x 0) (cliffordPairMk 0 y) +
        interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk 0 x) (cliffordPairMk 0 y), ?_⟩
      change isometry (H := H) φ J hφ
        (interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk x 0) (cliffordPairMk 0 y) +
          interiorModuleTensorMk (representation φ J hφ) (cliffordPairMk 0 x) (cliffordPairMk 0 y)) =
        cliffordPairMk (B := C) 0 (interiorModuleTensorMk (E := H) φ x y)
      rw [map_add, isometry_mk, isometry_mk, bilinear_apply, bilinear_apply]
      apply Prod.ext
      · change interiorModuleTensorMk (E := H) φ x (plus J 0) +
          interiorModuleTensorMk φ 0 (minus J 0) +
          (interiorModuleTensorMk φ 0 (plus J 0) + interiorModuleTensorMk φ x (minus J 0)) = 0
        simp only [map_zero, add_zero]
      · change interiorModuleTensorMk φ x (minus J y) + interiorModuleTensorMk φ 0 (plus J y) +
          (interiorModuleTensorMk φ 0 (minus J y) + interiorModuleTensorMk φ x (plus J y)) =
          interiorModuleTensorMk φ x y
        simp only [map_zero, LinearMap.zero_apply, add_zero, zero_add]
        rw [add_comm, ← map_add, plus_add_minus_apply]
    change z ∈ P
    exact closure_minimal hspan hP (interiorModuleTensor_span_dense φ z)
  intro z
  change z ∈ R
  have hh := R.add_mem (hleft z.1) (hright z.2)
  have hz : cliffordPairMk (B := C) z.1 0 + cliffordPairMk (B := C) 0 z.2 = z := by
    change (z.1, (0 : InteriorModuleTensor (E := H) φ)) + (0, z.2) = (z.1, z.2)
    exact Prod.ext (add_zero _) (zero_add _)
  rw [hz] at hh
  exact hh

/-- The actual completed balanced tensor unitary, preserving both full
coefficient coordinates and attaining every completion vector. -/
def hilbertEquiv : HilbertModuleEquiv (C × C) (SourceTensor (H := H) φ J hφ)
    (TargetModule (H := H) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (isometry φ J hφ) (isometry_surjective φ J hφ)
  inner_map := InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _

@[simp] theorem hilbertEquiv_mk (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    hilbertEquiv φ J hφ (interiorModuleTensorMk (representation φ J hφ) x y) = cliffordPairMk
      (interiorModuleTensorMk φ x.1 (plus J y.1) + interiorModuleTensorMk φ x.2 (minus J y.1))
      (interiorModuleTensorMk φ x.1 (minus J y.2) + interiorModuleTensorMk φ x.2 (plus J y.2)) :=
  isometry_mk φ J hφ x y

end BC4lean.KKTheory.CliffordExternalEvenBalancedTensor
