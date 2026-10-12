import BC4lean.CliffordExternalEvenBalancedCreation
import BC4lean.CliffordExternalEvenCycle
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # The genuine Koszul grading and operators on the balanced Clifford tensor

The target involution is K = 1 ⊗ J on the original interior tensor, with
coordinate grading swap(K). The first signed operator transports to
(AK, −AK), where A = F ⊗ 1. This is derived on pure tensors and extended
to every completion vector. The source action and representation also
intertwine through the same whole coefficient-form unitary.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenBalancedTensor
open CliffordExternalEvenRepresentation

variable {B C H F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)
  (hφ : ∀ b, J.toAdjointable * φ b = φ b * J.toAdjointable)

include hφ in
omit [PartialOrder B] [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace F] in
theorem representation_even (b : B) (y : F) :
    J.grading (φ b y) = φ b (J.grading y) :=
  congrArg (fun T : AdjointableMap C F F => T y) (hφ b)

def tensorGrading : GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
    (InteriorModuleTensor (E := H) φ) :=
  (GradedHilbertModule.trivial (B := B) (E := H)).interiorTensor
    (φ := φ) J (representation_even φ J hφ)

@[simp] theorem tensorGrading_mk (x : H) (y : F) :
    (tensorGrading (H := H) φ J hφ).grading (interiorModuleTensorMk φ x y) =
      interiorModuleTensorMk φ x (J.grading y) :=
  GradedHilbertModule.interiorTensor_grading_mk _ _ _ x y

theorem grading_mul_plus : J.toAdjointable * plus J = plus J := by
  have hJ : J.toAdjointable * J.toAdjointable = 1 := grading_square J
  simp only [plus, CliffordOne.plusProjection, mul_smul_comm, mul_add, mul_one,
    hJ]
  exact congrArg (fun T : AdjointableMap C F F => (2 : ℂ)⁻¹ • T)
    (add_comm J.toAdjointable 1)

theorem grading_mul_minus : J.toAdjointable * minus J = -(minus J) := by
  have hJ : J.toAdjointable * J.toAdjointable = 1 := grading_square J
  simp only [minus, CliffordOne.minusProjection, mul_smul_comm, mul_sub, mul_one,
    hJ]
  rw [← smul_neg]
  exact congrArg (fun T : AdjointableMap C F F => (2 : ℂ)⁻¹ • T)
    (show J.toAdjointable - 1 = -(1 - J.toAdjointable) from by abel)

theorem plus_mul_grading : plus J * J.toAdjointable = plus J :=
  (grading_commutes_plus J).symm.trans (grading_mul_plus J)

theorem minus_mul_grading : minus J * J.toAdjointable = -(minus J) :=
  (grading_commutes_minus J).symm.trans (grading_mul_minus J)

@[simp] theorem grading_plus_apply (y : F) : J.grading (plus J y) = plus J y :=
  congrArg (fun T : AdjointableMap C F F => T y) (grading_mul_plus J)

@[simp] theorem grading_minus_apply (y : F) : J.grading (minus J y) = -(minus J y) := by
  have h := congrArg (fun T : AdjointableMap C F F => T y) (grading_mul_minus J)
  change J.grading (minus J y) = (-minus J) y at h
  rw [AdjointableMap.coe_neg_apply] at h
  exact h

@[simp] theorem plus_grading_apply (y : F) : plus J (J.grading y) = plus J y :=
  congrArg (fun T : AdjointableMap C F F => T y) (plus_mul_grading J)

@[simp] theorem minus_grading_apply (y : F) : minus J (J.grading y) = -(minus J y) := by
  have h := congrArg (fun T : AdjointableMap C F F => T y) (minus_mul_grading J)
  change minus J (J.grading y) = (-minus J) y at h
  rw [AdjointableMap.coe_neg_apply] at h
  exact h

omit [PartialOrder B] [StarOrderedRing B] in
theorem external_representation_graded (b : B × B) (y : CliffordPairModule C F) :
    (cliffordExternalEvenGrading J).grading (representation φ J hφ b y) =
      representation φ J hφ (cliffordCoefficientGrading.automorphism b)
        ((cliffordExternalEvenGrading J).grading y) := by
  apply Prod.ext
  · exact congrArg (fun T : AdjointableMap C F F => T y.2)
      (grading_commutes_half φ J hφ (cliffordCoefficientGrading.automorphism b))
  · change J.grading (halfRepresentation φ J hφ b y.1) =
      halfRepresentation φ J hφ
        (cliffordCoefficientGrading.automorphism
          (cliffordCoefficientGrading.automorphism b)) (J.grading y.1)
    rw [CStarGrading.automorphism_sq]
    exact congrArg (fun T : AdjointableMap C F F => T y.1)
      (grading_commutes_half φ J hφ b)

def sourceGrading : GradedHilbertModule (cliffordCoefficientGrading (B := C))
    (SourceTensor (H := H) φ J hφ) :=
  (cliffordPairGrading (B := B) (H := H)).interiorTensor
    (φ := representation φ J hφ) (cliffordExternalEvenGrading J)
    (external_representation_graded φ J hφ)

def targetGrading : GradedHilbertModule (cliffordCoefficientGrading (B := C))
    (TargetModule (H := H) φ) :=
  cliffordExternalEvenGrading (tensorGrading (H := H) φ J hφ)

theorem bilinear_grading (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    bilinear φ J ((cliffordPairGrading (B := B) (H := H)).grading x)
      ((cliffordExternalEvenGrading J).grading y) =
    (targetGrading (H := H) φ J hφ).grading (bilinear φ J x y) := by
  change bilinear φ J (cliffordPairMk x.2 x.1) (cliffordPairMk (J.grading y.2) (J.grading y.1)) =
    cliffordPairMk ((tensorGrading (H := H) φ J hφ).grading (bilinear φ J x y).2)
      ((tensorGrading (H := H) φ J hφ).grading (bilinear φ J x y).1)
  apply Prod.ext
  · change interiorModuleTensorMk φ x.2 (plus J (J.grading y.2)) +
      interiorModuleTensorMk φ x.1 (minus J (J.grading y.2)) =
      (tensorGrading (H := H) φ J hφ).grading
        (interiorModuleTensorMk φ x.1 (minus J y.2) +
          interiorModuleTensorMk φ x.2 (plus J y.2))
    rw [plus_grading_apply, minus_grading_apply, map_add, tensorGrading_mk,
      tensorGrading_mk, grading_minus_apply, grading_plus_apply]
    simp only [map_neg]
    abel
  · change interiorModuleTensorMk φ x.2 (minus J (J.grading y.1)) +
      interiorModuleTensorMk φ x.1 (plus J (J.grading y.1)) =
      (tensorGrading (H := H) φ J hφ).grading
        (interiorModuleTensorMk φ x.1 (plus J y.1) +
          interiorModuleTensorMk φ x.2 (minus J y.1))
    rw [minus_grading_apply, plus_grading_apply, map_add, tensorGrading_mk,
      tensorGrading_mk, grading_plus_apply, grading_minus_apply]
    simp only [map_neg]
    abel

theorem hilbertEquiv_grading (z : SourceTensor (H := H) φ J hφ) :
    hilbertEquiv φ J hφ ((sourceGrading (H := H) φ J hφ).grading z) =
      (targetGrading (H := H) φ J hφ).grading (hilbertEquiv φ J hφ z) := by
  let W := (hilbertEquiv (H := H) φ J hφ).toAdjointable.toCLM
  let L := (sourceGrading (H := H) φ J hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (targetGrading (H := H) φ J hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp L = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ J hφ ((sourceGrading (H := H) φ J hφ).grading
      (interiorModuleTensorMk (representation φ J hφ) x y)) =
      (targetGrading (H := H) φ J hφ).grading
        (hilbertEquiv φ J hφ (interiorModuleTensorMk (representation φ J hφ) x y))
    have hrepr : ModuleTensorRepresentationGraded
        (δB := cliffordCoefficientGrading (B := B))
        (representation φ J hφ) (cliffordExternalEvenGrading J) :=
      fun b v => external_representation_graded φ J hφ b v
    have hsource := GradedHilbertModule.interiorTensor_grading_mk
      (φ := representation φ J hφ) (cliffordPairGrading (B := B) (H := H))
      (cliffordExternalEvenGrading J) hrepr x y
    change (sourceGrading (H := H) φ J hφ).grading
        (interiorModuleTensorMk (representation φ J hφ) x y) =
      interiorModuleTensorMk (representation φ J hφ)
        ((cliffordPairGrading (B := B) (H := H)).grading x)
        ((cliffordExternalEvenGrading J).grading y) at hsource
    rw [hsource, hilbertEquiv_mk, hilbertEquiv_mk]
    exact bilinear_grading φ J hφ x y
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_diagonal_operator (S : AdjointableMap B H H)
    (z : SourceTensor (H := H) φ J hφ) :
    hilbertEquiv φ J hφ (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S S) z) =
      cliffordPairMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ S)
        (hilbertEquiv φ J hφ z) := by
  let W := (hilbertEquiv (H := H) φ J hφ).toAdjointable.toCLM
  have h : W.comp (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S S)).toCLM =
      (cliffordPairMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ S)).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ J hφ
      (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S S)
        (interiorModuleTensorMk (representation φ J hφ) x y)) =
      cliffordPairMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ S)
        (hilbertEquiv φ J hφ (interiorModuleTensorMk (representation φ J hφ) x y))
    rw [interiorModuleTensorOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext
    · change interiorModuleTensorMk φ (S x.1) (plus J y.1) +
        interiorModuleTensorMk φ (S x.2) (minus J y.1) =
        interiorModuleTensorOperator φ S
          (interiorModuleTensorMk φ x.1 (plus J y.1) +
            interiorModuleTensorMk φ x.2 (minus J y.1))
      rw [map_add, interiorModuleTensorOperator_mk, interiorModuleTensorOperator_mk]
    · change interiorModuleTensorMk φ (S x.1) (minus J y.2) +
        interiorModuleTensorMk φ (S x.2) (plus J y.2) =
        interiorModuleTensorOperator φ S
          (interiorModuleTensorMk φ x.1 (minus J y.2) +
            interiorModuleTensorMk φ x.2 (plus J y.2))
      rw [map_add, interiorModuleTensorOperator_mk, interiorModuleTensorOperator_mk]
  exact DFunLike.congr_fun h z

theorem hilbertEquiv_signed_operator (S : AdjointableMap B H H)
    (z : SourceTensor (H := H) φ J hφ) :
    hilbertEquiv φ J hφ
      (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S (-S)) z) =
    cliffordPairMap
      (interiorModuleTensorOperator φ S * (tensorGrading (H := H) φ J hφ).toAdjointable)
      (-(interiorModuleTensorOperator φ S * (tensorGrading (H := H) φ J hφ).toAdjointable))
      (hilbertEquiv φ J hφ z) := by
  let W := (hilbertEquiv (H := H) φ J hφ).toAdjointable.toCLM
  let A := interiorModuleTensorOperator φ S * (tensorGrading (H := H) φ J hφ).toAdjointable
  have hA (u : H) (v : F) :
      A (interiorModuleTensorMk φ u v) = interiorModuleTensorMk φ (S u) (J.grading v) := by
    change interiorModuleTensorOperator φ S
      ((tensorGrading (H := H) φ J hφ).grading (interiorModuleTensorMk φ u v)) = _
    rw [tensorGrading_mk, interiorModuleTensorOperator_mk]
  have hneg (u : H) (v : F) :
      interiorModuleTensorMk φ (-u) v = -interiorModuleTensorMk φ u v :=
    ((interiorModuleTensorMk φ).flip v).map_neg u
  have h : W.comp (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S (-S))).toCLM =
      (cliffordPairMap A (-A)).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ J hφ
      (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S (-S))
        (interiorModuleTensorMk (representation φ J hφ) x y)) =
      cliffordPairMap A (-A)
        (hilbertEquiv φ J hφ (interiorModuleTensorMk (representation φ J hφ) x y))
    rw [interiorModuleTensorOperator_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext
    · change interiorModuleTensorMk φ (S x.1) (plus J y.1) +
        interiorModuleTensorMk φ ((-S) x.2) (minus J y.1) =
        A (interiorModuleTensorMk φ x.1 (plus J y.1) +
          interiorModuleTensorMk φ x.2 (minus J y.1))
      rw [AdjointableMap.coe_neg_apply, hneg, map_add, hA, hA,
        grading_plus_apply, grading_minus_apply, map_neg]
    · change interiorModuleTensorMk φ (S x.1) (minus J y.2) +
        interiorModuleTensorMk φ ((-S) x.2) (plus J y.2) =
        (-A) (interiorModuleTensorMk φ x.1 (minus J y.2) +
          interiorModuleTensorMk φ x.2 (plus J y.2))
      simp only [AdjointableMap.coe_neg_apply]
      rw [hneg, map_add, hA, hA, grading_minus_apply, grading_plus_apply, map_neg]
      abel
  exact DFunLike.congr_fun h z

theorem transport_diagonal_operator (S : AdjointableMap B H H) :
    (hilbertEquiv (H := H) φ J hφ).transport
      (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S S)) =
    cliffordPairMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ S) := by
  ext z
  obtain ⟨w, rfl⟩ := (hilbertEquiv (H := H) φ J hφ).surjective z
  rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
  exact hilbertEquiv_diagonal_operator φ J hφ S w

theorem transport_signed_operator (S : AdjointableMap B H H) :
    (hilbertEquiv (H := H) φ J hφ).transport
      (interiorModuleTensorOperator (representation φ J hφ) (cliffordPairMap S (-S))) =
    cliffordPairMap
      (interiorModuleTensorOperator φ S * (tensorGrading (H := H) φ J hφ).toAdjointable)
      (-(interiorModuleTensorOperator φ S * (tensorGrading (H := H) φ J hφ).toAdjointable)) := by
  ext z
  obtain ⟨w, rfl⟩ := (hilbertEquiv (H := H) φ J hφ).surjective z
  rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
  exact hilbertEquiv_signed_operator φ J hφ S w

variable {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (U : EquivariantHilbertModule β H) (V : EquivariantHilbertModule γ F)
  (hV : V.PreservesGrading J)
  (hact : ModuleTensorRepresentationEquivariant φ β V)
  (hactPair : ModuleTensorRepresentationEquivariant (representation φ J hφ)
    (cliffordCoefficientAction β) (cliffordPairAction V))

omit [StarOrderedRing B] [CompleteSpace H] in
@[simp] theorem pairAction_apply (g : Γ) (x : CliffordPairModule B H) :
    (cliffordPairAction U).action g x = cliffordPairMk (U.action g x.1) (U.action g x.2) := rfl

include hV in
theorem plus_action (g : Γ) (y : F) : plus J (V.action g y) = V.action g (plus J y) := by
  simp only [plus, CliffordOne.plusProjection, AdjointableMap.coe_smul_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.one_apply, GradedHilbertModule.toAdjointable_apply,
    ← hV g y, map_smul, map_add]

include hV in
theorem minus_action (g : Γ) (y : F) : minus J (V.action g y) = V.action g (minus J y) := by
  simp only [minus, CliffordOne.minusProjection, AdjointableMap.coe_smul_apply,
    AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, GradedHilbertModule.toAdjointable_apply,
    ← hV g y, map_smul, map_sub]

include hV in
theorem hilbertEquiv_action (g : Γ) (z : SourceTensor (H := H) φ J hφ) :
    hilbertEquiv φ J hφ
      (((cliffordPairAction U).interiorTensor (cliffordPairAction V) hactPair).action g z) =
    (cliffordPairAction (U.interiorTensor V hact)).action g (hilbertEquiv φ J hφ z) := by
  let W := (hilbertEquiv (H := H) φ J hφ).toAdjointable.toCLM
  let L := (((cliffordPairAction U).interiorTensor (cliffordPairAction V) hactPair).action g).toContinuousLinearEquiv.toContinuousLinearMap
  let K := ((cliffordPairAction (U.interiorTensor V hact)).action g).toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp L = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv φ J hφ
      ((((cliffordPairAction U).interiorTensor (cliffordPairAction V) hactPair).action g)
        (interiorModuleTensorMk (representation φ J hφ) x y)) =
      (cliffordPairAction (U.interiorTensor V hact)).action g
        (hilbertEquiv φ J hφ (interiorModuleTensorMk (representation φ J hφ) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext
    · change interiorModuleTensorMk φ (U.action g x.1) (plus J (V.action g y.1)) +
        interiorModuleTensorMk φ (U.action g x.2) (minus J (V.action g y.1)) =
        (U.interiorTensor V hact).action g
          (interiorModuleTensorMk φ x.1 (plus J y.1) +
            interiorModuleTensorMk φ x.2 (minus J y.1))
      rw [plus_action J V hV, minus_action J V hV, map_add,
        EquivariantHilbertModule.interiorTensor_action_mk,
        EquivariantHilbertModule.interiorTensor_action_mk]
    · change interiorModuleTensorMk φ (U.action g x.1) (minus J (V.action g y.2)) +
        interiorModuleTensorMk φ (U.action g x.2) (plus J (V.action g y.2)) =
        (U.interiorTensor V hact).action g
          (interiorModuleTensorMk φ x.1 (minus J y.2) +
            interiorModuleTensorMk φ x.2 (plus J y.2))
      rw [minus_action J V hV, plus_action J V hV, map_add,
        EquivariantHilbertModule.interiorTensor_action_mk,
        EquivariantHilbertModule.interiorTensor_action_mk]
  exact DFunLike.congr_fun h z

end BC4lean.KKTheory.CliffordExternalEvenBalancedTensor
