import BC4lean.FiniteHilbertModuleSum
import BC4lean.RectangularInteriorModuleTensorOperator

/-! # Actual interior tensoring of a finite Hilbert-module sum

The forward coordinates are the completed tensors of the actual coordinate
evaluations. The inverse is the finite sum of the completed coordinate
inclusions. These are genuine adjoint pairs and inverse maps on whole vectors,
so the equivalence preserves the coefficient-valued form and intertwines the
actual finite matrix operators. No essentiality of the left representation is
required.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace
open RectangularInteriorModuleTensorOperator

variable {B C E F ι : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] [Fintype ι] [DecidableEq ι]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance standardFiniteHilbertModuleTensorLocalInstance01 : CompleteSpace (FiniteHilbertModuleSum B E ι) :=
  finiteHilbertModuleSum_complete
local instance standardFiniteHilbertModuleTensorLocalInstance02 : CompleteSpace (FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι) :=
  finiteHilbertModuleSum_complete

def finiteHilbertModuleTensorForward :
    InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ →L[ℂ]
      FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι :=
  LinearMap.mkContinuous
    { toFun z := (WithCStarModule.equiv _ _).symm
        (fun i => tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) z)
      map_add' z w := by
        ext i
        change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) (z + w) =
          tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) z +
          tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) w
        exact (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)).toCLM.map_add z w
      map_smul' a z := by
        ext i
        change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) (a • z) =
          a • tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) z
        exact (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)).toCLM.map_smul a z }
    (∑ i : ι, ‖tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)‖)
    (fun z => by
      calc
        ‖(WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ)).symm
            (fun i => tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) z)‖
            ≤ ∑ i : ι, ‖tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) z‖ :=
          WithCStarModule.pi_norm_le_sum_norm _
        _ ≤ ∑ i : ι, ‖tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)‖ * ‖z‖ :=
          Finset.sum_le_sum (fun i _ =>
            (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)).toCLM.le_opNorm z)
        _ = _ := (Finset.sum_mul _ _ _).symm)

@[simp] theorem finiteHilbertModuleTensorForward_apply
    (z : InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ) (i : ι) :
    finiteHilbertModuleTensorForward φ z i = tensor φ (finiteHilbertModuleEvaluation i) z := rfl

@[simp] theorem finiteHilbertModuleTensorForward_mk
    (x : FiniteHilbertModuleSum B E ι) (y : F) (i : ι) :
    finiteHilbertModuleTensorForward φ (interiorModuleTensorMk φ x y) i =
      interiorModuleTensorMk φ (x i) y := by
  rw [finiteHilbertModuleTensorForward_apply, tensor_mk, finiteHilbertModuleEvaluation_apply]

def finiteHilbertModuleTensorReverse :
    FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι →L[ℂ]
      InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ :=
  ∑ i : ι, (tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i)).toCLM.comp
    (finiteHilbertModuleEvaluationCLM (B := C) (E := InteriorModuleTensor (E := E) φ) i)

@[simp] theorem finiteHilbertModuleTensorReverse_apply
    (x : FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι) :
    finiteHilbertModuleTensorReverse φ x = ∑ i : ι, tensor φ (finiteHilbertModuleInclusion i) (x i) := by
  simp only [finiteHilbertModuleTensorReverse, _root_.sum_apply,
    ContinuousLinearMap.comp_apply]
  rfl

theorem finiteHilbertModuleTensor_adjoint_identity
    (z : InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ)
    (x : FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι) :
    ⟪finiteHilbertModuleTensorForward φ z, x⟫_(Cᵐᵒᵖ) =
      ⟪z, finiteHilbertModuleTensorReverse φ x⟫_(Cᵐᵒᵖ) := by
  let cx : ι → InteriorModuleTensor (E := E) φ :=
    WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ) x
  change (∑ i : ι, ⟪tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) z, cx i⟫_(Cᵐᵒᵖ)) =
    ⟪z, finiteHilbertModuleTensorReverse (ι := ι) φ x⟫_(Cᵐᵒᵖ)
  have hx : finiteHilbertModuleTensorReverse (ι := ι) φ x =
      ∑ i : ι, tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i) (cx i) :=
    finiteHilbertModuleTensorReverse_apply φ x
  rw [hx, CStarModule.inner_sum_right
    (A := Cᵐᵒᵖ) (E := InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ)]
  exact Finset.sum_congr rfl (fun i _ =>
    (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)).adjoint_identity z (cx i))

theorem finiteHilbertModuleTensor_reverse_forward
    (z : InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ) :
    finiteHilbertModuleTensorReverse φ (finiteHilbertModuleTensorForward φ z) = z := by
  have h : (finiteHilbertModuleTensorReverse (E := E) (ι := ι) φ).comp
      (finiteHilbertModuleTensorForward (E := E) (ι := ι) φ) =
      ContinuousLinearMap.id ℂ (InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    let cx : ι → E := WithCStarModule.equiv Bᵐᵒᵖ (ι → E) x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      finiteHilbertModuleTensorReverse_apply]
    simp only [finiteHilbertModuleTensorForward_apply]
    change (∑ i : ι, tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i)
      (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
        (interiorModuleTensorMk φ x y))) = interiorModuleTensorMk φ x y
    have hi (i : ι) :
        tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i)
          (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
            (interiorModuleTensorMk (E := FiniteHilbertModuleSum B E ι) φ x y)) =
        interiorModuleTensorMk (E := FiniteHilbertModuleSum B E ι) φ
          (finiteHilbertModuleSingle (B := B) i (cx i)) y := by
      calc
        _ = tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i)
            (interiorModuleTensorMk (E := E) φ
              (finiteHilbertModuleEvaluation (B := B) (E := E) i x) y) :=
          congrArg (fun v : InteriorModuleTensor (E := E) φ =>
            tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i) v)
              (tensor_mk φ (finiteHilbertModuleEvaluation (B := B) (E := E) i) x y)
        _ = interiorModuleTensorMk (E := FiniteHilbertModuleSum B E ι) φ
            (finiteHilbertModuleInclusion (B := B) (E := E) i
              (finiteHilbertModuleEvaluation (B := B) (E := E) i x)) y :=
          tensor_mk φ (finiteHilbertModuleInclusion (B := B) (E := E) i)
            (finiteHilbertModuleEvaluation (B := B) (E := E) i x) y
        _ = _ := rfl
    have hs : (∑ i : ι, finiteHilbertModuleSingle (B := B) i (cx i)) = x := by
      apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → E)).injective
      change (∑ j : ι, (Pi.single j (cx j) : ι → E)) = cx
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    calc
      _ = (∑ i : ι, interiorModuleTensorMk (E := FiniteHilbertModuleSum B E ι) φ
          (finiteHilbertModuleSingle (B := B) i (cx i)) y) :=
        Finset.sum_congr rfl (fun i _ => hi i)
      _ = interiorModuleTensorMk φ x y := by
        change (∑ i : ι, ((interiorModuleTensorMk
          (E := FiniteHilbertModuleSum B E ι) φ).flip y)
          (finiteHilbertModuleSingle (B := B) i (cx i))) =
          ((interiorModuleTensorMk (E := FiniteHilbertModuleSum B E ι) φ).flip y) x
        rw [← map_sum ((interiorModuleTensorMk
          (E := FiniteHilbertModuleSum B E ι) φ).flip y), hs]
  exact congrArg (fun L : InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ →L[ℂ]
    InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ => L z) h

theorem finiteHilbertModuleTensor_evaluation_inclusion (i j : ι)
    (z : InteriorModuleTensor (E := E) φ) :
    tensor φ (finiteHilbertModuleEvaluation i) (tensor φ (finiteHilbertModuleInclusion j) z) =
      if i = j then z else 0 := by
  by_cases hij : i = j
  · subst j
    have h : (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)).toCLM.comp
        (tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i)).toCLM =
        ContinuousLinearMap.id ℂ (InteriorModuleTensor (E := E) φ) := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
        (tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i)
          (interiorModuleTensorMk φ x y)) = interiorModuleTensorMk φ x y
      rw [tensor_mk, tensor_mk]
      change interiorModuleTensorMk φ ((Pi.single i x : ι → E) i) y = interiorModuleTensorMk φ x y
      rw [Pi.single_eq_same]
    have hz := congrArg (fun L : InteriorModuleTensor (E := E) φ →L[ℂ]
      InteriorModuleTensor (E := E) φ => L z) h
    change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
      (tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) i) z) = z at hz
    rw [if_pos rfl]
    exact hz
  · have h : (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)).toCLM.comp
        (tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) j)).toCLM = 0 := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
        (tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) j)
          (interiorModuleTensorMk φ x y)) = 0
      rw [tensor_mk, tensor_mk]
      change interiorModuleTensorMk φ ((Pi.single j x : ι → E) i) y = 0
      rw [Pi.single_eq_of_ne hij]
      exact map_zero ((interiorModuleTensorMk (E := E) φ).flip y)
    have hz := congrArg (fun L : InteriorModuleTensor (E := E) φ →L[ℂ]
      InteriorModuleTensor (E := E) φ => L z) h
    change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
      (tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) j) z) = 0 at hz
    rw [if_neg hij]
    exact hz

theorem finiteHilbertModuleTensor_forward_reverse
    (x : FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι) :
    finiteHilbertModuleTensorForward φ (finiteHilbertModuleTensorReverse φ x) = x := by
  apply (WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ)).injective
  funext i
  let cx : ι → InteriorModuleTensor (E := E) φ :=
    WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ) x
  change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
    (finiteHilbertModuleTensorReverse (ι := ι) φ x) = cx i
  have hx : finiteHilbertModuleTensorReverse (ι := ι) φ x =
      ∑ j : ι, tensor φ (finiteHilbertModuleInclusion (B := B) (E := E) j) (cx j) :=
    finiteHilbertModuleTensorReverse_apply φ x
  rw [hx, adjointable_finset_sum]
  simp only [finiteHilbertModuleTensor_evaluation_inclusion]
  simp

def finiteHilbertModuleTensorEquiv :
    HilbertModuleEquiv C (InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ)
      (FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := finiteHilbertModuleTensorForward φ
          invFun := finiteHilbertModuleTensorReverse φ
          left_inv := finiteHilbertModuleTensor_reverse_forward φ
          right_inv := finiteHilbertModuleTensor_forward_reverse φ
          map_add' := (finiteHilbertModuleTensorForward φ).map_add
          map_smul' := (finiteHilbertModuleTensorForward φ).map_smul }
      norm_map' z := by
        change ‖finiteHilbertModuleTensorForward (ι := ι) φ z‖ = ‖z‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ),
          finiteHilbertModuleTensor_adjoint_identity, finiteHilbertModuleTensor_reverse_forward]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) z).symm }
  inner_map z w := by
    change ⟪finiteHilbertModuleTensorForward (ι := ι) φ z,
      finiteHilbertModuleTensorForward (ι := ι) φ w⟫_(Cᵐᵒᵖ) = ⟪z, w⟫_(Cᵐᵒᵖ)
    rw [finiteHilbertModuleTensor_adjoint_identity, finiteHilbertModuleTensor_reverse_forward]

@[simp] theorem finiteHilbertModuleTensorEquiv_mk
    (x : FiniteHilbertModuleSum B E ι) (y : F) (i : ι) :
    finiteHilbertModuleTensorEquiv φ (interiorModuleTensorMk φ x y) i =
      interiorModuleTensorMk φ (x i) y := finiteHilbertModuleTensorForward_mk φ x y i

@[simp] theorem finiteHilbertModuleTensorEquiv_apply
    (z : InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ) (i : ι) :
    finiteHilbertModuleTensorEquiv φ z i = tensor φ (finiteHilbertModuleEvaluation i) z := rfl

theorem finiteHilbertModuleTensorEquiv_operatorMatrix
    (T : Matrix ι ι (AdjointableMap B E E))
    (z : InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ) :
    finiteHilbertModuleTensorEquiv φ (interiorModuleTensorOperator φ (finiteHilbertModuleOperatorMatrix T) z) =
      finiteHilbertModuleOperatorMatrix (fun i j => interiorModuleTensorOperator φ (T i j))
        (finiteHilbertModuleTensorEquiv φ z) := by
  have h : (finiteHilbertModuleTensorForward (E := E) (ι := ι) φ).comp
      (interiorModuleTensorOperator φ (finiteHilbertModuleOperatorMatrix T)).toCLM =
      (finiteHilbertModuleOperatorMatrix (fun i j => interiorModuleTensorOperator φ (T i j))).toCLM.comp
        (finiteHilbertModuleTensorForward (E := E) (ι := ι) φ) := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    apply (WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ)).injective
    funext i
    let cx : ι → E := WithCStarModule.equiv Bᵐᵒᵖ (ι → E) x
    have hm : (finiteHilbertModuleOperatorMatrix T x) i = ∑ j : ι, T i j (cx j) :=
      finiteHilbertModuleOperatorMatrix_apply T x i
    change (WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ)
        (finiteHilbertModuleTensorForward (ι := ι) φ
          (interiorModuleTensorOperator φ (finiteHilbertModuleOperatorMatrix T)
            (interiorModuleTensorMk φ x y)))) i =
      (WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ)
        (finiteHilbertModuleOperatorMatrix (fun i j => interiorModuleTensorOperator φ (T i j))
          (finiteHilbertModuleTensorForward (ι := ι) φ (interiorModuleTensorMk φ x y)))) i
    calc
      _ = interiorModuleTensorMk φ ((finiteHilbertModuleOperatorMatrix T x) i) y := by
        change tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) i)
          (interiorModuleTensorOperator φ (finiteHilbertModuleOperatorMatrix T)
            (interiorModuleTensorMk φ x y)) =
          interiorModuleTensorMk φ ((finiteHilbertModuleOperatorMatrix T x) i) y
        rw [interiorModuleTensorOperator_mk, tensor_mk]; rfl
      _ = interiorModuleTensorMk φ (∑ j : ι, T i j (cx j)) y :=
        congrArg (fun v : E => interiorModuleTensorMk (E := E) φ v y) hm
      _ = ∑ j : ι, interiorModuleTensorMk φ (T i j (cx j)) y :=
        map_sum ((interiorModuleTensorMk (E := E) φ).flip y) _ _
      _ = _ := by
        have hr : (WithCStarModule.equiv Cᵐᵒᵖ (ι → InteriorModuleTensor (E := E) φ)
            (finiteHilbertModuleOperatorMatrix (fun i j => interiorModuleTensorOperator φ (T i j))
              (finiteHilbertModuleTensorForward (ι := ι) φ (interiorModuleTensorMk φ x y)))) i =
            ∑ j : ι, interiorModuleTensorOperator φ (T i j)
              (tensor φ (finiteHilbertModuleEvaluation (B := B) (E := E) j)
                (interiorModuleTensorMk φ x y)) :=
          finiteHilbertModuleOperatorMatrix_apply
            (fun i j => interiorModuleTensorOperator φ (T i j))
            (finiteHilbertModuleTensorForward (ι := ι) φ (interiorModuleTensorMk φ x y)) i
        rw [hr]
        apply Finset.sum_congr rfl
        intro j _
        rw [tensor_mk, interiorModuleTensorOperator_mk]; rfl
  change finiteHilbertModuleTensorForward (E := E) (ι := ι) φ
      (interiorModuleTensorOperator φ (finiteHilbertModuleOperatorMatrix T) z) =
    finiteHilbertModuleOperatorMatrix (fun i j => interiorModuleTensorOperator φ (T i j))
      (finiteHilbertModuleTensorForward (E := E) (ι := ι) φ z)
  exact congrArg (fun L : InteriorModuleTensor (E := FiniteHilbertModuleSum B E ι) φ →L[ℂ]
    FiniteHilbertModuleSum C (InteriorModuleTensor (E := E) φ) ι => L z) h

end BC4lean.KKTheory
