import BC4lean.CountableModuleOperator
import BC4lean.RectangularInteriorModuleTensorOperator
import BC4lean.InteriorModuleTensorIsometry
import BC4lean.HilbertModuleEquiv

/-! # Actual countable sums commute with the completed interior tensor

The inverse coordinate map is the finite sum of actual rectangular tensor
inclusions. Its full coefficient form is preserved. It descends through
the true positive radical and completion; elementary tensor density proves
that its completed isometry is onto.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

abbrev CountableModuleTensorSource := InteriorModuleTensor (E := CountableHilbertModuleSum B E) φ
abbrev CountableModuleTensorTarget := CountableHilbertModuleSum C (InteriorModuleTensor (E := E) φ)

def countableModuleTensorCoordinateInclusion (i : ℕ) :
    AdjointableMap C (InteriorModuleTensor (E := E) φ) (CountableModuleTensorSource (E := E) φ) :=
  RectangularInteriorModuleTensorOperator.tensor φ (countableModuleInclusion (B := B) i)

theorem countableModuleTensorCoordinateInclusion_inner (i j : ℕ)
    (u v : InteriorModuleTensor (E := E) φ) :
    ⟪countableModuleTensorCoordinateInclusion φ i u,
      countableModuleTensorCoordinateInclusion φ j v⟫_(Cᵐᵒᵖ) =
        if i = j then ⟪u, v⟫_(Cᵐᵒᵖ) else 0 := by
  rw [(countableModuleTensorCoordinateInclusion φ i).adjoint_identity]
  change ⟪u, RectangularInteriorModuleTensorOperator.tensor φ
    (countableModuleEvaluation (B := B) i)
      (RectangularInteriorModuleTensorOperator.tensor φ (countableModuleInclusion (B := B) j) v)⟫_(Cᵐᵒᵖ) = _
  rw [← AdjointableMap.comp_apply, ← RectangularInteriorModuleTensorOperator.tensor_comp]
  have hδ : (countableModuleEvaluation (B := B) (E := E) i).comp
      (countableModuleInclusion (B := B) j) = if i = j then 1 else 0 := by
    ext x
    rw [AdjointableMap.comp_apply, countableModuleEvaluation_inclusion]
    by_cases hij : i = j
    · subst j
      simp only [if_true]
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simp only [if_neg hji, if_neg hij, AdjointableMap.coe_zero_apply]
  rw [hδ]
  by_cases hij : i = j
  · simp only [if_pos hij, RectangularInteriorModuleTensorOperator.tensor_endo]
    change ⟪u, interiorModuleTensorOperatorHom φ 1 v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ)
    rw [map_one, AdjointableMap.one_apply]
  · simp only [if_neg hij, RectangularInteriorModuleTensorOperator.tensor_endo]
    change ⟪u, interiorModuleTensorOperatorHom φ 0 v⟫_(Cᵐᵒᵖ) = 0
    rw [map_zero, AdjointableMap.coe_zero_apply]
    exact CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := E) φ) (x := u)

def countableModuleTensorFiniteJoin :
    CountableModuleVectors (InteriorModuleTensor (E := E) φ) →ₗ[ℂ]
      CountableModuleTensorSource (E := E) φ :=
  Finsupp.lsum ℂ (fun i => (countableModuleTensorCoordinateInclusion φ i).toCLM.toLinearMap)

@[simp] theorem countableModuleTensorFiniteJoin_single (i : ℕ)
    (u : InteriorModuleTensor (E := E) φ) :
    countableModuleTensorFiniteJoin φ (Finsupp.single i u) =
      countableModuleTensorCoordinateInclusion φ i u := Finsupp.lsum_single _ _ _ _

theorem countableModuleTensorFiniteJoin_inner
    (v w : CountableModuleVectors (InteriorModuleTensor (E := E) φ)) :
    ⟪countableModuleTensorFiniteJoin φ v, countableModuleTensorFiniteJoin φ w⟫_(Cᵐᵒᵖ) =
      countableModuleFiniteInner (B := C) v w := by
  change ⟪∑ i ∈ v.support, countableModuleTensorCoordinateInclusion (E := E) φ i (v i),
      ∑ j ∈ w.support, countableModuleTensorCoordinateInclusion (E := E) φ j (w j)⟫_(Cᵐᵒᵖ) =
    ∑ i ∈ v.support, ⟪v i, w i⟫_(Cᵐᵒᵖ)
  rw [CStarModule.inner_sum_left (A := Cᵐᵒᵖ)
    (E := CountableModuleTensorSource (E := E) φ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [CStarModule.inner_sum_right (A := Cᵐᵒᵖ)
    (E := CountableModuleTensorSource (E := E) φ)]
  have hrow :
      (∑ j ∈ w.support,
        ⟪countableModuleTensorCoordinateInclusion (E := E) φ i (v i),
          countableModuleTensorCoordinateInclusion (E := E) φ j (w j)⟫_(Cᵐᵒᵖ)) =
      ∑ j ∈ w.support, if i = j then ⟪v i, w j⟫_(Cᵐᵒᵖ) else 0 :=
    Finset.sum_congr rfl (fun j _ =>
      countableModuleTensorCoordinateInclusion_inner (E := E) φ i j (v i) (w j))
  rw [hrow]
  rw [Finset.sum_ite_eq w.support i (fun j => ⟪v i, w j⟫_(Cᵐᵒᵖ))]
  by_cases hi : i ∈ w.support
  · rw [if_pos hi]
  · have hw : w i = 0 := Finsupp.notMem_support_iff.mp hi
    rw [if_neg hi, hw]
    exact (CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := E) φ) (x := v i)).symm

def countableModuleTensorPreJoin :
    CountableHilbertModulePreSum C (InteriorModuleTensor (E := E) φ) →ₗ[ℂ]
      CountableModuleTensorSource (E := E) φ :=
  (PositiveModuleForm.nullRadical
      (B := C) (E := CountableModuleVectors (InteriorModuleTensor (E := E) φ))).liftQ
    (countableModuleTensorFiniteJoin φ) (fun v hv => by
      rw [countableModuleFinite_nullRadical_eq_bot, Submodule.mem_bot] at hv
      rw [hv]
      change countableModuleTensorFiniteJoin (E := E) φ
        (0 : CountableModuleVectors (InteriorModuleTensor (E := E) φ)) = 0
      exact map_zero (countableModuleTensorFiniteJoin (E := E) φ))

theorem countableModuleTensorPreJoin_inner
    (v w : CountableHilbertModulePreSum C (InteriorModuleTensor (E := E) φ)) :
    ⟪countableModuleTensorPreJoin φ v, countableModuleTensorPreJoin φ w⟫_(Cᵐᵒᵖ) = ⟪v, w⟫_(Cᵐᵒᵖ) := by
  obtain ⟨v, rfl⟩ := positiveModuleQuotientMk_surjective v
  obtain ⟨w, rfl⟩ := positiveModuleQuotientMk_surjective w
  exact countableModuleTensorFiniteJoin_inner φ v w

theorem countableModuleTensorPreJoin_norm
    (v : CountableHilbertModulePreSum C (InteriorModuleTensor (E := E) φ)) :
    ‖countableModuleTensorPreJoin φ v‖ = ‖v‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), countableModuleTensorPreJoin_inner]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) v).symm

def countableModuleTensorJoin : CountableModuleTensorTarget (E := E) φ →L[ℂ]
    CountableModuleTensorSource (E := E) φ :=
  ((countableModuleTensorPreJoin φ).mkContinuous 1
    (fun v => by rw [countableModuleTensorPreJoin_norm, one_mul])).fromCompletion

@[simp] theorem countableModuleTensorJoin_mk
    (v : CountableModuleVectors (InteriorModuleTensor (E := E) φ)) :
    countableModuleTensorJoin φ (countableModuleMk (B := C) v) =
      countableModuleTensorFiniteJoin φ v := by
  rw [countableModuleMk_apply, countableModuleTensorJoin,
    ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

theorem countableModuleTensorJoin_inner (v w : CountableModuleTensorTarget (E := E) φ) :
    ⟪countableModuleTensorJoin φ v, countableModuleTensorJoin φ w⟫_(Cᵐᵒᵖ) = ⟪v, w⟫_(Cᵐᵒᵖ) := by
  refine ((countableModuleMk_denseRange (B := C) (E := InteriorModuleTensor (E := E) φ)).prodMap
    (countableModuleMk_denseRange (B := C) (E := InteriorModuleTensor (E := E) φ))).induction_on
    (p := fun q : CountableModuleTensorTarget (E := E) φ × CountableModuleTensorTarget (E := E) φ =>
      ⟪countableModuleTensorJoin φ q.1, countableModuleTensorJoin φ q.2⟫_(Cᵐᵒᵖ) =
        ⟪q.1, q.2⟫_(Cᵐᵒᵖ))
    (v, w) (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro p
  change ⟪countableModuleTensorJoin φ (countableModuleMk (B := C) p.1),
      countableModuleTensorJoin φ (countableModuleMk (B := C) p.2)⟫_(Cᵐᵒᵖ) =
    ⟪countableModuleMk (B := C) p.1, countableModuleMk (B := C) p.2⟫_(Cᵐᵒᵖ)
  rw [countableModuleTensorJoin_mk φ p.1, countableModuleTensorJoin_mk φ p.2,
    countableModuleMk_inner (B := C) p.1 p.2]
  exact countableModuleTensorFiniteJoin_inner φ p.1 p.2

def countableModuleTensorJoinIsometry : CountableModuleTensorTarget (E := E) φ →ₗᵢ[ℂ]
    CountableModuleTensorSource (E := E) φ where
  toLinearMap := (countableModuleTensorJoin φ).toLinearMap
  norm_map' v := by
    calc
      ‖countableModuleTensorJoin φ v‖ =
          Real.sqrt ‖⟪countableModuleTensorJoin φ v, countableModuleTensorJoin φ v⟫_(Cᵐᵒᵖ)‖ :=
        completion_norm_eq_sqrt_inner (B := C)
          (E := PreHilbertModuleTensor (E := CountableHilbertModuleSum B E) φ)
          (countableModuleTensorJoin φ v)
      _ = Real.sqrt ‖⟪v, v⟫_(Cᵐᵒᵖ)‖ :=
        congrArg (fun a : Cᵐᵒᵖ => Real.sqrt ‖a‖) (countableModuleTensorJoin_inner φ v v)
      _ = ‖v‖ := (CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) v).symm

theorem countableModuleTensorJoinIsometry_surjective :
    Function.Surjective (countableModuleTensorJoinIsometry (E := E) φ) := by
  let R : Submodule ℂ (CountableModuleTensorSource (E := E) φ) :=
    (countableModuleTensorJoinIsometry φ).toLinearMap.range
  have hR : IsClosed (R : Set (CountableModuleTensorSource (E := E) φ)) :=
    (countableModuleTensorJoinIsometry φ).isometry.isUniformInducing.isComplete_range.isClosed
  have hsingle (i : ℕ) (x : E) (y : F) :
      interiorModuleTensorMk φ (countableModuleInclusion (B := B) i x) y ∈ R := by
    refine ⟨countableModuleInclusion (B := C) i (interiorModuleTensorMk φ x y), ?_⟩
    change countableModuleTensorJoin φ (countableModuleMk (B := C)
      (Finsupp.single i (interiorModuleTensorMk φ x y))) = _
    rw [countableModuleTensorJoin_mk, countableModuleTensorFiniteJoin_single,
      countableModuleTensorCoordinateInclusion, RectangularInteriorModuleTensorOperator.tensor_mk]
  have hpure (x : CountableHilbertModuleSum B E) (y : F) : interiorModuleTensorMk φ x y ∈ R := by
    let Ly : CountableHilbertModuleSum B E →L[ℂ] CountableModuleTensorSource (E := E) φ :=
      ((interiorModuleTensorMk (E := CountableHilbertModuleSum B E) φ).flip y).mkContinuous
        ‖y‖ (fun z => by
          change ‖interiorModuleTensorMk φ z y‖ ≤ ‖y‖ * ‖z‖
          rw [mul_comm ‖y‖ ‖z‖]
          exact interiorModuleTensorMk_norm_le φ z y)
    refine (countableModuleMk_denseRange (B := B) (E := E)).induction_on
      (p := fun z => Ly z ∈ R) x
      (hR.preimage Ly.continuous) ?_
    intro v
    have hv : countableModuleMk (B := B) v =
        ∑ i ∈ v.support, countableModuleInclusion (B := B) i (v i) := by
      simp only [countableModuleInclusion_apply, ← map_sum]
      exact congrArg (countableModuleMk (B := B)) v.sum_single.symm
    change Ly (countableModuleMk (B := B) v) ∈ R
    rw [hv, map_sum Ly]
    exact R.sum_mem (fun i _ => hsingle i (v i) y)
  have hspan : Submodule.span ℂ
      (Set.range fun p : CountableHilbertModuleSum B E × F => interiorModuleTensorMk φ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact hpure x y
  intro z
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense φ z)

def countableModuleTensorJoinEquiv : HilbertModuleEquiv C (CountableModuleTensorTarget (E := E) φ)
    (CountableModuleTensorSource (E := E) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (countableModuleTensorJoinIsometry φ)
    (countableModuleTensorJoinIsometry_surjective φ)
  inner_map := countableModuleTensorJoin_inner φ

/-- The genuine completed tensor-row unitary, in the coordinate direction. -/
def countableModuleTensorEquiv : HilbertModuleEquiv C (CountableModuleTensorSource (E := E) φ)
    (CountableModuleTensorTarget (E := E) φ) := (countableModuleTensorJoinEquiv φ).symm

theorem countableModuleTensorEquiv_tensor_inclusion (i : ℕ)
    (v : InteriorModuleTensor (E := E) φ) :
    countableModuleTensorEquiv φ (countableModuleTensorCoordinateInclusion φ i v) =
      countableModuleInclusion (B := C) i v := by
  have h : countableModuleTensorJoinEquiv φ (countableModuleInclusion (B := C) i v) =
      countableModuleTensorCoordinateInclusion φ i v := by
    change countableModuleTensorJoin φ (countableModuleMk (B := C) (Finsupp.single i v)) = _
    rw [countableModuleTensorJoin_mk, countableModuleTensorFiniteJoin_single]
  rw [← h]
  exact (countableModuleTensorJoinEquiv φ).symm_apply_apply _

@[simp] theorem countableModuleTensorEquiv_mk_inclusion (i : ℕ) (x : E) (y : F) :
    countableModuleTensorEquiv φ
      (interiorModuleTensorMk φ (countableModuleInclusion (B := B) i x) y) =
      countableModuleInclusion (B := C) i (interiorModuleTensorMk φ x y) := by
  rw [← RectangularInteriorModuleTensorOperator.tensor_mk φ (countableModuleInclusion (B := B) i)]
  exact countableModuleTensorEquiv_tensor_inclusion φ i _

end BC4lean.KKTheory
