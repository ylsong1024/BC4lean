import BC4lean.ArbitraryHilbertModuleSum
import BC4lean.RectangularInteriorModuleTensorOperator
import BC4lean.InteriorModuleTensorIsometry
import BC4lean.HilbertModuleEquiv
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Arbitrary indexed Hilbert-module sums commute with interior tensor



This is the proved CountableHilbertModuleTensor construction with its index
Nat replaced by an arbitrary type I and its finite-vector module replaced by
the actual IndexedHilbertModule construction. The finite join preserves the
whole coefficient-valued form, descends through the actual positive radical,
and extends to the genuine completion. Its range is closed; pure tensors and
finite-vector density prove surjectivity. No nondegeneracy of the left
representation and no norm or surjectivity conclusion is an input.
-/

noncomputable section
namespace BC4lean.KKTheory
namespace IndexedHilbertModule.Tensor
open scoped InnerProductSpace

variable {B C E F I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance : DecidableEq I := Classical.decEq I

abbrev Source := InteriorModuleTensor (E := IndexedHilbertModule.Module B E I) φ
abbrev Target := IndexedHilbertModule.Module C (InteriorModuleTensor (E := E) φ) I

def coordinateInclusion (i : I) :
    AdjointableMap C (InteriorModuleTensor (E := E) φ) (Source (E := E) (I := I) φ) :=
  RectangularInteriorModuleTensorOperator.tensor φ (IndexedHilbertModule.inclusion (B := B) i)

theorem coordinateInclusion_inner (i j : I)
    (u v : InteriorModuleTensor (E := E) φ) :
    ⟪coordinateInclusion (I := I) φ i u,
      coordinateInclusion (I := I) φ j v⟫_(Cᵐᵒᵖ) =
        if i = j then ⟪u, v⟫_(Cᵐᵒᵖ) else 0 := by
  rw [(coordinateInclusion (I := I) φ i).adjoint_identity]
  change ⟪u, RectangularInteriorModuleTensorOperator.tensor φ
    (IndexedHilbertModule.evaluation (B := B) i)
      (RectangularInteriorModuleTensorOperator.tensor φ (IndexedHilbertModule.inclusion (B := B) j) v)⟫_(Cᵐᵒᵖ) = _
  rw [← AdjointableMap.comp_apply, ← RectangularInteriorModuleTensorOperator.tensor_comp]
  have hδ : (IndexedHilbertModule.evaluation (B := B) (E := E) i).comp
      (IndexedHilbertModule.inclusion (B := B) j) = if i = j then 1 else 0 := by
    ext x
    rw [AdjointableMap.comp_apply, IndexedHilbertModule.evaluation_inclusion]
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

def finiteJoin :
    IndexedHilbertModule.Vectors (InteriorModuleTensor (E := E) φ) I →ₗ[ℂ]
      Source (E := E) (I := I) φ :=
  Finsupp.lsum ℂ (fun i => (coordinateInclusion (I := I) φ i).toCLM.toLinearMap)

@[simp] theorem finiteJoin_single (i : I)
    (u : InteriorModuleTensor (E := E) φ) :
    finiteJoin (I := I) φ (Finsupp.single i u) =
      coordinateInclusion (I := I) φ i u := Finsupp.lsum_single _ _ _ _

theorem finiteJoin_inner
    (v w : IndexedHilbertModule.Vectors (InteriorModuleTensor (E := E) φ) I) :
    ⟪finiteJoin (I := I) φ v, finiteJoin (I := I) φ w⟫_(Cᵐᵒᵖ) =
      IndexedHilbertModule.finiteInner (B := C) v w := by
  change ⟪∑ i ∈ v.support, coordinateInclusion (E := E) (I := I) φ i (v i),
      ∑ j ∈ w.support, coordinateInclusion (E := E) (I := I) φ j (w j)⟫_(Cᵐᵒᵖ) =
    ∑ i ∈ v.support, ⟪v i, w i⟫_(Cᵐᵒᵖ)
  rw [CStarModule.inner_sum_left (A := Cᵐᵒᵖ)
    (E := Source (E := E) (I := I) φ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [CStarModule.inner_sum_right (A := Cᵐᵒᵖ)
    (E := Source (E := E) (I := I) φ)]
  have hrow :
      (∑ j ∈ w.support,
        ⟪coordinateInclusion (E := E) (I := I) φ i (v i),
          coordinateInclusion (E := E) (I := I) φ j (w j)⟫_(Cᵐᵒᵖ)) =
      ∑ j ∈ w.support, if i = j then ⟪v i, w j⟫_(Cᵐᵒᵖ) else 0 :=
    Finset.sum_congr rfl (fun j _ =>
      coordinateInclusion_inner (E := E) (I := I) φ i j (v i) (w j))
  rw [hrow]
  rw [Finset.sum_ite_eq w.support i (fun j => ⟪v i, w j⟫_(Cᵐᵒᵖ))]
  by_cases hi : i ∈ w.support
  · rw [if_pos hi]
  · have hw : w i = 0 := Finsupp.notMem_support_iff.mp hi
    rw [if_neg hi, hw]
    exact (CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
      (E := InteriorModuleTensor (E := E) φ) (x := v i)).symm

def preJoin :
    IndexedHilbertModule.PreModule C (InteriorModuleTensor (E := E) φ) I →ₗ[ℂ]
      Source (E := E) (I := I) φ :=
  (PositiveModuleForm.nullRadical
      (B := C) (E := IndexedHilbertModule.Vectors (InteriorModuleTensor (E := E) φ) I)).liftQ
    (finiteJoin (I := I) φ) (fun v hv => by
      rw [IndexedHilbertModule.finite_nullRadical_eq_bot, Submodule.mem_bot] at hv
      rw [hv]
      change finiteJoin (E := E) (I := I) φ
        (0 : IndexedHilbertModule.Vectors (InteriorModuleTensor (E := E) φ) I) = 0
      exact map_zero (finiteJoin (E := E) (I := I) φ))

theorem preJoin_inner
    (v w : IndexedHilbertModule.PreModule C (InteriorModuleTensor (E := E) φ) I) :
    ⟪preJoin (I := I) φ v, preJoin (I := I) φ w⟫_(Cᵐᵒᵖ) = ⟪v, w⟫_(Cᵐᵒᵖ) := by
  obtain ⟨v, rfl⟩ := positiveModuleQuotientMk_surjective v
  obtain ⟨w, rfl⟩ := positiveModuleQuotientMk_surjective w
  exact finiteJoin_inner (I := I) φ v w

theorem preJoin_norm
    (v : IndexedHilbertModule.PreModule C (InteriorModuleTensor (E := E) φ) I) :
    ‖preJoin (I := I) φ v‖ = ‖v‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), preJoin_inner]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) v).symm

def join : Target (E := E) (I := I) φ →L[ℂ]
    Source (E := E) (I := I) φ :=
  ((preJoin (I := I) φ).mkContinuous 1
    (fun v => by rw [preJoin_norm, one_mul])).fromCompletion

@[simp] theorem join_mk
    (v : IndexedHilbertModule.Vectors (InteriorModuleTensor (E := E) φ) I) :
    join (I := I) φ (IndexedHilbertModule.mk (B := C) v) =
      finiteJoin (I := I) φ v := by
  rw [IndexedHilbertModule.mk_apply, join,
    ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

theorem join_inner (v w : Target (E := E) (I := I) φ) :
    ⟪join (I := I) φ v, join (I := I) φ w⟫_(Cᵐᵒᵖ) = ⟪v, w⟫_(Cᵐᵒᵖ) := by
  refine ((IndexedHilbertModule.mk_denseRange (B := C) (E := InteriorModuleTensor (E := E) φ) (I := I)).prodMap
    (IndexedHilbertModule.mk_denseRange (B := C) (E := InteriorModuleTensor (E := E) φ) (I := I))).induction_on
    (p := fun q : Target (E := E) (I := I) φ × Target (E := E) (I := I) φ =>
      ⟪join (I := I) φ q.1, join (I := I) φ q.2⟫_(Cᵐᵒᵖ) =
        ⟪q.1, q.2⟫_(Cᵐᵒᵖ))
    (v, w) (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro p
  change ⟪join (I := I) φ (IndexedHilbertModule.mk (B := C) p.1),
      join (I := I) φ (IndexedHilbertModule.mk (B := C) p.2)⟫_(Cᵐᵒᵖ) =
    ⟪IndexedHilbertModule.mk (B := C) p.1, IndexedHilbertModule.mk (B := C) p.2⟫_(Cᵐᵒᵖ)
  rw [join_mk (I := I) φ p.1, join_mk (I := I) φ p.2,
    IndexedHilbertModule.mk_inner (B := C) p.1 p.2]
  exact finiteJoin_inner (I := I) φ p.1 p.2

def joinIsometry : Target (E := E) (I := I) φ →ₗᵢ[ℂ]
    Source (E := E) (I := I) φ where
  toLinearMap := (join (I := I) φ).toLinearMap
  norm_map' v := by
    calc
      ‖join (I := I) φ v‖ =
          Real.sqrt ‖⟪join (I := I) φ v, join (I := I) φ v⟫_(Cᵐᵒᵖ)‖ :=
        completion_norm_eq_sqrt_inner (B := C)
          (E := PreHilbertModuleTensor (E := IndexedHilbertModule.Module B E I) φ)
          (join (I := I) φ v)
      _ = Real.sqrt ‖⟪v, v⟫_(Cᵐᵒᵖ)‖ :=
        congrArg (fun a : Cᵐᵒᵖ => Real.sqrt ‖a‖) (join_inner (I := I) φ v v)
      _ = ‖v‖ := (CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ) v).symm

theorem joinIsometry_surjective :
    Function.Surjective (joinIsometry (E := E) (I := I) φ) := by
  let R : Submodule ℂ (Source (E := E) (I := I) φ) :=
    (joinIsometry (I := I) φ).toLinearMap.range
  have hR : IsClosed (R : Set (Source (E := E) (I := I) φ)) :=
    (joinIsometry (I := I) φ).isometry.isUniformInducing.isComplete_range.isClosed
  have hsingle (i : I) (x : E) (y : F) :
      interiorModuleTensorMk φ (IndexedHilbertModule.inclusion (B := B) i x) y ∈ R := by
    refine ⟨IndexedHilbertModule.inclusion (B := C) i (interiorModuleTensorMk φ x y), ?_⟩
    change join (I := I) φ (IndexedHilbertModule.mk (B := C)
      (Finsupp.single i (interiorModuleTensorMk φ x y))) = _
    rw [join_mk, finiteJoin_single,
      coordinateInclusion, RectangularInteriorModuleTensorOperator.tensor_mk]
  have hpure (x : IndexedHilbertModule.Module B E I) (y : F) : interiorModuleTensorMk φ x y ∈ R := by
    let Ly : IndexedHilbertModule.Module B E I →L[ℂ] Source (E := E) (I := I) φ :=
      ((interiorModuleTensorMk (E := IndexedHilbertModule.Module B E I) φ).flip y).mkContinuous
        ‖y‖ (fun z => by
          change ‖interiorModuleTensorMk φ z y‖ ≤ ‖y‖ * ‖z‖
          rw [mul_comm ‖y‖ ‖z‖]
          exact interiorModuleTensorMk_norm_le φ z y)
    refine (IndexedHilbertModule.mk_denseRange (B := B) (E := E) (I := I)).induction_on
      (p := fun z => Ly z ∈ R) x
      (hR.preimage Ly.continuous) ?_
    intro v
    have hv : IndexedHilbertModule.mk (B := B) v =
        ∑ i ∈ v.support, IndexedHilbertModule.inclusion (B := B) i (v i) := by
      simp only [IndexedHilbertModule.inclusion_apply, ← map_sum]
      exact congrArg (IndexedHilbertModule.mk (B := B)) v.sum_single.symm
    change Ly (IndexedHilbertModule.mk (B := B) v) ∈ R
    rw [hv, map_sum Ly]
    exact R.sum_mem (fun i _ => hsingle i (v i) y)
  have hspan : Submodule.span ℂ
      (Set.range fun p : IndexedHilbertModule.Module B E I × F => interiorModuleTensorMk φ p.1 p.2) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact hpure x y
  intro z
  exact closure_minimal hspan hR (interiorModuleTensor_span_dense φ z)

def joinEquiv : HilbertModuleEquiv C (Target (E := E) (I := I) φ)
    (Source (E := E) (I := I) φ) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (joinIsometry (I := I) φ)
    (joinIsometry_surjective (I := I) φ)
  inner_map := join_inner (I := I) φ

/-- The genuine completed tensor-row unitary, in the coordinate direction. -/
def equiv : HilbertModuleEquiv C (Source (E := E) (I := I) φ)
    (Target (E := E) (I := I) φ) := (joinEquiv (I := I) φ).symm

theorem equiv_tensor_inclusion (i : I)
    (v : InteriorModuleTensor (E := E) φ) :
    equiv (I := I) φ (coordinateInclusion (I := I) φ i v) =
      IndexedHilbertModule.inclusion (B := C) i v := by
  have h : joinEquiv (I := I) φ (IndexedHilbertModule.inclusion (B := C) i v) =
      coordinateInclusion (I := I) φ i v := by
    change join (I := I) φ (IndexedHilbertModule.mk (B := C) (Finsupp.single i v)) = _
    rw [join_mk, finiteJoin_single]
  rw [← h]
  exact (joinEquiv (I := I) φ).symm_apply_apply _

@[simp] theorem equiv_mk_inclusion (i : I) (x : E) (y : F) :
    equiv (I := I) φ
      (interiorModuleTensorMk φ (IndexedHilbertModule.inclusion (B := B) i x) y) =
      IndexedHilbertModule.inclusion (B := C) i (interiorModuleTensorMk φ x y) := by
  rw [← RectangularInteriorModuleTensorOperator.tensor_mk φ (IndexedHilbertModule.inclusion (B := B) i)]
  exact equiv_tensor_inclusion (I := I) φ i _

end IndexedHilbertModule.Tensor
end BC4lean.KKTheory
