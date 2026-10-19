import BC4lean.ArbitraryHilbertModuleSum
import BC4lean.ReducedCrossedHilbertModule
import BC4lean.HilbertModuleEquiv
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The indexed standard module is the regular coefficient Hilbert module



Both constructions start with the actual finite families `Γ →₀ Bᵐᵒᵖ` and the
same coefficient-valued finite inner product. Their canonical finite-vector
norms therefore agree. Extending the identity between the two dense finite
images gives the genuine completed unitary below. No norm comparison or
surjectivity of that completed map is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
namespace IndexedStandardReducedCrossed
open UniformSpace
open scoped InnerProductSpace

variable {B Γ : Type*} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- The two actual finite coefficient forms are the same finite sum. -/
theorem finiteInner (x y : Γ →₀ Bᵐᵒᵖ) :
    IndexedHilbertModule.finiteInner (B := B) x y =
      reducedCrossedFiniteInner x y := rfl

/-- The two canonical finite-vector maps have exactly the same norm. -/
theorem mk_norm (x : Γ →₀ Bᵐᵒᵖ) :
    ‖IndexedHilbertModule.mk (B := B) x‖ = ‖reducedCrossedMk x‖ := by
  rw [IndexedHilbertModule.mk_norm, reducedCrossedMk_norm]

/-- The actual isometric equivalence, extending the identity on finite vectors. -/
def linearEquiv :
    IndexedHilbertModule.Module B Bᵐᵒᵖ Γ ≃ₗᵢ[ℂ]
      ReducedCrossedHilbertModule B Γ :=
  (LinearEquiv.refl ℂ (Γ →₀ Bᵐᵒᵖ)).extendOfIsometry
    (IndexedHilbertModule.mk (B := B)) reducedCrossedMk
    (IndexedHilbertModule.mk_denseRange (B := B) (E := Bᵐᵒᵖ) (I := Γ))
    (reducedCrossedMk_denseRange (B := B) (Γ := Γ))
    (fun x => (mk_norm x).symm)

@[simp] theorem linearEquiv_mk (x : Γ →₀ Bᵐᵒᵖ) :
    linearEquiv (IndexedHilbertModule.mk (B := B) x) = reducedCrossedMk x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- The finite coefficient pairing equality extends through both dense images. -/
theorem linearEquiv_inner
    (x y : IndexedHilbertModule.Module B Bᵐᵒᵖ Γ) :
    ⟪linearEquiv x, linearEquiv y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  refine (IndexedHilbertModule.mk_denseRange (B := B) (E := Bᵐᵒᵖ) (I := Γ)).induction_on
    x ?_ ?_
  · exact isClosed_eq
      (CStarModule.continuous_inner.comp
        ((linearEquiv (B := B) (Γ := Γ)).continuous.prodMk continuous_const))
      (CStarModule.continuous_inner.comp (continuous_id.prodMk continuous_const))
  · intro a
    refine (IndexedHilbertModule.mk_denseRange (B := B) (E := Bᵐᵒᵖ) (I := Γ)).induction_on
      y ?_ ?_
    · exact isClosed_eq
        (CStarModule.continuous_inner.comp
          (continuous_const.prodMk (linearEquiv (B := B) (Γ := Γ)).continuous))
        (CStarModule.continuous_inner.comp (continuous_const.prodMk continuous_id))
    · intro b
      rw [linearEquiv_mk, linearEquiv_mk,
        reducedCrossedMk_inner, IndexedHilbertModule.mk_inner]
      exact (finiteInner a b).symm

/-- The actual unitary of Hilbert modules over the original coefficient algebra. -/
def equiv :
    HilbertModuleEquiv B (IndexedHilbertModule.Module B Bᵐᵒᵖ Γ)
      (ReducedCrossedHilbertModule B Γ) where
  linearIsometryEquiv := linearEquiv
  inner_map := linearEquiv_inner

@[simp] theorem equiv_mk (x : Γ →₀ Bᵐᵒᵖ) :
    equiv (IndexedHilbertModule.mk (B := B) x) = reducedCrossedMk x :=
  linearEquiv_mk x

@[simp] theorem equiv_symm_mk (x : Γ →₀ Bᵐᵒᵖ) :
    (equiv (B := B) (Γ := Γ)).symm (reducedCrossedMk x) =
      IndexedHilbertModule.mk (B := B) x := by
  rw [← equiv_mk x, HilbertModuleEquiv.symm_apply_apply]

/-- Coordinate inclusions are identified with their actual regular counterparts. -/
@[simp] theorem equiv_inclusion (i : Γ) (b : Bᵐᵒᵖ) :
    equiv (IndexedHilbertModule.inclusion (B := B) i b) =
      reducedCrossedInclusion i b := by
  rw [IndexedHilbertModule.inclusion_apply, equiv_mk, reducedCrossedInclusion_apply]

@[simp] theorem equiv_symm_inclusion (i : Γ) (b : Bᵐᵒᵖ) :
    (equiv (B := B) (Γ := Γ)).symm (reducedCrossedInclusion i b) =
      IndexedHilbertModule.inclusion (B := B) i b := by
  rw [reducedCrossedInclusion_apply, equiv_symm_mk,
    IndexedHilbertModule.inclusion_apply]

/-- Completed coordinate evaluation commutes with the actual unitary. -/
@[simp] theorem evaluation_equiv (i : Γ)
    (x : IndexedHilbertModule.Module B Bᵐᵒᵖ Γ) :
    reducedCrossedEvaluation i (equiv x) =
      IndexedHilbertModule.evaluation (B := B) i x := by
  have h := (IndexedHilbertModule.mk_denseRange (B := B) (E := Bᵐᵒᵖ) (I := Γ)).equalizer
    ((reducedCrossedEvaluation (B := B) i).toCLM.continuous.comp
      (equiv (B := B) (Γ := Γ)).linearIsometryEquiv.continuous)
    (IndexedHilbertModule.evaluation (B := B) (E := Bᵐᵒᵖ) i).toCLM.continuous
    (by
      funext u
      change reducedCrossedEvaluation i
          (equiv (IndexedHilbertModule.mk (B := B) u)) =
        IndexedHilbertModule.evaluation (B := B) i
          (IndexedHilbertModule.mk (B := B) u)
      simp only [equiv_mk, reducedCrossedEvaluation_mk,
        IndexedHilbertModule.evaluation_mk])
  exact congrFun h x

@[simp] theorem evaluation_equiv_symm (i : Γ)
    (x : ReducedCrossedHilbertModule B Γ) :
    IndexedHilbertModule.evaluation (B := B) i
        ((equiv (B := B) (Γ := Γ)).symm x) =
      reducedCrossedEvaluation i x := by
  simpa only [HilbertModuleEquiv.apply_symm_apply] using
    (evaluation_equiv i ((equiv (B := B) (Γ := Γ)).symm x)).symm

theorem inclusion_intertwining (i : Γ) :
    (equiv (B := B) (Γ := Γ)).toAdjointable.comp
        (IndexedHilbertModule.inclusion (B := B) i) =
      reducedCrossedInclusion i := by
  apply AdjointableMap.ext
  intro b
  exact equiv_inclusion i b

theorem evaluation_intertwining (i : Γ) :
    (reducedCrossedEvaluation (B := B) i).comp
        (equiv (B := B) (Γ := Γ)).toAdjointable =
      IndexedHilbertModule.evaluation (B := B) i := by
  apply AdjointableMap.ext
  intro x
  exact evaluation_equiv i x

/-- Conjugation by the actual module unitary identifies the operator algebras. -/
def operatorEquiv :
    AdjointableMap B (IndexedHilbertModule.Module B Bᵐᵒᵖ Γ)
        (IndexedHilbertModule.Module B Bᵐᵒᵖ Γ) ≃⋆ₐ[ℂ]
      AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (ReducedCrossedHilbertModule B Γ) :=
  (equiv (B := B) (Γ := Γ)).transportStarAlgEquiv

@[simp] theorem operatorEquiv_mk
    (T : AdjointableMap B (IndexedHilbertModule.Module B Bᵐᵒᵖ Γ)
      (IndexedHilbertModule.Module B Bᵐᵒᵖ Γ)) (x : Γ →₀ Bᵐᵒᵖ) :
    operatorEquiv T (reducedCrossedMk x) =
      equiv (T (IndexedHilbertModule.mk (B := B) x)) := by
  change equiv (T ((equiv (B := B) (Γ := Γ)).symm (reducedCrossedMk x))) = _
  rw [equiv_symm_mk]

@[simp] theorem operatorEquiv_norm
    (T : AdjointableMap B (IndexedHilbertModule.Module B Bᵐᵒᵖ Γ)
      (IndexedHilbertModule.Module B Bᵐᵒᵖ Γ)) :
    ‖operatorEquiv T‖ = ‖T‖ :=
  (equiv (B := B) (Γ := Γ)).transport_norm T

end IndexedStandardReducedCrossed
end BC4lean.KKTheory
