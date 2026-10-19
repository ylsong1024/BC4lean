import BC4lean.ArbitraryHilbertModuleSum
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Coordinatewise extension of an actual coefficient-form isometry



An actual complex linear isometry L preserving the original B-valued pairing
acts coordinatewise on finite vectors. The finite coefficient form is proved
preserved, which proves the form norm bound used for the actual radical
quotient. The resulting quotient isometry is completed, and its full pairing
identity is proved by completion density. No conclusion about the indexed
module norm or pairing is assumed as input.

The extension need not be onto. E and F need not be complete for constructing
the extension between their completed indexed modules; completeness is used
only for the inclusion and evaluation formulas at the end.
-/

noncomputable section
namespace BC4lean.KKTheory
namespace IndexedHilbertModule.Isometry
open UniformSpace
open scoped InnerProductSpace

variable {B E F I : Type*} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

local instance : DecidableEq I := Classical.decEq I

variable (L : E →ₗᵢ[ℂ] F)
  (hL : ∀ x y, ⟪L x, L y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ))

/-- The actual coordinatewise linear map on finite module vectors. -/
def finiteMap : IndexedHilbertModule.Vectors E I →ₗ[ℂ] IndexedHilbertModule.Vectors F I :=
  Finsupp.mapRange.linearMap L.toLinearMap

@[simp] theorem finiteMap_apply (x : IndexedHilbertModule.Vectors E I) (i : I) :
    finiteMap L x i = L (x i) := rfl

theorem finiteMap_support_subset (x : IndexedHilbertModule.Vectors E I) :
    (finiteMap L x).support ⊆ x.support :=
  Finsupp.support_mapRange (hf := map_zero L.toLinearMap)

@[simp] theorem finiteMap_single (i : I) (x : E) :
    finiteMap L (Finsupp.single i x) = Finsupp.single i (L x) := by
  ext j
  simp only [finiteMap_apply, Finsupp.single_apply]
  split_ifs <;> simp only [map_zero]

include hL
omit [StarOrderedRing B] in
/-- The whole finite coefficient-valued form is preserved coordinate by coordinate. -/
theorem finiteMap_inner (x y : IndexedHilbertModule.Vectors E I) :
    IndexedHilbertModule.finiteInner (B := B) (finiteMap L x) (finiteMap L y) =
      IndexedHilbertModule.finiteInner (B := B) x y := by
  rw [IndexedHilbertModule.finiteInner_eq_sum _ _ x.support (finiteMap_support_subset L x),
    IndexedHilbertModule.finiteInner_eq_sum x y x.support Finset.Subset.rfl]
  exact Finset.sum_congr rfl (fun i _ => hL (x i) (y i))

theorem finiteMap_formNorm (x : IndexedHilbertModule.Vectors E I) :
    PositiveModuleForm.formNorm (B := B) (finiteMap L x) =
      PositiveModuleForm.formNorm (B := B) x := by
  change Real.sqrt ‖IndexedHilbertModule.finiteInner (B := B) (finiteMap L x) (finiteMap L x)‖ =
    Real.sqrt ‖IndexedHilbertModule.finiteInner (B := B) x x‖
  rw [finiteMap_inner L hL]

/-- Descent through the actual positive-form radical quotient. -/
def preMap : IndexedHilbertModule.PreModule B E I →ₗ[ℂ]
    IndexedHilbertModule.PreModule B F I :=
  positiveModuleQuotientLift (finiteMap L) (K := 1)
    (fun x => by rw [finiteMap_formNorm L hL, one_mul])

@[simp] theorem preMap_mk (x : IndexedHilbertModule.Vectors E I) :
    preMap L hL (positiveModuleQuotientMk (B := B) x) =
      positiveModuleQuotientMk (B := B) (finiteMap L x) := rfl

theorem preMap_inner (x y : IndexedHilbertModule.PreModule B E I) :
    ⟪preMap L hL x, preMap L hL y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective x
  obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective y
  rw [preMap_mk, preMap_mk, PositiveModuleQuotient.inner_mk,
    PositiveModuleQuotient.inner_mk]
  exact finiteMap_inner L hL x y

def preIsometry : IndexedHilbertModule.PreModule B E I →ₗᵢ[ℂ]
    IndexedHilbertModule.PreModule B F I where
  toLinearMap := preMap L hL
  norm_map' x := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), preMap_inner]
    exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

def completedCLM : IndexedHilbertModule.Module B E I →L[ℂ]
    IndexedHilbertModule.Module B F I :=
  (preIsometry L hL).toContinuousLinearMap.completion

@[simp] theorem completedCLM_coe (x : IndexedHilbertModule.PreModule B E I) :
    completedCLM L hL (x : IndexedHilbertModule.Module B E I) =
      (preMap L hL x : IndexedHilbertModule.Module B F I) :=
  ContinuousLinearMap.completion_apply_coe _ x

/-- The actual coefficient pairing survives completion, by density. -/
theorem completedCLM_inner (x y : IndexedHilbertModule.Module B E I) :
    ⟪completedCLM L hL x, completedCLM L hL y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x y
    rw [completedCLM_coe, completedCLM_coe, completionInner_coe, completionInner_coe]
    exact preMap_inner L hL x y

/-- The genuine coordinatewise isometry of the completed indexed modules. -/
def lift : IndexedHilbertModule.Module B E I →ₗᵢ[ℂ]
    IndexedHilbertModule.Module B F I where
  toLinearMap := (completedCLM L hL).toLinearMap
  norm_map' x := by
    change ‖completedCLM L hL x‖ = ‖x‖
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), completedCLM_inner]
    exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

theorem lift_inner (x y : IndexedHilbertModule.Module B E I) :
    ⟪lift L hL x, lift L hL y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) :=
  completedCLM_inner L hL x y

@[simp] theorem lift_mk (x : IndexedHilbertModule.Vectors E I) :
    lift L hL (IndexedHilbertModule.mk (B := B) x) =
      IndexedHilbertModule.mk (B := B) (finiteMap L x) := by
  change completedCLM L hL
      ((positiveModuleQuotientMk (B := B) x) : IndexedHilbertModule.Module B E I) =
    ((positiveModuleQuotientMk (B := B) (finiteMap L x)) : IndexedHilbertModule.Module B F I)
  rw [completedCLM_coe, preMap_mk]

variable [CompleteSpace E] [CompleteSpace F]

@[simp] theorem lift_inclusion (i : I) (x : E) :
    lift L hL (IndexedHilbertModule.inclusion (B := B) i x) =
      IndexedHilbertModule.inclusion (B := B) i (L x) := by
  rw [IndexedHilbertModule.inclusion_apply, lift_mk, finiteMap_single,
    IndexedHilbertModule.inclusion_apply]

@[simp] theorem evaluation_lift (i : I) (x : IndexedHilbertModule.Module B E I) :
    IndexedHilbertModule.evaluation (B := B) i (lift L hL x) =
      L (IndexedHilbertModule.evaluation (B := B) i x) := by
  have h := (IndexedHilbertModule.mk_denseRange (B := B) (E := E) (I := I)).equalizer
    ((IndexedHilbertModule.evaluation (B := B) (E := F) i).toCLM.continuous.comp
      (lift (I := I) L hL).continuous)
    (L.continuous.comp (IndexedHilbertModule.evaluation (B := B) (E := E) i).toCLM.continuous) (by
      funext u
      change IndexedHilbertModule.evaluation (B := B) i
        (lift L hL (IndexedHilbertModule.mk (B := B) u)) =
          L (IndexedHilbertModule.evaluation (B := B) i (IndexedHilbertModule.mk (B := B) u))
      simp only [lift_mk, IndexedHilbertModule.evaluation_mk, finiteMap_apply])
  exact congrFun h x

end IndexedHilbertModule.Isometry
end BC4lean.KKTheory
