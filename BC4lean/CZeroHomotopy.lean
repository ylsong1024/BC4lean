import BC4lean.CZeroPullback
import BC4lean.EquivariantHomotopy
import BC4lean.StarHomotopy
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

/-! # Proper homotopies give point-norm homotopies on `C₀`

The parameter slices of a function vanishing at infinity on `I × X` vary
continuously in the genuine supremum norm. Uniform continuity of a `C₀`
function proves this after choosing a metric compatible with the topology on
the pseudometrizable space `X`. Second-countable locally compact Hausdorff
spaces satisfy this hypothesis.
-/

noncomputable section

open Topology TopologicalSpace
open scoped ZeroAtInfty

namespace BC4lean.KKTheory.CZero

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inclusion of one time slice is proper. -/
theorem intervalSlice_isProperMap (t : unitInterval) :
    IsProperMap (fun x : X => (t, x)) := by
  apply IsClosedEmbedding.isProperMap
  refine ⟨isEmbedding_prodMkRight t, ?_⟩
  have hr : Set.range (fun x : X => (t, x)) = ({t} ×ˢ Set.univ) := by
    simp [Set.singleton_prod]
  rw [hr]
  exact isClosed_singleton.prod isClosed_univ

/-- Restrict a function on the whole interval product to a time slice. -/
def curry (a : C₀(unitInterval × X, ℂ)) (t : unitInterval) : C₀(X, ℂ) :=
  properPullback (fun x : X => (t, x)) (intervalSlice_isProperMap t) a

@[simp] theorem curry_apply (a : C₀(unitInterval × X, ℂ)) (t : unitInterval) (x : X) :
    curry a t x = a (t, x) := rfl

/-- Joint vanishing at infinity gives norm-continuous time slices. -/
theorem continuous_curry [PseudoMetrizableSpace X] (a : C₀(unitInterval × X, ℂ)) :
    Continuous (curry a) := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  apply UniformContinuous.continuous
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous a) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {s t} hst => ?_⟩
  apply lt_of_le_of_lt _ (half_lt_self hε)
  change dist (curry a s).toBCF (curry a t).toBCF ≤ ε / 2
  apply (BoundedContinuousFunction.dist_le (le_of_lt (half_pos hε))).mpr
  intro x
  apply le_of_lt
  apply hd
  change dist (s, x) (t, x) < δ
  simpa only [dist_prod_same_right] using hst

variable {f₀ f₁ : C(X, Y)}

/-- Every time slice of a proper homotopy is proper. -/
theorem homotopySlice_isProperMap (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : IsProperMap H) (t : unitInterval) : IsProperMap (fun x : X => H (t, x)) :=
  hH.comp (intervalSlice_isProperMap t)

/-- The source map of a proper homotopy is proper. -/
theorem homotopySource_isProperMap (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : IsProperMap H) : IsProperMap f₀ := by
  convert homotopySlice_isProperMap H hH 0 using 1
  funext x
  exact (H.apply_zero x).symm

/-- The target map of a proper homotopy is proper. -/
theorem homotopyTarget_isProperMap (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : IsProperMap H) : IsProperMap f₁ := by
  convert homotopySlice_isProperMap H hH 1 using 1
  funext x
  exact (H.apply_one x).symm

/-- A proper continuous homotopy induces an actual point-norm star homotopy. -/
def properHomotopyPullback [PseudoMetrizableSpace X]
    (H : ContinuousMap.Homotopy f₀ f₁) (hH : IsProperMap H) :
    BC4lean.OperatorKTheory.StarHomotopy
      (properPullback f₀ (homotopySource_isProperMap H hH))
      (properPullback f₁ (homotopyTarget_isProperMap H hH)) where
  toFun t := properPullback (fun x : X => H (t, x)) (homotopySlice_isProperMap H hH t)
  continuous_apply a := by
    convert continuous_curry (properPullback H hH a) using 1
    funext t
    ext x
    rfl
  source := by ext a x; exact congrArg a (H.apply_zero x)
  target := by ext a x; exact congrArg a (H.apply_one x)

@[simp] theorem properHomotopyPullback_apply [PseudoMetrizableSpace X]
    (H : ContinuousMap.Homotopy f₀ f₁) (hH : IsProperMap H)
    (t : unitInterval) (a : C₀(Y, ℂ)) (x : X) :
    (properHomotopyPullback H hH).toFun t a x = a (H (t, x)) := rfl

variable {Γ : Type*} [Group Γ] [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  {e₀ e₁ : BC4lean.ProperActions.EquivariantMap Γ X Y}

/-- Every stage of the pullback of an equivariant proper homotopy is equivariant. -/
theorem properHomotopyPullback_equivariant [PseudoMetrizableSpace X]
    (H : BC4lean.ProperActions.EquivariantHomotopy e₀ e₁) (hH : IsProperMap H)
    (t : unitInterval) (g : Γ) (a : C₀(Y, ℂ)) :
    (properHomotopyPullback H.toHomotopy hH).toFun t ((action Γ).automorphism g a) =
      (action Γ).automorphism g ((properHomotopyPullback H.toHomotopy hH).toFun t a) := by
  ext x
  change a (g⁻¹ • H (t, x)) = a (H (t, g⁻¹ • x))
  have he := H.prop t g⁻¹ x
  change H (t, g⁻¹ • x) = g⁻¹ • H (t, x) at he
  exact congrArg a he.symm

end BC4lean.KKTheory.CZero
