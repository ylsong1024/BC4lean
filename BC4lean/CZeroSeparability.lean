import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Separability of the actual supremum-norm C₀ algebra

The extension by zero at infinity is an isometric embedding into the continuous
functions on the one-point compactification. Second countability of that
compactification is proved using a compact exhaustion; compact-open separability
of `C(X, ℂ)` alone would not establish supremum-norm separability for noncompact X.
-/

noncomputable section
open Topology TopologicalSpace Set Filter
open scoped ZeroAtInfty OnePoint

namespace BC4lean.TopologicalKHomology
variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- A locally compact second-countable space has a second-countable one-point
compactification, including when the original space is empty or compact. -/
theorem onePoint_secondCountable [LocallyCompactSpace X] [SecondCountableTopology X] :
    SecondCountableTopology (OnePoint X) := by
  let K := CompactExhaustion.choice X
  let b : Set (Set (OnePoint X)) :=
    (fun U : Set X => ((↑) : X → OnePoint X) '' U) '' countableBasis X ∪
      Set.range (fun n : ℕ => (((↑) : X → OnePoint X) '' K n)ᶜ)
  apply TopologicalSpace.IsTopologicalBasis.secondCountableTopology (b := b)
  · apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      rcases hU with hU | hU
      · obtain ⟨V, hV, rfl⟩ := hU
        exact OnePoint.isOpenMap_coe V (isOpen_of_mem_countableBasis hV)
      · obtain ⟨n, rfl⟩ := hU
        exact OnePoint.isOpen_compl_image_coe.mpr ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · intro x U hx hU
      induction x using OnePoint.rec with
      | infty =>
          have hc : IsCompact (((↑) : X → OnePoint X) ⁻¹' Uᶜ) :=
            ((OnePoint.isOpen_iff_of_mem hx).mp hU).2
          obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hc
          refine ⟨(((↑) : X → OnePoint X) '' K n)ᶜ, Or.inr ⟨n, rfl⟩,
            OnePoint.infty_notMem_image_coe, ?_⟩
          intro z hz
          induction z using OnePoint.rec with
          | infty => exact hx
          | coe z =>
              by_contra h
              exact hz ⟨z, hn h, rfl⟩
      | coe x =>
          obtain ⟨V, hV, hxV, hVU⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open
            hx (hU.preimage OnePoint.continuous_coe)
          exact ⟨((↑) : X → OnePoint X) '' V, Or.inl ⟨V, hV, rfl⟩,
            ⟨x, hxV, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hVU hy⟩
  · exact ((countable_countableBasis X).image _).union (countable_range _)

/-- Extend a vanishing-at-infinity function by the value zero at infinity. -/
def extendAtInfinity (f : C₀(X, ℂ)) : C(OnePoint X, ℂ) :=
  OnePoint.continuousMapMk f.toContinuousMap 0
    (by
      change Tendsto f (coclosedCompact X) (𝓝 0)
      simpa only [coclosedCompact_eq_cocompact] using zero_at_infty f)

@[simp] theorem extendAtInfinity_coe (f : C₀(X, ℂ)) (x : X) :
    extendAtInfinity f (x : OnePoint X) = f x := rfl

@[simp] theorem extendAtInfinity_infty (f : C₀(X, ℂ)) :
    extendAtInfinity f ∞ = 0 := rfl

/-- The extension retains the genuine C₀ supremum metric. -/
theorem extendAtInfinity_isometry : Isometry (extendAtInfinity (X := X)) := by
  apply Isometry.of_dist_eq
  intro f g
  apply le_antisymm
  · apply (ContinuousMap.dist_le (dist_nonneg)).mpr
    intro x
    induction x using OnePoint.rec with
    | infty => simp
    | coe x =>
        exact BoundedContinuousFunction.dist_coe_le_dist (f := f.toBCF) (g := g.toBCF) x
  · change dist f.toBCF g.toBCF ≤ _
    apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro x
    exact ContinuousMap.dist_apply_le_dist (f := extendAtInfinity f)
      (g := extendAtInfinity g) (x : OnePoint X)

/-- The C₀ algebra of a second-countable locally compact Hausdorff space is
separable in its supremum norm. -/
theorem cZero_separableSpace [LocallyCompactSpace X] [SecondCountableTopology X] :
    SeparableSpace C₀(X, ℂ) := by
  let := onePoint_secondCountable (X := X)
  exact extendAtInfinity_isometry.isEmbedding.separableSpace

end BC4lean.TopologicalKHomology
