import BC4lean.NormalizedQuasicentralApproximateUnit
import BC4lean.CompactModuleSeparability
import BC4lean.HilbertModuleCountableGenerationSeparable
import BC4lean.CompactModuleStrongResolution

/-! # Constructing actual countable compact approximate units

In the chapter's separable-coefficient applications, countable module
generation implies separability of the module and hence of its actual
compact algebra. Canonical order-tail selections then construct an
increasing positive contractive two-sided approximate-unit sequence.
The verified rank-one estimate proves that this sequence converges
strongly on the original module. No separability of all endomorphisms is
assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter TopologicalSpace
open scoped Topology

section SeparableCoefficient
variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [SeparableSpace J]

/-- A genuine sequential approximate unit is constructed from canonical
order-tail selections on a dense countable coefficient family. -/
theorem exists_separable_increasing_approximateUnit :
    ∃ e : ℕ → J, e 0 = 0 ∧ Monotone e ∧ (∀ n, 0 ≤ e n) ∧ (∀ n, ‖e n‖ ≤ 1) ∧
      (∀ n, star (e n) = e n) ∧
      (∀ a, Tendsto (fun n => a * e n) atTop (𝓝 a)) ∧
      (∀ a, Tendsto (fun n => e n * a) atTop (𝓝 a)) := by
  obtain ⟨e, hezero, hemono, he0, he1, hestar, hleft, hright, _, _⟩ :=
    NormalizedQuasicentral.exists_monotone_positive_contractive_nonunital_sequence
      (Γ := PUnit.{1}) (NonUnitalStarAlgHom.id ℂ J) Function.injective_id
      (fun _ => (0 : J))
      (fun _ _ => ⟨0, by simp⟩) (fun _ _ => ⟨0, by simp⟩)
      (fun _ => StarAlgEquiv.refl ℂ J)
  exact ⟨e, hezero, hemono, he0, he1, hestar, hleft, hright⟩

end SeparableCoefficient

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance compactModuleCountableApproximateUnitLocalOrderInstance01 : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
local instance compactModuleCountableApproximateUnitLocalOrderInstance02 : Preorder (CompactModuleOperator B E) := (CStarAlgebra.spectralOrder (CompactModuleOperator B E)).toPreorder
local instance compactModuleCountableApproximateUnitLocalOrderInstance03 : LE (CompactModuleOperator B E) := (CStarAlgebra.spectralOrder (CompactModuleOperator B E)).toLE
local instance compactModuleCountableApproximateUnitLocalOrderInstance04 : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _
local instance compactModuleCountableApproximateUnitLocalOrderInstance05 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance compactModuleCountableApproximateUnitLocalOrderInstance06 : Preorder (AdjointableMap B E E) := (CStarAlgebra.spectralOrder (AdjointableMap B E E)).toPreorder
local instance compactModuleCountableApproximateUnitLocalOrderInstance07 : LE (AdjointableMap B E E) := (CStarAlgebra.spectralOrder (AdjointableMap B E E)).toLE
local instance compactModuleCountableApproximateUnitLocalOrderInstance08 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- For the chapter's actual countably generated modules, a genuine
countable compact AU and its strong resolution properties are derived. -/
theorem exists_countablyGenerated_compact_approximateUnit (hE : IsCountablyGeneratedModule B E) :
    ∃ e : ℕ → CompactModuleOperator B E, e 0 = 0 ∧ Monotone e ∧
      (∀ n, 0 ≤ e n) ∧ (∀ n, ‖e n‖ ≤ 1) ∧
      (∀ a, Tendsto (fun n => a * e n) atTop (𝓝 a)) ∧
      (∀ a, Tendsto (fun n => e n * a) atTop (𝓝 a)) ∧
      IsStrongIncreasingModuleResolution (fun n => (e n : AdjointableMap B E E)) := by
  let : SeparableSpace E := hE.separableSpace
  obtain ⟨e, hezero, hemono, he0, he1, _, hleft, hright⟩ :=
    exists_separable_increasing_approximateUnit (J := CompactModuleOperator B E)
  exact ⟨e, hezero, hemono, he0, he1, hleft, hright,
    strongIncreasingModuleResolution_of_compact_sequence e hezero hemono he0 he1 hleft hright⟩

end BC4lean.KKTheory
