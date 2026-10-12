import BC4lean.CompactModuleOperator
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Separability of the actual compact module-operator algebra

The diagonal ambient endomorphism algebra need not be separable. The actual
compact maps are separable when their two module spaces are: rank-one maps
depend jointly continuously on their vectors, their complex span remains
separable, and so does its norm closure.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule TopologicalSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

omit [StarOrderedRing B] in
private theorem coefficient_real_smul_comm (a : Bᵐᵒᵖ) (r : ℝ) (x : F) :
    a • (r • x) = r • (a • x) := by
  apply module_inner_ext_right (B := B)
  intro y
  simp only [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_real,
    mul_smul_comm]

omit [StarOrderedRing B] in
private theorem real_coefficient_smul (a : Bᵐᵒᵖ) (r : ℝ) (x : F) :
    (r • a) • x = r • (a • x) := by
  apply module_inner_ext_right (B := B)
  intro y
  simp only [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_real,
    smul_mul_assoc]

/-- Rank-one operators form an actual bounded real bilinear map in their
two vector parameters. -/
def moduleRankOneRealBilinear : F →L[ℝ] E →L[ℝ] AdjointableMap B E F :=
  (LinearMap.mk₂ ℝ (fun x y => moduleRankOne (B := B) x y)
    (fun x z y => by
      apply AdjointableMap.ext
      intro u
      change ⟪y, u⟫_(Bᵐᵒᵖ) • (x + z) =
        ⟪y, u⟫_(Bᵐᵒᵖ) • x + ⟪y, u⟫_(Bᵐᵒᵖ) • z
      exact module_smul_add _ _ _)
    (fun r x y => by
      apply AdjointableMap.ext
      intro u
      exact coefficient_real_smul_comm _ r x)
    (fun x y z => by
      apply AdjointableMap.ext
      intro u
      change ⟪y + z, u⟫_(Bᵐᵒᵖ) • x =
        ⟪y, u⟫_(Bᵐᵒᵖ) • x + ⟪z, u⟫_(Bᵐᵒᵖ) • x
      rw [CStarModule.inner_add_left, module_add_smul])
    (fun r x y => by
      apply AdjointableMap.ext
      intro u
      change ⟪r • y, u⟫_(Bᵐᵒᵖ) • x = r • (⟪y, u⟫_(Bᵐᵒᵖ) • x)
      rw [CStarModule.inner_smul_left_real]
      exact real_coefficient_smul _ r x)).mkContinuous₂ 1 (fun x y => by
        simpa only [LinearMap.mk₂_apply, one_mul, AdjointableMap.norm_def] using
          moduleRankOne_norm_le (B := B) x y)

@[simp] theorem moduleRankOneRealBilinear_apply (x : F) (y : E) :
    moduleRankOneRealBilinear (B := B) x y = moduleRankOne x y := rfl

/-- Joint continuity is proved in the actual operator norm. -/
theorem continuous_moduleRankOne :
    Continuous (fun p : F × E => moduleRankOne (B := B) p.1 p.2) :=
  (moduleRankOneRealBilinear (B := B) (E := E) (F := F)).continuous₂

/-- The actual finite rank span and its norm closure are separable. -/
theorem moduleCompact_isSeparable [SeparableSpace E] [SeparableSpace F] :
    IsSeparable (moduleCompact B E F : Set (AdjointableMap B E F)) := by
  change IsSeparable (closure (Submodule.span ℂ
    (Set.range fun p : F × E => moduleRankOne (B := B) p.1 p.2) : Set (AdjointableMap B E F)))
  exact (isSeparable_range (continuous_moduleRankOne (B := B) (E := E) (F := F))).span.closure

/-- In particular the compact algebra is separable even when all
adjointable endomorphisms are not. -/
instance compactModuleOperator_separableSpace [SeparableSpace E] :
    SeparableSpace (CompactModuleOperator B E) :=
  (moduleCompact_isSeparable (B := B) (E := E) (F := E)).separableSpace

end BC4lean.KKTheory
