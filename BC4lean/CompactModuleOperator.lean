import BC4lean.AdjointableComplete
import BC4lean.RankOneOperator
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Topology.Algebra.Module.Basic

/-! # Compact operators on right Hilbert C⋆-modules

The compact module maps are the operator-norm closure of the complex linear
span of the maps `moduleRankOne x y`.  The span is the module notion of finite
rank; it need not consist of operators with finite-dimensional complex range.
We prove adjoint stability and the two composition ideal properties, also for
maps between different modules.  Compact endomorphisms form a closed non-unital
star subalgebra, hence a non-unital C⋆-algebra when the module is complete.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

namespace AdjointableMap

/-- Taking adjoints is a bounded conjugate-linear map, also between different
modules. -/
def adjointContinuousLinearMap :
    AdjointableMap B E F →L⋆[ℂ] AdjointableMap B F E :=
  LinearMap.mkContinuous
    { toFun := adjoint
      map_add' := fun S T => by
        change (S.add T).adjoint = S.adjoint.add T.adjoint
        exact adjoint_add S T
      map_smul' := fun c T => by
        change (T.smul c).adjoint = T.adjoint.smul (star c)
        exact adjoint_smul c T }
    1 (fun T => by
      simp only [norm_def, one_mul]
      exact (norm_adjoint_toCLM T).le)

@[simp] theorem adjointContinuousLinearMap_apply (T : AdjointableMap B E F) :
    adjointContinuousLinearMap T = T.adjoint := rfl

/-- Left composition by a fixed adjointable map is bounded and complex-linear. -/
def compLeftContinuousLinearMap (S : AdjointableMap B F G) :
    AdjointableMap B E F →L[ℂ] AdjointableMap B E G :=
  LinearMap.mkContinuous
    { toFun := S.comp
      map_add' := fun T U => by
        ext x
        change S.toCLM (T.toCLM x + U.toCLM x) =
          S.toCLM (T.toCLM x) + S.toCLM (U.toCLM x)
        exact S.toCLM.map_add _ _
      map_smul' := fun c T => by
        ext x
        change S.toCLM (c • T.toCLM x) = c • S.toCLM (T.toCLM x)
        exact S.toCLM.map_smul c _ }
    ‖S‖ (fun T => norm_comp_le S T)

omit [StarOrderedRing B] in
@[simp] theorem compLeftContinuousLinearMap_apply
    (S : AdjointableMap B F G) (T : AdjointableMap B E F) :
    compLeftContinuousLinearMap S T = S.comp T := rfl

/-- Right composition by a fixed adjointable map is bounded and complex-linear. -/
def compRightContinuousLinearMap (T : AdjointableMap B E F) :
    AdjointableMap B F G →L[ℂ] AdjointableMap B E G :=
  LinearMap.mkContinuous
    { toFun := fun S => S.comp T
      map_add' := fun S U => by ext x; rfl
      map_smul' := fun c S => by ext x; rfl }
    ‖T‖ (fun S => by
      change ‖S.comp T‖ ≤ ‖T‖ * ‖S‖
      rw [mul_comm]
      exact norm_comp_le S T)

omit [StarOrderedRing B] in
@[simp] theorem compRightContinuousLinearMap_apply
    (T : AdjointableMap B E F) (S : AdjointableMap B F G) :
    compRightContinuousLinearMap T S = S.comp T := rfl

end AdjointableMap

/-- The complex linear span of rank-one module maps. -/
def moduleFiniteRank (B E F : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] :
    Submodule ℂ (AdjointableMap B E F) :=
  Submodule.span ℂ (Set.range fun p : F × E => moduleRankOne (B := B) p.1 p.2)

/-- Compact module maps: the operator-norm closure of the rank-one span. -/
def moduleCompact (B E F : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] :
    Submodule ℂ (AdjointableMap B E F) :=
  (moduleFiniteRank B E F).topologicalClosure

/-- An adjointable map is compact in the Hilbert C⋆-module sense. -/
def IsModuleCompact (T : AdjointableMap B E F) : Prop := T ∈ moduleCompact B E F

/-- The normed space of compact module maps. -/
abbrev CompactModuleMap (B E F : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] :=
  moduleCompact B E F

@[simp] theorem mem_moduleCompact_iff (T : AdjointableMap B E F) :
    T ∈ moduleCompact B E F ↔
      T ∈ closure (moduleFiniteRank B E F : Set (AdjointableMap B E F)) := Iff.rfl

/-- Compactness is approximation in the operator norm by the rank-one span. -/
theorem mem_moduleCompact_iff_approx (T : AdjointableMap B E F) :
    T ∈ moduleCompact B E F ↔
      ∀ ε > 0, ∃ S ∈ moduleFiniteRank B E F, ‖T - S‖ < ε := by
  rw [mem_moduleCompact_iff]
  constructor
  · intro hT ε hε
    obtain ⟨S, hS, hTS⟩ := Metric.mem_closure_iff.mp hT ε hε
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hTS⟩
  · intro hT
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨S, hS, hTS⟩ := hT ε hε
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hTS⟩

theorem moduleFiniteRank_le_moduleCompact :
    moduleFiniteRank B E F ≤ moduleCompact B E F :=
  Submodule.le_topologicalClosure _

theorem moduleCompact_isClosed :
    IsClosed (moduleCompact B E F : Set (AdjointableMap B E F)) :=
  Submodule.isClosed_topologicalClosure _

/-- Compact maps are the smallest closed complex subspace containing rank-one
module maps. -/
theorem moduleCompact_le_of_isClosed (S : Submodule ℂ (AdjointableMap B E F))
    (hS : IsClosed (S : Set (AdjointableMap B E F)))
    (hθ : ∀ (x : F) (y : E), moduleRankOne (B := B) x y ∈ S) :
    moduleCompact B E F ≤ S := by
  apply Submodule.topologicalClosure_minimal _ _ hS
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact hθ x y

theorem moduleRankOne_mem_moduleFiniteRank (x : F) (y : E) :
    moduleRankOne (B := B) x y ∈ moduleFiniteRank B E F :=
  Submodule.subset_span ⟨(x, y), rfl⟩

theorem moduleRankOne_mem_moduleCompact (x : F) (y : E) :
    moduleRankOne (B := B) x y ∈ moduleCompact B E F :=
  moduleFiniteRank_le_moduleCompact (moduleRankOne_mem_moduleFiniteRank x y)

/-- The rank-one span is stable under taking adjoints. -/
theorem moduleFiniteRank_adjoint {T : AdjointableMap B E F}
    (hT : T ∈ moduleFiniteRank B E F) : T.adjoint ∈ moduleFiniteRank B F E := by
  change AdjointableMap.adjointContinuousLinearMap T ∈ moduleFiniteRank B F E
  induction hT using Submodule.span_induction with
  | mem T hT =>
    rcases hT with ⟨⟨x, y⟩, rfl⟩
    exact moduleRankOne_mem_moduleFiniteRank y x
  | zero =>
    rw [map_zero]
    exact (moduleFiniteRank B F E).zero_mem
  | add S T _ _ hS hT =>
    rw [map_add]
    exact (moduleFiniteRank B F E).add_mem hS hT
  | smul c T _ hT =>
    rw [map_smulₛₗ]
    exact (moduleFiniteRank B F E).smul_mem _ hT

/-- Left composition preserves the rank-one span. -/
theorem comp_mem_moduleFiniteRank (S : AdjointableMap B F G)
    {T : AdjointableMap B E F} (hT : T ∈ moduleFiniteRank B E F) :
    S.comp T ∈ moduleFiniteRank B E G := by
  change AdjointableMap.compLeftContinuousLinearMap S T ∈ moduleFiniteRank B E G
  induction hT using Submodule.span_induction with
  | mem T hT =>
    rcases hT with ⟨⟨x, y⟩, rfl⟩
    simpa only [AdjointableMap.compLeftContinuousLinearMap_apply, comp_moduleRankOne] using
      moduleRankOne_mem_moduleFiniteRank (S x) y
  | zero =>
    rw [map_zero]
    exact (moduleFiniteRank B E G).zero_mem
  | add T U _ _ hT hU =>
    rw [map_add]
    exact (moduleFiniteRank B E G).add_mem hT hU
  | smul c T _ hT =>
    rw [map_smul]
    exact (moduleFiniteRank B E G).smul_mem _ hT

/-- Right composition preserves the rank-one span. -/
theorem mem_moduleFiniteRank_comp {S : AdjointableMap B F G}
    (hS : S ∈ moduleFiniteRank B F G) (T : AdjointableMap B E F) :
    S.comp T ∈ moduleFiniteRank B E G := by
  change AdjointableMap.compRightContinuousLinearMap T S ∈ moduleFiniteRank B E G
  induction hS using Submodule.span_induction with
  | mem S hS =>
    rcases hS with ⟨⟨x, y⟩, rfl⟩
    simpa only [AdjointableMap.compRightContinuousLinearMap_apply, moduleRankOne_comp] using
      moduleRankOne_mem_moduleFiniteRank x (T.adjoint y)
  | zero =>
    rw [map_zero]
    exact (moduleFiniteRank B E G).zero_mem
  | add S U _ _ hS hU =>
    rw [map_add]
    exact (moduleFiniteRank B E G).add_mem hS hU
  | smul c S _ hS =>
    rw [map_smul]
    exact (moduleFiniteRank B E G).smul_mem _ hS

/-- Adjoint stability of compact maps follows by continuity from rank-one
adjoint stability. -/
theorem moduleCompact_adjoint {T : AdjointableMap B E F}
    (hT : T ∈ moduleCompact B E F) : T.adjoint ∈ moduleCompact B F E := by
  have h : closure (moduleFiniteRank B E F : Set (AdjointableMap B E F)) ⊆
      AdjointableMap.adjointContinuousLinearMap ⁻¹'
        (moduleCompact B F E : Set (AdjointableMap B F E)) :=
    closure_minimal
      (fun _ hS => moduleFiniteRank_le_moduleCompact (moduleFiniteRank_adjoint hS))
      (moduleCompact_isClosed.preimage AdjointableMap.adjointContinuousLinearMap.continuous)
  exact h hT

@[simp] theorem adjoint_mem_moduleCompact_iff (T : AdjointableMap B E F) :
    T.adjoint ∈ moduleCompact B F E ↔ T ∈ moduleCompact B E F :=
  ⟨fun h => by simpa using moduleCompact_adjoint h, moduleCompact_adjoint⟩

/-- Compact module maps form a left composition ideal. -/
theorem comp_mem_moduleCompact (S : AdjointableMap B F G)
    {T : AdjointableMap B E F} (hT : T ∈ moduleCompact B E F) :
    S.comp T ∈ moduleCompact B E G := by
  have h : closure (moduleFiniteRank B E F : Set (AdjointableMap B E F)) ⊆
      AdjointableMap.compLeftContinuousLinearMap S ⁻¹'
        (moduleCompact B E G : Set (AdjointableMap B E G)) :=
    closure_minimal
      (fun _ hU => moduleFiniteRank_le_moduleCompact (comp_mem_moduleFiniteRank S hU))
      (moduleCompact_isClosed.preimage (AdjointableMap.compLeftContinuousLinearMap S).continuous)
  exact h hT

/-- Compact module maps form a right composition ideal. -/
theorem mem_moduleCompact_comp {S : AdjointableMap B F G}
    (hS : S ∈ moduleCompact B F G) (T : AdjointableMap B E F) :
    S.comp T ∈ moduleCompact B E G := by
  have h : closure (moduleFiniteRank B F G : Set (AdjointableMap B F G)) ⊆
      AdjointableMap.compRightContinuousLinearMap T ⁻¹'
        (moduleCompact B E G : Set (AdjointableMap B E G)) :=
    closure_minimal
      (fun _ hU => moduleFiniteRank_le_moduleCompact (mem_moduleFiniteRank_comp hU T))
      (moduleCompact_isClosed.preimage (AdjointableMap.compRightContinuousLinearMap T).continuous)
  exact h hS

namespace IsModuleCompact

theorem zero : IsModuleCompact (0 : AdjointableMap B E F) :=
  (moduleCompact B E F).zero_mem

theorem add {S T : AdjointableMap B E F} (hS : IsModuleCompact S)
    (hT : IsModuleCompact T) : IsModuleCompact (S + T) :=
  (moduleCompact B E F).add_mem hS hT

theorem neg {T : AdjointableMap B E F} (hT : IsModuleCompact T) :
    IsModuleCompact (-T) := (moduleCompact B E F).neg_mem hT

theorem sub {S T : AdjointableMap B E F} (hS : IsModuleCompact S)
    (hT : IsModuleCompact T) : IsModuleCompact (S - T) :=
  (moduleCompact B E F).sub_mem hS hT

theorem smul {T : AdjointableMap B E F} (hT : IsModuleCompact T) (c : ℂ) :
    IsModuleCompact (c • T) := (moduleCompact B E F).smul_mem c hT

theorem adjoint {T : AdjointableMap B E F} (hT : IsModuleCompact T) :
    IsModuleCompact T.adjoint := moduleCompact_adjoint hT

theorem comp_left {T : AdjointableMap B E F} (hT : IsModuleCompact T)
    (S : AdjointableMap B F G) : IsModuleCompact (S.comp T) :=
  comp_mem_moduleCompact S hT

theorem comp_right {S : AdjointableMap B F G} (hS : IsModuleCompact S)
    (T : AdjointableMap B E F) : IsModuleCompact (S.comp T) :=
  mem_moduleCompact_comp hS T

end IsModuleCompact

/-- The two-sided ideal property for endomorphisms, in multiplication notation. -/
theorem mul_mem_moduleCompact_left (S : AdjointableMap B E E)
    {T : AdjointableMap B E E} (hT : T ∈ moduleCompact B E E) :
    S * T ∈ moduleCompact B E E := comp_mem_moduleCompact S hT

/-- The two-sided ideal property for endomorphisms, in multiplication notation. -/
theorem mul_mem_moduleCompact_right {S : AdjointableMap B E E}
    (hS : S ∈ moduleCompact B E E) (T : AdjointableMap B E E) :
    S * T ∈ moduleCompact B E E := mem_moduleCompact_comp hS T

/-- Compact endomorphisms, packaged as a ring ideal. -/
def compactModuleOperatorIdeal : Ideal (AdjointableMap B E E) where
  carrier := moduleCompact B E E
  zero_mem' := (moduleCompact B E E).zero_mem
  add_mem' := (moduleCompact B E E).add_mem
  smul_mem' := fun S _ hT => comp_mem_moduleCompact S hT

@[simp] theorem mem_compactModuleOperatorIdeal (T : AdjointableMap B E E) :
    T ∈ compactModuleOperatorIdeal (B := B) (E := E) ↔ T ∈ moduleCompact B E E := Iff.rfl

instance compactModuleOperatorIdeal_isTwoSided :
    (compactModuleOperatorIdeal (B := B) (E := E)).IsTwoSided where
  mul_mem_of_left T hS := mem_moduleCompact_comp hS T

instance compactModuleOperatorIdeal_isClosed :
    IsClosed (compactModuleOperatorIdeal (B := B) (E := E) : Set (AdjointableMap B E E)) :=
  moduleCompact_isClosed

/-- The compact endomorphisms as a non-unital star subalgebra of all adjointable
endomorphisms. -/
def compactModuleOperatorAlgebra : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E) where
  carrier := moduleCompact B E E
  zero_mem' := (moduleCompact B E E).zero_mem
  add_mem' := (moduleCompact B E E).add_mem
  mul_mem' := fun _ hT => comp_mem_moduleCompact _ hT
  smul_mem' := fun c _ hx => (moduleCompact B E E).smul_mem c hx
  star_mem' := moduleCompact_adjoint

@[simp] theorem mem_compactModuleOperatorAlgebra (T : AdjointableMap B E E) :
    T ∈ compactModuleOperatorAlgebra (B := B) (E := E) ↔ T ∈ moduleCompact B E E := Iff.rfl

instance compactModuleOperatorAlgebra_isClosed :
    IsClosed (compactModuleOperatorAlgebra (B := B) (E := E) : Set (AdjointableMap B E E)) :=
  moduleCompact_isClosed

/-- The C⋆-algebra of compact endomorphisms of a complete right Hilbert
C⋆-module. -/
abbrev CompactModuleOperator (B E : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] :=
  compactModuleOperatorAlgebra (B := B) (E := E)

instance compactModuleOperator_nonUnitalCStarAlgebra [CompleteSpace E] :
    NonUnitalCStarAlgebra (CompactModuleOperator B E) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _

end BC4lean.KKTheory
