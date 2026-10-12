import BC4lean.CompactModuleOperator
import BC4lean.EquivariantHilbertModule
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! # Actual conjugation by a semilinear module grading

The grading need not itself be a coefficient-linear adjointable map.
Conjugating an adjointable operator by its genuine complex-linear grading
is nevertheless adjointable. This gives an actual involutive star
automorphism, transports rank-one maps, preserves the compact ideal, and
has exactly the even operators as its fixed points.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  {β : CStarGrading B}

namespace GradedHilbertModule

/-- Conjugation by the actual module grading, with its genuine adjoint. -/
def conjugateOperator (γ : GradedHilbertModule β E) (T : AdjointableMap B E E) :
    AdjointableMap B E E where
  toCLM := γ.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.toCLM.comp γ.grading.toContinuousLinearEquiv.toContinuousLinearMap)
  adjointCLM := γ.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.adjointCLM.comp γ.grading.toContinuousLinearEquiv.toContinuousLinearMap)
  adjoint_identity x y := by
    change ⟪γ.grading (T (γ.grading x)), y⟫_(Bᵐᵒᵖ) =
      ⟪x, γ.grading (T.adjointCLM (γ.grading y))⟫_(Bᵐᵒᵖ)
    rw [γ.inner_grading_left, T.adjoint_identity, γ.inner_grading_left,
      CStarGrading.op_automorphism_sq]

omit [StarOrderedRing B] in
@[simp] theorem conjugateOperator_apply (γ : GradedHilbertModule β E)
    (T : AdjointableMap B E E) (x : E) :
    γ.conjugateOperator T x = γ.grading (T (γ.grading x)) := rfl

omit [StarOrderedRing B] in
@[simp] theorem conjugateOperator_involutive (γ : GradedHilbertModule β E)
    (T : AdjointableMap B E E) : γ.conjugateOperator (γ.conjugateOperator T) = T := by
  ext x
  simp only [conjugateOperator_apply, γ.grading_sq]

/-- The genuine grading conjugation star automorphism on endomorphisms. -/
def conjugateOperatorStarAlgEquiv (γ : GradedHilbertModule β E) :
    AdjointableMap B E E ≃⋆ₐ[ℂ] AdjointableMap B E E where
  toFun := γ.conjugateOperator
  invFun := γ.conjugateOperator
  left_inv := γ.conjugateOperator_involutive
  right_inv := γ.conjugateOperator_involutive
  map_mul' := fun S T => by
    ext x
    simp only [conjugateOperator_apply, AdjointableMap.mul_apply, γ.grading_sq]
  map_add' := fun S T => by
    ext x
    simp only [conjugateOperator_apply, AdjointableMap.coe_add_apply, map_add]
  map_star' := fun T => rfl
  map_smul' := fun c T => by
    ext x
    simp only [conjugateOperator_apply, AdjointableMap.coe_smul_apply, map_smul]

omit [StarOrderedRing B] in
@[simp] theorem conjugateOperatorStarAlgEquiv_apply (γ : GradedHilbertModule β E)
    (T : AdjointableMap B E E) : γ.conjugateOperatorStarAlgEquiv T = γ.conjugateOperator T := rfl

omit [StarOrderedRing B] in
theorem conjugateOperator_eq_self_iff (γ : GradedHilbertModule β E)
    (T : AdjointableMap B E E) : γ.conjugateOperator T = T ↔ IsEven γ γ T := by
  constructor
  · intro h x
    have hx := congrArg (fun S : AdjointableMap B E E => S (γ.grading x)) h
    simpa only [conjugateOperator_apply, γ.grading_sq] using hx
  · intro h
    ext x
    change γ.grading (T (γ.grading x)) = T x
    simpa only [γ.grading_sq] using h (γ.grading x)

@[simp] theorem conjugateOperator_rankOne (γ : GradedHilbertModule β E) (x y : E) :
    γ.conjugateOperator (moduleRankOne x y) = moduleRankOne (γ.grading x) (γ.grading y) := by
  ext z
  simp only [conjugateOperator_apply, moduleRankOne_apply, γ.map_op_smul]
  rw [← γ.inner_grading_left]

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem conjugateOperator_mem_moduleFiniteRank (γ : GradedHilbertModule β E)
    {T : AdjointableMap B E E} (hT : T ∈ moduleFiniteRank B E E) :
    γ.conjugateOperator T ∈ moduleFiniteRank B E E := by
  let σ := γ.conjugateOperatorStarAlgEquiv
  change σ T ∈ moduleFiniteRank B E E
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨⟨x, y⟩, rfl⟩ := hT
    change γ.conjugateOperator (moduleRankOne x y) ∈ moduleFiniteRank B E E
    rw [γ.conjugateOperator_rankOne]
    exact moduleRankOne_mem_moduleFiniteRank (γ.grading x) (γ.grading y)
  | zero => simp
  | add S T _ _ hS hT => simpa only [map_add] using (moduleFiniteRank B E E).add_mem hS hT
  | smul c T _ hT => simpa only [map_smul] using (moduleFiniteRank B E E).smul_mem c hT

theorem conjugateOperator_mem_moduleCompact (γ : GradedHilbertModule β E)
    {T : AdjointableMap B E E} (hT : IsModuleCompact T) :
    IsModuleCompact (γ.conjugateOperator T) := by
  let σ := γ.conjugateOperatorStarAlgEquiv
  have h : closure (moduleFiniteRank B E E : Set (AdjointableMap B E E)) ⊆
      σ ⁻¹' (moduleCompact B E E : Set (AdjointableMap B E E)) :=
    closure_minimal
      (fun _ hS => moduleFiniteRank_le_moduleCompact (γ.conjugateOperator_mem_moduleFiniteRank hS))
      (moduleCompact_isClosed.preimage (NonUnitalStarAlgHom.isometry σ σ.injective).continuous)
  exact h hT

local instance : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- Actual grading fixed points pass to positive CFC square roots. -/
theorem IsEven.cfcSqrt {γ : GradedHilbertModule β E} {M : AdjointableMap B E E}
    (hM : IsEven γ γ M) (hpos : 0 ≤ M) : IsEven γ γ (CFC.sqrt M) := by
  let σ := γ.conjugateOperatorStarAlgEquiv
  apply (γ.conjugateOperator_eq_self_iff _).mp
  have hfixed : σ M = M := (γ.conjugateOperator_eq_self_iff M).mpr hM
  have heq : σ (CFC.sqrt M) = CFC.sqrt (σ M) := by
    symm
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self M hpos]
    · exact map_nonneg σ (CFC.sqrt_nonneg M)
  exact heq.trans (congrArg CFC.sqrt hfixed)

section CompatibleAction
variable {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ B}

omit [StarOrderedRing B] [CompleteSpace E] in
theorem conjugateOperator_commutes_action (γ : GradedHilbertModule β E)
    (U : EquivariantHilbertModule α E) (hU : U.PreservesGrading γ) (g : Γ)
    (T : AdjointableMap B E E) :
    γ.conjugateOperator (U.conjugateOperator g T) = U.conjugateOperator g (γ.conjugateOperator T) := by
  ext x
  simp only [conjugateOperator_apply, EquivariantHilbertModule.conjugateMap_apply]
  rw [← hU g, ← hU g⁻¹]

end CompatibleAction
end GradedHilbertModule
end BC4lean.KKTheory
