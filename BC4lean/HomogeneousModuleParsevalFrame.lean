import BC4lean.ModuleParsevalFrame
import BC4lean.ModuleCoordinateAnalysis
import BC4lean.GradedHilbertModule
import Mathlib.Tactic.Module

/-! # Constructed homogeneous Parseval frames

A genuine Parseval frame is split into the even and odd parts of each vector.
The two coefficient coordinates are actual adjointable maps into two finite
coordinates of H_B. Their coefficient partial sums converge to the module
inner product. The actual countable-sum synthesis and the proved flattening
unitary therefore give a genuine Parseval frame of homogeneous vectors.

The module grading may be semilinear over a nontrivial coefficient grading.
It is never treated as a B-linear or adjointable endomorphism here.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

namespace ModuleParsevalFrame

variable {ξ : ℕ → E} (P : ModuleParsevalFrame (B := B) ξ)

omit [CompleteSpace E] in
/-- Mixed coefficient sums converge in the actual coefficient norm. -/
theorem coefficient_mixed_partial_tendsto (P : ModuleParsevalFrame (B := B) ξ) (u v : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ⟪⟪ξ n, u⟫_(Bᵐᵒᵖ), ⟪ξ n, v⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ)) atTop (𝓝 ⟪u, v⟫_(Bᵐᵒᵖ)) := by
  have ht := (CStarModule.continuous_inner (A := Bᵐᵒᵖ)
    (E := StandardCountableHilbertModule B)).tendsto (P.analysis u, P.analysis v) |>.comp
    ((standardCountableCutoff_tendsto (P.analysis u)).prodMk_nhds tendsto_const_nhds)
  have heq (N : ℕ) :
      ⟪standardCountableCutoff N (P.analysis u), P.analysis v⟫_(Bᵐᵒᵖ) =
        ∑ n ∈ Finset.range N, ⟪⟪ξ n, u⟫_(Bᵐᵒᵖ), ⟪ξ n, v⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ) := by
    rw [standardCountableCutoff_apply,
      CStarModule.inner_sum_left (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [(standardCountableInclusion n).adjoint_identity]
    change ⟪standardCountableEvaluation n (P.analysis u),
      standardCountableEvaluation n (P.analysis v)⟫_(Bᵐᵒᵖ) = _
    rw [P.coordinate, P.coordinate]
  simpa only [Function.comp_def, heq, P.inner_analysis] using ht

end ModuleParsevalFrame

private theorem inner_two_half_coordinates (a b c d : Bᵐᵒᵖ) :
    ⟪(2 : ℂ)⁻¹ • (a + b), (2 : ℂ)⁻¹ • (c + d)⟫_(Bᵐᵒᵖ) +
      ⟪(2 : ℂ)⁻¹ • (a - b), (2 : ℂ)⁻¹ • (c - d)⟫_(Bᵐᵒᵖ) =
        (2 : ℂ)⁻¹ • (⟪a, c⟫_(Bᵐᵒᵖ) + ⟪b, d⟫_(Bᵐᵒᵖ)) := by
  have hstar : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  simp only [CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
    CStarModule.inner_add_left, CStarModule.inner_add_right,
    CStarModule.inner_sub_left, CStarModule.inner_sub_right, hstar]
  module

private theorem standardCountable_inner_two_coordinates (a b c d : Bᵐᵒᵖ) :
    ⟪standardCountableInclusion 0 a + standardCountableInclusion 1 b,
      standardCountableInclusion 0 c + standardCountableInclusion 1 d⟫_(Bᵐᵒᵖ) =
      ⟪a, c⟫_(Bᵐᵒᵖ) + ⟪b, d⟫_(Bᵐᵒᵖ) := by
  rw [CStarModule.inner_add_left (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B),
    CStarModule.inner_add_right (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B),
    CStarModule.inner_add_right (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B)]
  simp only [(standardCountableInclusion (B := B) 0).adjoint_identity,
    (standardCountableInclusion (B := B) 1).adjoint_identity]
  change ⟪a, standardCountableEvaluation 0 (standardCountableInclusion 0 c)⟫_(Bᵐᵒᵖ) +
    ⟪a, standardCountableEvaluation 0 (standardCountableInclusion 1 d)⟫_(Bᵐᵒᵖ) +
    (⟪b, standardCountableEvaluation 1 (standardCountableInclusion 0 c)⟫_(Bᵐᵒᵖ) +
      ⟪b, standardCountableEvaluation 1 (standardCountableInclusion 1 d)⟫_(Bᵐᵒᵖ)) = _
  simp only [standardCountableEvaluation_inclusion (B := B), if_true,
    if_neg (by decide : (1 : ℕ) ≠ 0), if_neg (by decide : (0 : ℕ) ≠ 1),
    CStarModule.inner_zero_right (A := Bᵐᵒᵖ) (E := Bᵐᵒᵖ), add_zero, zero_add]

variable {δB : CStarGrading B} (J : GradedHilbertModule δB E)

/-- The actual two-coordinate block belonging to one split frame vector. -/
def homogeneousFrameCoordinateBlock (ξ : ℕ → E) (n : ℕ) :
    AdjointableMap B E (StandardCountableHilbertModule B) :=
  (standardCountableInclusion 0).comp (moduleVectorCreation (J.evenPart (ξ n))).adjoint +
    (standardCountableInclusion 1).comp (moduleVectorCreation (J.oddPart (ξ n))).adjoint

omit [CompleteSpace E] in
@[simp] theorem homogeneousFrameCoordinateBlock_apply (ξ : ℕ → E) (n : ℕ) (u : E) :
    homogeneousFrameCoordinateBlock J ξ n u =
      standardCountableInclusion 0 ⟪J.evenPart (ξ n), u⟫_(Bᵐᵒᵖ) +
        standardCountableInclusion 1 ⟪J.oddPart (ξ n), u⟫_(Bᵐᵒᵖ) := rfl

omit [CompleteSpace E] in
/-- Splitting the coefficient coordinates gives half of the original square
and half of its genuinely coefficient-twisted grading conjugate. -/
theorem homogeneousFrameCoordinateBlock_inner (ξ : ℕ → E) (n : ℕ) (u v : E) :
    ⟪homogeneousFrameCoordinateBlock J ξ n u,
      homogeneousFrameCoordinateBlock J ξ n v⟫_(Bᵐᵒᵖ) =
      (2 : ℂ)⁻¹ • (⟪⟪ξ n, u⟫_(Bᵐᵒᵖ), ⟪ξ n, v⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ) +
        opStarAlgEquiv δB.automorphism
          ⟪⟪ξ n, J.grading u⟫_(Bᵐᵒᵖ), ⟪ξ n, J.grading v⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ)) := by
  rw [homogeneousFrameCoordinateBlock_apply, homogeneousFrameCoordinateBlock_apply,
    standardCountable_inner_two_coordinates]
  have hstar : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  have heven (w : E) : ⟪J.evenPart (ξ n), w⟫_(Bᵐᵒᵖ) =
      (2 : ℂ)⁻¹ • (⟪ξ n, w⟫_(Bᵐᵒᵖ) + ⟪J.grading (ξ n), w⟫_(Bᵐᵒᵖ)) := by
    change ⟪(2 : ℂ)⁻¹ • (ξ n + J.grading (ξ n)), w⟫_(Bᵐᵒᵖ) = _
    rw [CStarModule.inner_smul_left_complex (A := Bᵐᵒᵖ) (E := E),
      CStarModule.inner_add_left (A := Bᵐᵒᵖ) (E := E), hstar]
  have hodd (w : E) : ⟪J.oddPart (ξ n), w⟫_(Bᵐᵒᵖ) =
      (2 : ℂ)⁻¹ • (⟪ξ n, w⟫_(Bᵐᵒᵖ) - ⟪J.grading (ξ n), w⟫_(Bᵐᵒᵖ)) := by
    change ⟪(2 : ℂ)⁻¹ • (ξ n - J.grading (ξ n)), w⟫_(Bᵐᵒᵖ) = _
    rw [CStarModule.inner_smul_left_complex (A := Bᵐᵒᵖ) (E := E),
      CStarModule.inner_sub_left (A := Bᵐᵒᵖ) (E := E), hstar]
  rw [heven u, heven v, hodd u, hodd v, inner_two_half_coordinates,
    J.inner_grading_left, J.inner_grading_left]
  congr 2
  change opStarAlgEquiv δB.automorphism _ * star (opStarAlgEquiv δB.automorphism _) =
    opStarAlgEquiv δB.automorphism (_ * star _)
  rw [map_mul, map_star]

namespace ModuleParsevalFrame

variable {ξ : ℕ → E}

omit [CompleteSpace E] in
/-- The two-coordinate blocks satisfy the full Parseval identity by proof. -/
theorem homogeneousCoordinates (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) :
    HasParsevalOperatorCoordinates (homogeneousFrameCoordinateBlock J ξ) where
  partial_inner_tendsto u v := by
    have ht := ((P.coefficient_mixed_partial_tendsto u v).add
      (((StarAlgEquiv.isometry (opStarAlgEquiv δB.automorphism)).continuous.tendsto _).comp
        (P.coefficient_mixed_partial_tendsto (J.grading u) (J.grading v)))).const_smul ((2 : ℂ)⁻¹)
    have heq (N : ℕ) :
        (∑ n ∈ Finset.range N, ⟪homogeneousFrameCoordinateBlock J ξ n u,
          homogeneousFrameCoordinateBlock J ξ n v⟫_(Bᵐᵒᵖ)) =
        (2 : ℂ)⁻¹ • ((∑ n ∈ Finset.range N,
          ⟪⟪ξ n, u⟫_(Bᵐᵒᵖ), ⟪ξ n, v⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ)) +
          opStarAlgEquiv δB.automorphism (∑ n ∈ Finset.range N,
            ⟪⟪ξ n, J.grading u⟫_(Bᵐᵒᵖ), ⟪ξ n, J.grading v⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ))) := by
      simp only [homogeneousFrameCoordinateBlock_inner, ← Finset.smul_sum,
        Finset.sum_add_distrib, map_sum]
    have hlim : (2 : ℂ)⁻¹ • (⟪u, v⟫_(Bᵐᵒᵖ) +
        opStarAlgEquiv δB.automorphism ⟪J.grading u, J.grading v⟫_(Bᵐᵒᵖ)) =
        ⟪u, v⟫_(Bᵐᵒᵖ) := by
      rw [J.inner_grading, CStarGrading.op_automorphism_sq,
        ← two_smul ℂ ⟪u, v⟫_(Bᵐᵒᵖ),
        smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
    simpa only [Function.comp_def, heq, hlim] using ht

/-- Flatten the proved coefficient analysis into the actual H_B. -/
def homogeneousAnalysis (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) : AdjointableMap B E (StandardCountableHilbertModule B) :=
  (standardCountableInfiniteSumEquiv (B := B)).toAdjointable.comp
    (P.homogeneousCoordinates J).synthesis.adjoint

/-- The countable split frame, with zero vectors on the unused flattened lanes. -/
def homogeneousVector (_P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (k : ℕ) : E :=
  if (Nat.unpair k).2 = 0 then J.evenPart (ξ (Nat.unpair k).1)
  else if (Nat.unpair k).2 = 1 then J.oddPart (ξ (Nat.unpair k).1) else 0

/-- Degree zero for the even and unused lanes, degree one for the odd lane. -/
def homogeneousDegree (_P : ModuleParsevalFrame (B := B) ξ) (k : ℕ) : Bool :=
  (Nat.unpair k).2 == 1

omit [CompleteSpace E] in
theorem homogeneousVector_grading (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (k : ℕ) :
    J.grading (P.homogeneousVector J k) =
      if P.homogeneousDegree k then -P.homogeneousVector J k else P.homogeneousVector J k := by
  simp only [homogeneousVector, homogeneousDegree, beq_iff_eq]
  split_ifs <;> simp_all

theorem homogeneousAnalysis_coordinate (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (k : ℕ) (u : E) :
    standardCountableEvaluation k (P.homogeneousAnalysis J u) =
      ⟪P.homogeneousVector J k, u⟫_(Bᵐᵒᵖ) := by
  let n := (Nat.unpair k).1
  let m := (Nat.unpair k).2
  have hk : Nat.pair n m = k := Nat.pair_unpair k
  rw [← hk]
  change standardCountableEvaluation (Nat.pair n m)
      (standardCountableFlattenCLM ((P.homogeneousCoordinates J).synthesis.adjoint u)) = _
  rw [standardCountableEvaluation_pair_flatten,
    HasParsevalOperatorCoordinates.evaluation_synthesis_adjoint,
    homogeneousFrameCoordinateBlock_apply, map_add,
    standardCountableEvaluation_inclusion, standardCountableEvaluation_inclusion]
  simp only [homogeneousVector, Nat.unpair_pair]
  by_cases hm0 : m = 0
  · simp only [hm0, if_true, if_neg (by decide : (1 : ℕ) ≠ 0), add_zero]
  · by_cases hm1 : m = 1
    · simp only [hm1, if_true, if_neg (by decide : (0 : ℕ) ≠ 1),
        if_neg (by decide : (1 : ℕ) ≠ 0), zero_add]
    · simp only [if_neg hm0, if_neg hm1, if_neg (Ne.symm hm0),
        if_neg (Ne.symm hm1), zero_add,
        CStarModule.inner_zero_left (A := Bᵐᵒᵖ) (E := E)]

/-- A genuine Parseval frame whose vectors have proved homogeneous degrees. -/
def homogeneous (P : ModuleParsevalFrame (B := B) ξ) (J : GradedHilbertModule δB E) :
    ModuleParsevalFrame (B := B) (P.homogeneousVector J) where
  analysis := P.homogeneousAnalysis J
  coordinate := P.homogeneousAnalysis_coordinate J
  adjoint_comp_self := by
    let U := standardCountableInfiniteSumEquiv (B := B)
    let S := (P.homogeneousCoordinates J).synthesis
    rw [homogeneousAnalysis, AdjointableMap.adjoint_comp]
    ext u
    change S (U.toAdjointable.adjoint (U.toAdjointable (S.adjoint u))) = u
    rw [U.toAdjointable_adjoint, U.toAdjointable_apply, U.symm.toAdjointable_apply,
      U.symm_apply_apply]
    exact congrArg (fun R => R u) (P.homogeneousCoordinates J).synthesis_comp_adjoint

end ModuleParsevalFrame

/-- Countable generation constructs a homogeneous Parseval frame for every
actual module grading, including a nontrivial coefficient grading. -/
theorem exists_homogeneousModuleParsevalFrame (hE : IsCountablyGeneratedModule B E) :
    ∃ (ξ : ℕ → E) (p : ℕ → Bool), Nonempty (ModuleParsevalFrame (B := B) ξ) ∧
      ∀ n, J.grading (ξ n) = if p n then -ξ n else ξ n := by
  obtain ⟨η, ⟨P⟩⟩ := exists_moduleParsevalFrame hE
  exact ⟨P.homogeneousVector J, P.homogeneousDegree, ⟨P.homogeneous J⟩,
    P.homogeneousVector_grading J⟩

end BC4lean.KKTheory
