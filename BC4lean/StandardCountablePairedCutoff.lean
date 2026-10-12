import BC4lean.CompactModuleStrongCutoff
import BC4lean.HilbertModuleSum

/-! # Paired coordinate compression preserving the Julia reference tail

On H_B ⊕ H_B, the actual paired cutoffs diag(P_n,P_n) are selfadjoint
projections converging strongly to the identity. They commute with the fixed
reference projection diag(0,1). A compact difference P−Q is therefore
approximated in operator norm by Q+C_n(P−Q)C_n, whose tail equals Q exactly.
The cutoffs themselves are not asserted compact over a nonunital algebra.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The genuine coordinate cutoff on both copies of the standard module. -/
def standardCountablePairedCutoff (n : ℕ) :
    AdjointableMap B (HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :=
  sumMap (standardCountableCutoff n) (standardCountableCutoff n)

@[simp] theorem standardCountablePairedCutoff_adjoint (n : ℕ) :
    (standardCountablePairedCutoff (B := B) n).adjoint = standardCountablePairedCutoff n := by
  simp only [standardCountablePairedCutoff, sumMap_adjoint, standardCountableCutoff_adjoint]

@[simp] theorem standardCountablePairedCutoff_mul_self (n : ℕ) :
    standardCountablePairedCutoff (B := B) n * standardCountablePairedCutoff n =
      standardCountablePairedCutoff n := by
  simp only [standardCountablePairedCutoff, ← sumMap_mul, standardCountableCutoff_mul_self]

theorem standardCountablePairedCutoff_isStarProjection (n : ℕ) :
    IsStarProjection (standardCountablePairedCutoff (B := B) n) :=
  isStarProjection_iff'.mpr ⟨standardCountablePairedCutoff_mul_self n,
    standardCountablePairedCutoff_adjoint n⟩

/-- The contraction estimate uses the actual Hilbert-module direct-sum norm. -/
theorem norm_standardCountablePairedCutoff_le (n : ℕ) :
    ‖standardCountablePairedCutoff (B := B) n‖ ≤ 1 :=
  IsStarProjection.norm_le _ (standardCountablePairedCutoff_isStarProjection n)

/-- Strong convergence is transported through the actual continuous coordinate
inclusions, rather than an assumed product-norm identification. -/
theorem standardCountablePairedCutoff_tendsto
    (x : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
    Tendsto (fun n => standardCountablePairedCutoff n x) atTop (𝓝 x) := by
  have hl := ((sumInl (B := B) (E := StandardCountableHilbertModule B)
    (F := StandardCountableHilbertModule B)).toCLM.continuous.tendsto x.fst).comp
      (standardCountableCutoff_tendsto x.fst)
  have hr := ((sumInr (B := B) (E := StandardCountableHilbertModule B)
    (F := StandardCountableHilbertModule B)).toCLM.continuous.tendsto x.snd).comp
      (standardCountableCutoff_tendsto x.snd)
  simpa only [Function.comp_def, standardCountablePairedCutoff, sumMap_apply,
    sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add, sumMk_eta] using hl.add hr

/-- Genuine compact endomorphisms are approximated by their paired coordinate
compressions in the operator norm. -/
theorem standardCountablePairedCutoff_mul_mul_tendsto
    {K : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))}
    (hK : IsModuleCompact K) :
    Tendsto (fun n => standardCountablePairedCutoff n * K * standardCountablePairedCutoff n)
      atTop (𝓝 K) :=
  isModuleCompact_tendsto_sandwich_of_strong_selfadjoint_contractions standardCountablePairedCutoff
    norm_standardCountablePairedCutoff_le standardCountablePairedCutoff_adjoint
    standardCountablePairedCutoff_tendsto hK

/-- The Julia reference projection on the paired standard module. -/
def standardCountablePairedReferenceProjection :
    AdjointableMap B (HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :=
  sumMap 0 1

theorem standardCountablePairedReferenceProjection_isStarProjection :
    IsStarProjection (standardCountablePairedReferenceProjection (B := B)) := by
  apply isStarProjection_iff'.mpr
  constructor
  · simp only [standardCountablePairedReferenceProjection, ← sumMap_mul, zero_mul, one_mul]
  · change (sumMap (0 : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)) 1).adjoint = sumMap 0 1
    rw [sumMap_adjoint]
    rfl

/-- The paired cutoffs commute with the fixed reference projection exactly. -/
theorem standardCountablePairedCutoff_commutes_reference (n : ℕ) :
    standardCountablePairedCutoff n * standardCountablePairedReferenceProjection (B := B) =
      standardCountablePairedReferenceProjection * standardCountablePairedCutoff n := by
  simp only [standardCountablePairedCutoff, standardCountablePairedReferenceProjection,
    ← sumMap_mul, mul_zero, zero_mul, mul_one, one_mul]

/-- Retain the reference tail and compress only the actual projection difference. -/
def standardCountableReferenceCompression
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (n : ℕ) :=
  standardCountablePairedReferenceProjection + standardCountablePairedCutoff n *
    (P - standardCountablePairedReferenceProjection) * standardCountablePairedCutoff n

/-- The compression of an actual selfadjoint operator is selfadjoint. -/
theorem standardCountableReferenceCompression_isSelfAdjoint
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsSelfAdjoint P) (n : ℕ) : IsSelfAdjoint (standardCountableReferenceCompression P n) := by
  change star (standardCountablePairedReferenceProjection + standardCountablePairedCutoff n *
      (P - standardCountablePairedReferenceProjection) * standardCountablePairedCutoff n) = _
  have hQ := (standardCountablePairedReferenceProjection_isStarProjection (B := B)).isSelfAdjoint.star_eq
  have hC : star (standardCountablePairedCutoff (B := B) n) = standardCountablePairedCutoff n :=
    standardCountablePairedCutoff_adjoint n
  simp only [star_add, star_mul, star_sub, hP.star_eq, hQ, hC, mul_assoc,
    standardCountableReferenceCompression]

/-- Only the compressed compact difference is added to the reference. -/
theorem standardCountableReferenceCompression_sub_isModuleCompact
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ) :
    IsModuleCompact (standardCountableReferenceCompression P n -
      standardCountablePairedReferenceProjection) := by
  have heq : standardCountableReferenceCompression P n - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (P - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n := by
    dsimp only [standardCountableReferenceCompression]
    abel
  rw [heq]
  exact (hP.comp_left (standardCountablePairedCutoff n)).comp_right (standardCountablePairedCutoff n)

/-- The reference-tail compressions tend to the original operator in norm
whenever its actual difference from the reference is compact. -/
theorem standardCountableReferenceCompression_tendsto
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    Tendsto (standardCountableReferenceCompression P) atTop (𝓝 P) := by
  have heq : standardCountablePairedReferenceProjection +
      (P - standardCountablePairedReferenceProjection) = P := by abel
  change Tendsto (fun n => standardCountablePairedReferenceProjection +
    standardCountablePairedCutoff n * (P - standardCountablePairedReferenceProjection) *
      standardCountablePairedCutoff n) atTop (𝓝 P)
  simpa only [heq] using
    (standardCountablePairedCutoff_mul_mul_tendsto hP).const_add
      standardCountablePairedReferenceProjection

/-- The compressed operator has exactly the reference action on the left tail. -/
theorem standardCountableReferenceCompression_left_tail
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (n : ℕ) :
    (1 - standardCountablePairedCutoff n) * standardCountableReferenceCompression P n =
      (1 - standardCountablePairedCutoff n) * standardCountablePairedReferenceProjection := by
  have hc : (1 - standardCountablePairedCutoff (B := B) n) * standardCountablePairedCutoff n = 0 := by
    rw [sub_mul, one_mul, standardCountablePairedCutoff_mul_self, sub_self]
  simp only [standardCountableReferenceCompression, mul_add, ← mul_assoc, hc, zero_mul, add_zero]

/-- The compressed operator has exactly the reference action on the right tail. -/
theorem standardCountableReferenceCompression_right_tail
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (n : ℕ) :
    standardCountableReferenceCompression P n * (1 - standardCountablePairedCutoff n) =
      standardCountablePairedReferenceProjection * (1 - standardCountablePairedCutoff n) := by
  have hc : standardCountablePairedCutoff (B := B) n * (1 - standardCountablePairedCutoff n) = 0 := by
    rw [mul_sub, mul_one, standardCountablePairedCutoff_mul_self, sub_self]
  simp only [standardCountableReferenceCompression, add_mul, mul_assoc, hc, mul_zero, add_zero]

end BC4lean.KKTheory
