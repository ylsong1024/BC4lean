import BC4lean.OddKTheoryMatrixUnitaryClass
import BC4lean.OddFredholmFiniteCompression
import BC4lean.ProjectionHilbertModuleSplit

/-! # The genuine finite corner and its actual orthogonal tail

The coordinate inclusion identifies the cutoff corner with Bⁿ. Its
orthogonal complement is the actual range of I-Pₙ, not an assumed essential
complement of a coefficient homomorphism. A unitary with exact identity tail
is transported to its genuine finite compression plus the identity.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace CStarAlgebra

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local instance oddContinuationOddKTheoryStandardFiniteSplitLocalInstance01 (n : ℕ) : CompleteSpace (FiniteStandardModule B (Fin n)) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryStandardFiniteSplitLocalInstance02 (n : ℕ) : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B (Fin n))
    (ProjectionModule (1 - standardCountableCutoff (B := B) n))) := hilbertModuleSum_complete

theorem oddKTheoryFiniteAdjoint_tail_zero (n : ℕ)
    (x : ProjectionModule (1 - standardCountableCutoff (B := B) n)) :
    (oddFredholmStandardFiniteInclusion n).adjoint (x : _) = 0 := by
  have hp : standardCountableCutoff n (x : _) = 0 := projection_complement_fixed_eq_zero _ x
  have h := congrArg (fun T => T (x : _)) (oddFredholmStandardFiniteAdjoint_comp_cutoff (B := B) n)
  simpa only [AdjointableMap.comp_apply, hp, map_zero] using h.symm

theorem oddKTheoryStandardFiniteSplit_inner (n : ℕ) (x y : StandardCountableHilbertModule B) :
    ⟪(oddFredholmStandardFiniteInclusion n).adjoint x,
      (oddFredholmStandardFiniteInclusion n).adjoint y⟫_(Bᵐᵒᵖ) +
      ⟪projectionCorestrict (1 - standardCountableCutoff n)
          (standardCountableCutoff_isStarProjection n).one_sub x,
        projectionCorestrict (1 - standardCountableCutoff n)
          (standardCountableCutoff_isStarProjection n).one_sub y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  have hfirst : ⟪(oddFredholmStandardFiniteInclusion n).adjoint x,
      (oddFredholmStandardFiniteInclusion n).adjoint y⟫_(Bᵐᵒᵖ) =
      ⟪x, standardCountableCutoff n y⟫_(Bᵐᵒᵖ) := by
    rw [(oddFredholmStandardFiniteInclusion n).adjoint.adjoint_identity,
      AdjointableMap.adjoint_adjoint, ← AdjointableMap.comp_apply,
      oddFredholmStandardFiniteInclusion_comp_adjoint]
  have htail : ⟪projectionCorestrict (1 - standardCountableCutoff n)
        (standardCountableCutoff_isStarProjection n).one_sub x,
      projectionCorestrict (1 - standardCountableCutoff n)
        (standardCountableCutoff_isStarProjection n).one_sub y⟫_(Bᵐᵒᵖ) =
      ⟪x, (1 - standardCountableCutoff n) y⟫_(Bᵐᵒᵖ) := by
    change ⟪(1 - standardCountableCutoff n) x, (1 - standardCountableCutoff n) y⟫_(Bᵐᵒᵖ) = _
    rw [(1 - standardCountableCutoff (B := B) n).adjoint_identity,
      (standardCountableCutoff_isStarProjection n).one_sub.isSelfAdjoint.star_eq,
      ← AdjointableMap.mul_apply, (standardCountableCutoff_isStarProjection n).one_sub.isIdempotentElem.eq]
  rw [hfirst, htail, ← CStarModule.inner_add_right, projection_complement_apply_add]

def oddKTheoryStandardFiniteSplitEquiv (n : ℕ) : HilbertModuleEquiv B
    (StandardCountableHilbertModule B)
    (HilbertModuleSum B (FiniteStandardModule B (Fin n))
      (ProjectionModule (1 - standardCountableCutoff n))) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := sumMk ((oddFredholmStandardFiniteInclusion n).adjoint x)
            (projectionCorestrict (1 - standardCountableCutoff n)
              (standardCountableCutoff_isStarProjection n).one_sub x)
          invFun x := oddFredholmStandardFiniteInclusion n x.fst + (x.snd : _)
          left_inv x := by
            rw [← AdjointableMap.comp_apply, oddFredholmStandardFiniteInclusion_comp_adjoint]
            exact projection_complement_apply_add _ x
          right_inv x := by
            apply Prod.ext
            · rw [(oddFredholmStandardFiniteInclusion n).adjoint.toCLM.map_add,
                ← AdjointableMap.comp_apply, oddFredholmStandardFiniteInclusion_adjoint_comp_self,
                AdjointableMap.id_apply, oddKTheoryFiniteAdjoint_tail_zero, add_zero]
            · apply Subtype.ext
              change (1 - standardCountableCutoff n)
                (oddFredholmStandardFiniteInclusion n x.fst + (x.snd : _)) = (x.snd : _)
              rw [(1 - standardCountableCutoff (B := B) n).toCLM.map_add, x.snd.property]
              have hz : (1 - standardCountableCutoff n) (oddFredholmStandardFiniteInclusion n x.fst) = 0 := by
                change oddFredholmStandardFiniteInclusion n x.fst -
                  standardCountableCutoff n (oddFredholmStandardFiniteInclusion n x.fst) = 0
                rw [← AdjointableMap.comp_apply, oddFredholmStandardCutoff_mul_finiteInclusion, sub_self]
              rw [hz, zero_add]
          map_add' x y := by
            apply Prod.ext
            · exact (oddFredholmStandardFiniteInclusion n).adjoint.toCLM.map_add x y
            · exact (projectionCorestrict _ _).toCLM.map_add x y
          map_smul' c x := by
            apply Prod.ext
            · exact (oddFredholmStandardFiniteInclusion n).adjoint.toCLM.map_smul c x
            · exact (projectionCorestrict _ _).toCLM.map_smul c x }
      norm_map' x := by
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), inner_sum,
          oddKTheoryStandardFiniteSplit_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := oddKTheoryStandardFiniteSplit_inner n

theorem oddKTheoryStandardFiniteSplit_transport_supported
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    (oddKTheoryStandardFiniteSplitEquiv n).transport (U : OddFredholmStandardOperator B) =
      sumMap (oddFredholmSupportedUnitaryCompression U n hU : _) 1 := by
  have hJ (x : FiniteStandardModule B (Fin n)) :
      (U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion n x) =
        oddFredholmStandardFiniteInclusion n (oddFredholmSupportedUnitaryCompression U n hU x) := by
    have hc := oddFredholmSupportedUnitary_commutes_cutoff U n hU
    have hh := congrArg (fun T => T (oddFredholmStandardFiniteInclusion n x)) hc.eq
    rw [← AdjointableMap.comp_apply, oddFredholmStandardCutoff_mul_finiteInclusion] at hh
    simpa only [oddFredholmSupportedUnitaryCompression, AdjointableMap.comp_apply,
      ← oddFredholmStandardFiniteInclusion_comp_adjoint] using hh.symm
  have ht (x : ProjectionModule (1 - standardCountableCutoff (B := B) n)) :
      (U : OddFredholmStandardOperator B) (x : _) = (x : _) := by
    have hh := congrArg (fun T : OddFredholmStandardOperator B => T (x : _)) hU
    simpa only [AdjointableMap.mul_apply, x.property] using hh
  ext x
  change oddKTheoryStandardFiniteSplitEquiv n
    ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion n x.fst + (x.snd : _))) = _
  rw [(U : OddFredholmStandardOperator B).toCLM.map_add, hJ, ht]
  have hi := (oddKTheoryStandardFiniteSplitEquiv (B := B) n).apply_symm_apply
    (sumMk (oddFredholmSupportedUnitaryCompression U n hU x.fst) x.snd)
  simpa only [sumMap_apply, AdjointableMap.one_apply] using hi

end BC4lean.KKTheory
