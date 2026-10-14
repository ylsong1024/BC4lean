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

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryFiniteAdjoint_tail_zero (n : ℕ)
    (x : ProjectionModule (1 - standardCountableCutoff (B := B) n)) :
    (oddFredholmStandardFiniteInclusion (B := B) n).adjoint
      (x : StandardCountableHilbertModule B) = 0 := by
  have hp : standardCountableCutoff (B := B) n
      (x : StandardCountableHilbertModule B) = 0 :=
    projection_complement_fixed_eq_zero (standardCountableCutoff (B := B) n) x
  have h := congrArg (fun T : AdjointableMap B (StandardCountableHilbertModule B)
      (FiniteStandardModule B (Fin n)) => T (x : StandardCountableHilbertModule B))
    (oddFredholmStandardFiniteAdjoint_comp_cutoff (B := B) n)
  simpa only [AdjointableMap.comp_apply, hp, map_zero] using h.symm

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryStandardFiniteSplit_inner (n : ℕ) (x y : StandardCountableHilbertModule B) :
    ⟪(oddFredholmStandardFiniteInclusion (B := B) n).adjoint x,
      (oddFredholmStandardFiniteInclusion (B := B) n).adjoint y⟫_(Bᵐᵒᵖ) +
      ⟪projectionCorestrict (1 - standardCountableCutoff (B := B) n)
          (standardCountableCutoff_isStarProjection (B := B) n).one_sub x,
        projectionCorestrict (1 - standardCountableCutoff (B := B) n)
          (standardCountableCutoff_isStarProjection (B := B) n).one_sub y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  have hfirst : ⟪(oddFredholmStandardFiniteInclusion (B := B) n).adjoint x,
      (oddFredholmStandardFiniteInclusion (B := B) n).adjoint y⟫_(Bᵐᵒᵖ) =
      ⟪x, standardCountableCutoff (B := B) n y⟫_(Bᵐᵒᵖ) := by
    rw [(oddFredholmStandardFiniteInclusion (B := B) n).adjoint.adjoint_identity]
    change ⟪x, (oddFredholmStandardFiniteInclusion (B := B) n).adjoint.adjoint
        ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint y)⟫_(Bᵐᵒᵖ) =
      ⟪x, standardCountableCutoff (B := B) n y⟫_(Bᵐᵒᵖ)
    rw [AdjointableMap.adjoint_adjoint, ← AdjointableMap.comp_apply,
      oddFredholmStandardFiniteInclusion_comp_adjoint]
  have htail : ⟪projectionCorestrict (1 - standardCountableCutoff (B := B) n)
        (standardCountableCutoff_isStarProjection (B := B) n).one_sub x,
      projectionCorestrict (1 - standardCountableCutoff (B := B) n)
        (standardCountableCutoff_isStarProjection (B := B) n).one_sub y⟫_(Bᵐᵒᵖ) =
      ⟪x, (1 - standardCountableCutoff (B := B) n) y⟫_(Bᵐᵒᵖ) := by
    change ⟪(1 - standardCountableCutoff (B := B) n) x, (1 - standardCountableCutoff (B := B) n) y⟫_(Bᵐᵒᵖ) = _
    have hQstar : (1 - standardCountableCutoff (B := B) n).adjoint =
        1 - standardCountableCutoff (B := B) n :=
      (standardCountableCutoff_isStarProjection (B := B) n).one_sub.isSelfAdjoint.star_eq
    have hQQ : (1 - standardCountableCutoff (B := B) n)
        ((1 - standardCountableCutoff (B := B) n) y) =
      (1 - standardCountableCutoff (B := B) n) y :=
      congrArg (fun T : OddFredholmStandardOperator B => T y)
        (standardCountableCutoff_isStarProjection (B := B) n).one_sub.isIdempotentElem.eq
    rw [(1 - standardCountableCutoff (B := B) n).adjoint_identity]
    change ⟪x, (1 - standardCountableCutoff (B := B) n).adjoint
        ((1 - standardCountableCutoff (B := B) n) y)⟫_(Bᵐᵒᵖ) =
      ⟪x, (1 - standardCountableCutoff (B := B) n) y⟫_(Bᵐᵒᵖ)
    rw [hQstar, hQQ]
  rw [hfirst, htail,
    ← CStarModule.inner_add_right (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B),
    projection_complement_apply_add]

def oddKTheoryStandardFiniteSplitEquiv (n : ℕ) : HilbertModuleEquiv B
    (StandardCountableHilbertModule B)
    (HilbertModuleSum B (FiniteStandardModule B (Fin n))
      (ProjectionModule (1 - standardCountableCutoff (B := B) n))) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := sumMk ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint x)
            (projectionCorestrict (1 - standardCountableCutoff (B := B) n)
              (standardCountableCutoff_isStarProjection (B := B) n).one_sub x)
          invFun x := oddFredholmStandardFiniteInclusion (B := B) n x.fst + (x.snd : _)
          left_inv x := by
            change oddFredholmStandardFiniteInclusion (B := B) n
                ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint x) +
              (1 - standardCountableCutoff (B := B) n) x = x
            have hJJ : oddFredholmStandardFiniteInclusion (B := B) n
                ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint x) =
              standardCountableCutoff (B := B) n x :=
              congrArg (fun T : OddFredholmStandardOperator B => T x)
                (oddFredholmStandardFiniteInclusion_comp_adjoint (B := B) n)
            rw [hJJ]
            exact projection_complement_apply_add (standardCountableCutoff (B := B) n) x
          right_inv x := by
            change sumMk
                ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint
                  (oddFredholmStandardFiniteInclusion (B := B) n x.fst +
                    (x.snd : StandardCountableHilbertModule B)))
                (projectionCorestrict (1 - standardCountableCutoff (B := B) n)
                  (standardCountableCutoff_isStarProjection (B := B) n).one_sub
                  (oddFredholmStandardFiniteInclusion (B := B) n x.fst +
                    (x.snd : StandardCountableHilbertModule B))) = x
            apply (WithCStarModule.equiv Bᵐᵒᵖ
              (FiniteStandardModule B (Fin n) × ProjectionModule
                (1 - standardCountableCutoff (B := B) n))).injective
            apply Prod.ext
            · change (oddFredholmStandardFiniteInclusion (B := B) n).adjoint
                  (oddFredholmStandardFiniteInclusion (B := B) n x.fst +
                    (x.snd : StandardCountableHilbertModule B)) = x.fst
              rw [(oddFredholmStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_add,
                ← AdjointableMap.comp_apply, oddFredholmStandardFiniteInclusion_adjoint_comp_self,
                AdjointableMap.id_apply, oddKTheoryFiniteAdjoint_tail_zero, add_zero]
            · apply Subtype.ext
              change (1 - standardCountableCutoff (B := B) n)
                (oddFredholmStandardFiniteInclusion (B := B) n x.fst + (x.snd : _)) = (x.snd : _)
              rw [(1 - standardCountableCutoff (B := B) n).toCLM.map_add, x.snd.property]
              have hz : (1 - standardCountableCutoff (B := B) n) (oddFredholmStandardFiniteInclusion (B := B) n x.fst) = 0 := by
                rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply]
                have hPJ : standardCountableCutoff (B := B) n
                    (oddFredholmStandardFiniteInclusion (B := B) n x.fst) =
                  oddFredholmStandardFiniteInclusion (B := B) n x.fst :=
                  congrArg (fun T : AdjointableMap B (FiniteStandardModule B (Fin n))
                    (StandardCountableHilbertModule B) => T x.fst)
                    (oddFredholmStandardCutoff_mul_finiteInclusion (B := B) n)
                rw [hPJ, sub_self]
              rw [hz, zero_add]
          map_add' x y := by
            apply Prod.ext
            · exact (oddFredholmStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_add x y
            · exact (projectionCorestrict _ _).toCLM.map_add x y
          map_smul' c x := by
            apply Prod.ext
            · exact (oddFredholmStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_smul c x
            · exact (projectionCorestrict _ _).toCLM.map_smul c x }
      norm_map' x := by
        change ‖sumMk ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint x)
          (projectionCorestrict (1 - standardCountableCutoff (B := B) n)
            (standardCountableCutoff_isStarProjection (B := B) n).one_sub x)‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
          (sumMk ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint x)
            (projectionCorestrict (1 - standardCountableCutoff (B := B) n)
              (standardCountableCutoff_isStarProjection (B := B) n).one_sub x))]
        change Real.sqrt ‖⟪(oddFredholmStandardFiniteInclusion (B := B) n).adjoint x,
            (oddFredholmStandardFiniteInclusion (B := B) n).adjoint x⟫_(Bᵐᵒᵖ) +
          ⟪projectionCorestrict (1 - standardCountableCutoff (B := B) n)
              (standardCountableCutoff_isStarProjection (B := B) n).one_sub x,
            projectionCorestrict (1 - standardCountableCutoff (B := B) n)
              (standardCountableCutoff_isStarProjection (B := B) n).one_sub x⟫_(Bᵐᵒᵖ)‖ = ‖x‖
        rw [oddKTheoryStandardFiniteSplit_inner (B := B) n x x]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := oddKTheoryStandardFiniteSplit_inner (B := B) n

set_option maxHeartbeats 4000000 in
omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryStandardFiniteSplit_transport_supported
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff (B := B) n) =
      1 - standardCountableCutoff (B := B) n) :
    (oddKTheoryStandardFiniteSplitEquiv (B := B) n).transport (U : OddFredholmStandardOperator B) =
      sumMap (oddFredholmSupportedUnitaryCompression U n hU :
        AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))
        (1 : AdjointableMap B (ProjectionModule (1 - standardCountableCutoff (B := B) n))
          (ProjectionModule (1 - standardCountableCutoff (B := B) n))) := by
  have hJ (x : FiniteStandardModule B (Fin n)) :
      (U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x) =
        oddFredholmStandardFiniteInclusion (B := B) n
          ((oddFredholmSupportedUnitaryCompression U n hU :
            AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) x) := by
    have hc := oddFredholmSupportedUnitary_commutes_cutoff U n hU
    have hh := congrArg (fun T : OddFredholmStandardOperator B =>
      T (oddFredholmStandardFiniteInclusion (B := B) n x)) hc.eq
    change standardCountableCutoff (B := B) n
        ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x)) =
      (U : OddFredholmStandardOperator B)
        (standardCountableCutoff (B := B) n (oddFredholmStandardFiniteInclusion (B := B) n x)) at hh
    have hPJ : standardCountableCutoff (B := B) n
        (oddFredholmStandardFiniteInclusion (B := B) n x) =
      oddFredholmStandardFiniteInclusion (B := B) n x :=
      congrArg (fun T : AdjointableMap B (FiniteStandardModule B (Fin n))
        (StandardCountableHilbertModule B) => T x)
        (oddFredholmStandardCutoff_mul_finiteInclusion (B := B) n)
    rw [hPJ] at hh
    have hJJ : oddFredholmStandardFiniteInclusion (B := B) n
        ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint
          ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x))) =
      standardCountableCutoff (B := B) n
        ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x)) :=
      congrArg (fun T : OddFredholmStandardOperator B =>
        T ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x)))
        (oddFredholmStandardFiniteInclusion_comp_adjoint (B := B) n)
    change (U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x) =
      oddFredholmStandardFiniteInclusion (B := B) n
        ((oddFredholmStandardFiniteInclusion (B := B) n).adjoint
          ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x)))
    exact hh.symm.trans hJJ.symm
  have ht (x : ProjectionModule (1 - standardCountableCutoff (B := B) n)) :
      (U : OddFredholmStandardOperator B) (x : _) = (x : _) := by
    have hh := congrArg (fun T : OddFredholmStandardOperator B =>
      T (x : StandardCountableHilbertModule B)) hU
    change (U : OddFredholmStandardOperator B)
        ((1 - standardCountableCutoff (B := B) n) (x : StandardCountableHilbertModule B)) =
      (1 - standardCountableCutoff (B := B) n) (x : StandardCountableHilbertModule B) at hh
    have hx : (1 - standardCountableCutoff (B := B) n) (x : StandardCountableHilbertModule B) =
        (x : StandardCountableHilbertModule B) := x.property
    rw [hx] at hh
    exact hh
  apply AdjointableMap.ext
  intro x
  change oddKTheoryStandardFiniteSplitEquiv (B := B) n
    ((U : OddFredholmStandardOperator B) (oddFredholmStandardFiniteInclusion (B := B) n x.fst + (x.snd : _))) = _
  rw [(U : OddFredholmStandardOperator B).toCLM.map_add, hJ, ht]
  have hi := (oddKTheoryStandardFiniteSplitEquiv (B := B) n).apply_symm_apply
    (sumMk ((oddFredholmSupportedUnitaryCompression U n hU :
      AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) x.fst) x.snd)
  change oddKTheoryStandardFiniteSplitEquiv (B := B) n
      (oddFredholmStandardFiniteInclusion (B := B) n
        ((oddFredholmSupportedUnitaryCompression U n hU :
          AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) x.fst) +
        (x.snd : StandardCountableHilbertModule B)) =
    sumMk ((oddFredholmSupportedUnitaryCompression U n hU :
      AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) x.fst) x.snd at hi
  simpa only [sumMap_apply, AdjointableMap.one_apply] using hi

end BC4lean.KKTheory
