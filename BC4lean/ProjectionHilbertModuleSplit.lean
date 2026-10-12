import BC4lean.ProjectionHilbertModule
import BC4lean.HilbertModuleSum

/-! # The actual orthogonal decomposition by a module projection

The forward map consists of the actual projection corestrictions, and the
inverse adds the two included range vectors. The coefficient-valued inner
product identity proves its genuine Hilbert-module isometry.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

omit [StarOrderedRing B] in
@[simp] theorem projection_complement_fixed_eq_zero (P : AdjointableMap B E E)
    (x : ProjectionModule (1 - P)) : P (x : E) = 0 := by
  have hx : (1 - P) (x : E) = (x : E) := x.property
  rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply] at hx
  exact sub_eq_self.mp hx

omit [StarOrderedRing B] in
@[simp] theorem projection_complement_apply_fixed (P : AdjointableMap B E E)
    (x : ProjectionModule P) : (1 - P) (x : E) = 0 := by
  rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, x.property, sub_self]

omit [StarOrderedRing B] in
theorem projection_complement_apply_add (P : AdjointableMap B E E) (x : E) :
    P x + (1 - P) x = x := by
  rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply]
  abel

omit [StarOrderedRing B] in
/-- The two actual orthogonal projection parts preserve the full inner product. -/
theorem projection_split_inner (P : AdjointableMap B E E) (hP : IsStarProjection P) (x y : E) :
    ⟪P x, P y⟫_(Bᵐᵒᵖ) + ⟪(1 - P) x, (1 - P) y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  have hPstar : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hQstar : (1 - P).adjoint = 1 - P := hP.one_sub.isSelfAdjoint.star_eq
  have hPP : P (P y) = P y := congrArg (fun T => T y) hP.isIdempotentElem.eq
  have hQQ : (1 - P) ((1 - P) y) = (1 - P) y :=
    congrArg (fun T => T y) hP.one_sub.isIdempotentElem.eq
  rw [P.adjoint_identity, (1 - P).adjoint_identity]
  change ⟪x, P.adjoint (P y)⟫_(Bᵐᵒᵖ) +
    ⟪x, (1 - P).adjoint ((1 - P) y)⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
  rw [hPstar, hQstar, hPP, hQQ,
    ← CStarModule.inner_add_right, projection_complement_apply_add]

/-- Every genuine selfadjoint module projection gives the actual orthogonal
decomposition E≃Range(P)⊕Range(1-P). -/
def projectionModuleSplitEquiv (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    HilbertModuleEquiv B E (HilbertModuleSum B (ProjectionModule P) (ProjectionModule (1 - P))) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => sumMk (projectionCorestrict P hP x) (projectionCorestrict (1 - P) hP.one_sub x)
          invFun := fun x => (x.fst : E) + (x.snd : E)
          left_inv := projection_complement_apply_add P
          right_inv := fun x => by
            apply Prod.ext
            · apply Subtype.ext
              change P ((x.fst : E) + (x.snd : E)) = (x.fst : E)
              rw [P.toCLM.map_add, x.fst.property, projection_complement_fixed_eq_zero, add_zero]
            · apply Subtype.ext
              change (1 - P) ((x.fst : E) + (x.snd : E)) = (x.snd : E)
              rw [(1 - P).toCLM.map_add, projection_complement_apply_fixed, x.snd.property, zero_add]
          map_add' := fun x y => by
            apply Prod.ext <;> exact map_add _ x y
          map_smul' := fun c x => by
            apply Prod.ext <;> exact map_smul _ c x }
      norm_map' x := by
        change ‖sumMk (projectionCorestrict P hP x)
          (projectionCorestrict (1 - P) hP.one_sub x)‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
          (sumMk (projectionCorestrict P hP x) (projectionCorestrict (1 - P) hP.one_sub x))]
        change Real.sqrt ‖⟪P x, P x⟫_(Bᵐᵒᵖ) +
          ⟪(1 - P) x, (1 - P) x⟫_(Bᵐᵒᵖ)‖ = ‖x‖
        rw [projection_split_inner P hP x x]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map x y := projection_split_inner P hP x y

@[simp] theorem projectionModuleSplitEquiv_apply (P : AdjointableMap B E E)
    (hP : IsStarProjection P) (x : E) :
    projectionModuleSplitEquiv P hP x =
      sumMk (projectionCorestrict P hP x) (projectionCorestrict (1 - P) hP.one_sub x) := rfl

@[simp] theorem projectionModuleSplitEquiv_symm_apply (P : AdjointableMap B E E)
    (hP : IsStarProjection P) (x : HilbertModuleSum B (ProjectionModule P) (ProjectionModule (1 - P))) :
    (projectionModuleSplitEquiv P hP).symm x = (x.fst : E) + (x.snd : E) := rfl

end BC4lean.KKTheory
