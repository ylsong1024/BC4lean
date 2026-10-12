import BC4lean.ProjectionHilbertModule
import BC4lean.HilbertModuleSum

/-! # Actual unitary restrictions and sums of projection ranges

An ambient Hilbert-module unitary intertwining two operators restricts to their
fixed modules. The fixed module of a diagonal operator is unitarily equivalent
to the genuine Hilbert direct sum of its two fixed modules. Both statements use
the inherited coefficient inner products and their induced norms.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- Restrict a genuine ambient unitary using its exact projection intertwiner. -/
def HilbertModuleEquiv.restrictProjection (u : HilbertModuleEquiv B E F)
    (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (h : ∀ x, u (P x) = Q (u x)) :
    HilbertModuleEquiv B (ProjectionModule P) (ProjectionModule Q) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨u (x : E), by
            change Q (u (x : E)) = u (x : E)
            rw [← h, x.property]⟩
          invFun := fun y => ⟨u.symm (y : F), by
            apply u.injective
            have hh := h (u.symm (y : F))
            simp only [u.apply_symm_apply] at hh
            simpa only [u.apply_symm_apply] using hh.trans y.property⟩
          left_inv := fun x => Subtype.ext (u.symm_apply_apply (x : E))
          right_inv := fun y => Subtype.ext (u.apply_symm_apply (y : F))
          map_add' := fun x y => Subtype.ext (u.map_add (x : E) (y : E))
          map_smul' := fun c x => Subtype.ext (u.map_smul c (x : E)) }
      norm_map' x := u.norm_map (x : E) }
  inner_map x y := u.inner_map (x : E) (y : E)

@[simp] theorem HilbertModuleEquiv.restrictProjection_apply (u : HilbertModuleEquiv B E F)
    (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (h : ∀ x, u (P x) = Q (u x)) (x : ProjectionModule P) :
    ((u.restrictProjection P Q h x : ProjectionModule Q) : F) = u (x : E) := rfl

variable [StarOrderedRing B]

/-- The fixed module of a diagonal map has the actual direct-sum module norm. -/
def projectionSumRangeEquiv (P : AdjointableMap B E E) (Q : AdjointableMap B F F) :
    HilbertModuleEquiv B (ProjectionModule (sumMap P Q))
      (HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => sumMk
            ⟨(x : HilbertModuleSum B E F).fst,
              by
                change P (x : HilbertModuleSum B E F).fst = (x : HilbertModuleSum B E F).fst
                have hx : (sumMap P Q) (x : HilbertModuleSum B E F) =
                    (x : HilbertModuleSum B E F) := x.property
                have hcoord := congrArg (sumFstCLM (B := B) (E := E) (F := F))
                  ((sumMap_apply P Q (x : HilbertModuleSum B E F)).symm.trans hx)
                change P (x : HilbertModuleSum B E F).fst =
                  (x : HilbertModuleSum B E F).fst at hcoord
                exact hcoord⟩
            ⟨(x : HilbertModuleSum B E F).snd,
              by
                change Q (x : HilbertModuleSum B E F).snd = (x : HilbertModuleSum B E F).snd
                have hx : (sumMap P Q) (x : HilbertModuleSum B E F) =
                    (x : HilbertModuleSum B E F) := x.property
                have hcoord := congrArg (sumSndCLM (B := B) (E := E) (F := F))
                  ((sumMap_apply P Q (x : HilbertModuleSum B E F)).symm.trans hx)
                change Q (x : HilbertModuleSum B E F).snd =
                  (x : HilbertModuleSum B E F).snd at hcoord
                exact hcoord⟩
          invFun := fun y => ⟨sumMk (y.fst : E) (y.snd : F), by
            change (sumMap P Q) (sumMk (y.fst : E) (y.snd : F)) = sumMk (y.fst : E) (y.snd : F)
            calc
              (sumMap P Q) (sumMk (y.fst : E) (y.snd : F)) =
                  sumMk (P (y.fst : E)) (Q (y.snd : F)) :=
                sumMap_apply P Q (sumMk (B := B) (y.fst : E) (y.snd : F))
              _ = sumMk (y.fst : E) (y.snd : F) :=
                congrArg₂ (fun (a : E) (b : F) => sumMk (B := B) a b)
                  y.fst.property y.snd.property⟩
          left_inv := fun x => by apply Subtype.ext; rfl
          right_inv := fun y => by
            apply Prod.ext <;> apply Subtype.ext <;> rfl
          map_add' := fun x y => by
            apply Prod.ext <;> apply Subtype.ext <;> rfl
          map_smul' := fun c x => by
            apply Prod.ext <;> apply Subtype.ext <;> rfl }
      norm_map' x := rfl }
  inner_map _ _ := rfl

@[simp] theorem projectionSumRangeEquiv_fst (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (x : ProjectionModule (sumMap P Q)) :
    ((projectionSumRangeEquiv P Q x).fst : E) = (x : HilbertModuleSum B E F).fst := rfl

@[simp] theorem projectionSumRangeEquiv_snd (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (x : ProjectionModule (sumMap P Q)) :
    ((projectionSumRangeEquiv P Q x).snd : F) = (x : HilbertModuleSum B E F).snd := rfl

end BC4lean.KKTheory
