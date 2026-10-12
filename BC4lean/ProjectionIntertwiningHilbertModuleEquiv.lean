import BC4lean.ProjectionHilbertModule
import BC4lean.GradedHilbertModuleHomogeneousSplit

/-! # Whole range unitaries from genuine intertwining module unitaries

A whole module unitary intertwining two bounded projections restricts to
their actual closed fixed-point modules. A grading-intertwining unitary
therefore restricts to both actual homogeneous modules.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The whole actual range unitary determined by a genuine intertwiner. -/
def projectionIntertwiningHilbertModuleEquiv (u : HilbertModuleEquiv B E F)
    (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (h : ∀ x, u (P x) = Q (u x)) :
    HilbertModuleEquiv B (ProjectionModule P) (ProjectionModule Q) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := ⟨u (x : E), by
            change Q (u (x : E)) = u (x : E)
            have hx : P (x : E) = (x : E) := x.property
            rw [← h, hx]⟩
          invFun y := ⟨u.symm (y : F), by
            change P (u.symm (y : F)) = u.symm (y : F)
            have hy : Q (y : F) = (y : F) := y.property
            apply u.injective
            rw [h, u.apply_symm_apply]
            exact hy⟩
          left_inv x := Subtype.ext (u.symm_apply_apply (x : E))
          right_inv y := Subtype.ext (u.apply_symm_apply (y : F))
          map_add' x y := Subtype.ext (u.map_add (x : E) (y : E))
          map_smul' c x := Subtype.ext (u.map_smul c (x : E)) }
      norm_map' x := u.norm_map (x : E) }
  inner_map x y := u.inner_map (x : E) (y : E)

omit [StarOrderedRing B] in
@[simp] theorem projectionIntertwiningHilbertModuleEquiv_coe (u : HilbertModuleEquiv B E F)
    (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (h : ∀ x, u (P x) = Q (u x)) (x : ProjectionModule P) :
    ((projectionIntertwiningHilbertModuleEquiv u P Q h x : ProjectionModule Q) : F) = u (x : E) := rfl

namespace GradedHilbertModule
variable (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
  (δ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) F)
  (u : HilbertModuleEquiv B E F) (hu : ∀ x, u (γ.grading x) = δ.grading (u x))

omit [StarOrderedRing B] in
include hu in
/-- Grading intertwining preserves the actual even projection. -/
theorem evenProjection_intertwine (x : E) : u (γ.evenProjection x) = δ.evenProjection (u x) := by
  change u ((2 : ℂ)⁻¹ • (x + γ.grading x)) = (2 : ℂ)⁻¹ • (u x + δ.grading (u x))
  rw [HilbertModuleEquiv.map_smul, HilbertModuleEquiv.map_add, hu]

omit [StarOrderedRing B] in
include hu in
/-- Grading intertwining preserves the actual odd projection. -/
theorem oddProjection_intertwine (x : E) : u (γ.oddProjection x) = δ.oddProjection (u x) := by
  simp only [oddProjection, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    HilbertModuleEquiv.map_sub, γ.evenProjection_intertwine δ u hu]

/-- The true even homogeneous range unitary. -/
def evenModuleEquiv : HilbertModuleEquiv B γ.EvenModule δ.EvenModule :=
  projectionIntertwiningHilbertModuleEquiv u γ.evenProjection δ.evenProjection
    (γ.evenProjection_intertwine δ u hu)

/-- The true odd homogeneous range unitary. -/
def oddModuleEquiv : HilbertModuleEquiv B γ.OddModule δ.OddModule :=
  projectionIntertwiningHilbertModuleEquiv u γ.oddProjection δ.oddProjection
    (γ.oddProjection_intertwine δ u hu)

omit [StarOrderedRing B] in
@[simp] theorem evenModuleEquiv_coe (x : γ.EvenModule) :
    ((γ.evenModuleEquiv δ u hu x : δ.EvenModule) : F) = u (x : E) := rfl
omit [StarOrderedRing B] in
@[simp] theorem oddModuleEquiv_coe (x : γ.OddModule) :
    ((γ.oddModuleEquiv δ u hu x : δ.OddModule) : F) = u (x : E) := rfl


omit [StarOrderedRing B] in
/-- Whole operator intertwining restricts to the genuine homogeneous rectangular blocks. -/
theorem homogeneousOddMap_intertwine (T : AdjointableMap B E E) (S : AdjointableMap B F F)
    (hT : γ.IsOdd γ T) (hS : δ.IsOdd δ S) (hOperator : ∀ x, u (T x) = S (u x)) :
    (γ.evenModuleEquiv δ u hu).transportMap (γ.oddModuleEquiv δ u hu)
      (γ.homogeneousOddMap T) = δ.homogeneousOddMap S := by
  apply AdjointableMap.ext
  intro x
  rw [HilbertModuleEquiv.transportMap_apply]
  apply Subtype.ext
  rw [γ.oddModuleEquiv_coe δ u hu, γ.homogeneousOddMap_coe T hT,
    δ.homogeneousOddMap_coe S hS, hOperator]
  change S (u (u.symm (x : F))) = S (x : F)
  rw [HilbertModuleEquiv.apply_symm_apply]

end GradedHilbertModule
end BC4lean.KKTheory
