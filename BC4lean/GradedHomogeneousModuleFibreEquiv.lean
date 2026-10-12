import BC4lean.ProjectionIntertwiningHilbertModuleEquiv
import BC4lean.OddFredholmProjectionFibreEquiv
import BC4lean.IntervalKasparovFibre

/-! # Actual completed fibres of the homogeneous grading ranges

The actual projection-range fibre equivalence identifies each global
homogeneous module with the corresponding homogeneous module of the genuine
evaluated grading. Rectangular odd blocks evaluate through both whole range
unitaries; no continuous-section-module presentation is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

/-- Opaque carrier normalization for an identity intertwiner on the whole range.
The source and ambient module carriers are independent; only the projection
range changes its presentation under the given intertwining equality. -/
private theorem projectionIntertwining_refl_trans_coe
    {B U V : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [NormedAddCommGroup U] [NormedSpace ℂ U] [SMul Bᵐᵒᵖ U] [CStarModule Bᵐᵒᵖ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [SMul Bᵐᵒᵖ V] [CStarModule Bᵐᵒᵖ V]
    (P Q : AdjointableMap B V V) (u : HilbertModuleEquiv B U (ProjectionModule P))
    (h : ∀ x : V, (HilbertModuleEquiv.refl (B := B) : HilbertModuleEquiv B V V) (P x) =
      Q ((HilbertModuleEquiv.refl (B := B) : HilbertModuleEquiv B V V) x)) (z : U) :
    ((u.trans (projectionIntertwiningHilbertModuleEquiv (HilbertModuleEquiv.refl (B := B))
      P Q h) z : ProjectionModule Q) : V) = (u z : V) := by
  rw [HilbertModuleEquiv.trans_apply, projectionIntertwiningHilbertModuleEquiv_coe,
    HilbertModuleEquiv.refl_apply]

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

namespace GradedHilbertModule
variable (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)

omit [T2Space X] in
/-- The actual even projection evaluates to the even projection of the actual grading. -/
theorem evenProjection_fibre (t : X) :
    hilbertModuleFibreOperator (B := B) t γ.evenProjection = (γ.fibre t).evenProjection := by
  change hilbertModuleFibreOperator t ((2 : ℂ)⁻¹ • (1 + γ.toAdjointable)) =
    (2 : ℂ)⁻¹ • (1 + hilbertModuleFibreOperator t γ.toAdjointable)
  rw [hilbertModuleFibreOperator_smul, hilbertModuleFibreOperator_add, hilbertModuleFibreOperator_one]

omit [T2Space X] in
/-- The actual odd projection evaluates to the odd projection of the actual grading. -/
theorem oddProjection_fibre (t : X) :
    hilbertModuleFibreOperator (B := B) t γ.oddProjection = (γ.fibre t).oddProjection := by
  change hilbertModuleFibreOperator t (1 - γ.evenProjection) = 1 - (γ.fibre t).evenProjection
  rw [hilbertModuleFibreOperator_sub, hilbertModuleFibreOperator_one, γ.evenProjection_fibre]

/-- The true even homogeneous module fibre unitary. -/
def evenModuleFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B γ.EvenModule t) (γ.fibre t).EvenModule :=
  (oddFredholmProjectionFibreEquiv γ.evenProjection γ.evenProjection_isStarProjection t).trans
    (projectionIntertwiningHilbertModuleEquiv (HilbertModuleEquiv.refl (B := B))
      (hilbertModuleFibreOperator t γ.evenProjection) (γ.fibre t).evenProjection
      (fun x => by
        simpa only [HilbertModuleEquiv.refl_apply] using
          congrArg (fun P : AdjointableMap B (HilbertModuleFibre B M t)
            (HilbertModuleFibre B M t) => P x) (γ.evenProjection_fibre t)))

/-- The true odd homogeneous module fibre unitary. -/
def oddModuleFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B γ.OddModule t) (γ.fibre t).OddModule :=
  (oddFredholmProjectionFibreEquiv γ.oddProjection γ.oddProjection_isStarProjection t).trans
    (projectionIntertwiningHilbertModuleEquiv (HilbertModuleEquiv.refl (B := B))
      (hilbertModuleFibreOperator t γ.oddProjection) (γ.fibre t).oddProjection
      (fun x => by
        simpa only [HilbertModuleEquiv.refl_apply] using
          congrArg (fun P : AdjointableMap B (HilbertModuleFibre B M t)
            (HilbertModuleFibre B M t) => P x) (γ.oddProjection_fibre t)))

@[simp] theorem evenModuleFibreEquiv_mk_coe (t : X) (x : γ.EvenModule) :
    ((γ.evenModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t x) :
      (γ.fibre t).EvenModule) : HilbertModuleFibre B M t) = hilbertModuleFibreMk (B := B) t (x : M) := by
  exact (projectionIntertwining_refl_trans_coe
    (hilbertModuleFibreOperator t γ.evenProjection) (γ.fibre t).evenProjection
    (oddFredholmProjectionFibreEquiv γ.evenProjection γ.evenProjection_isStarProjection t)
    (fun y => by
      simpa only [HilbertModuleEquiv.refl_apply] using
        congrArg (fun P : AdjointableMap B (HilbertModuleFibre B M t)
          (HilbertModuleFibre B M t) => P y) (γ.evenProjection_fibre t))
    (hilbertModuleFibreMk (B := B) t x)).trans
      (oddFredholmProjectionFibreEquiv_mk γ.evenProjection
        γ.evenProjection_isStarProjection t x)

@[simp] theorem oddModuleFibreEquiv_mk_coe (t : X) (x : γ.OddModule) :
    ((γ.oddModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t x) :
      (γ.fibre t).OddModule) : HilbertModuleFibre B M t) = hilbertModuleFibreMk (B := B) t (x : M) := by
  exact (projectionIntertwining_refl_trans_coe
    (hilbertModuleFibreOperator t γ.oddProjection) (γ.fibre t).oddProjection
    (oddFredholmProjectionFibreEquiv γ.oddProjection γ.oddProjection_isStarProjection t)
    (fun y => by
      simpa only [HilbertModuleEquiv.refl_apply] using
        congrArg (fun P : AdjointableMap B (HilbertModuleFibre B M t)
          (HilbertModuleFibre B M t) => P y) (γ.oddProjection_fibre t))
    (hilbertModuleFibreMk (B := B) t x)).trans
      (oddFredholmProjectionFibreEquiv_mk γ.oddProjection
        γ.oddProjection_isStarProjection t x)

/-- The whole genuine rectangular odd block evaluates through both homogeneous fibres. -/
theorem homogeneousOddMap_fibre (t : X) (T : AdjointableMap C(X, B) M M)
    (hOdd : γ.IsOdd γ T) :
    (γ.evenModuleFibreEquiv t).transportMap (γ.oddModuleFibreEquiv t)
      (hilbertModuleFibreRectangularMap t (γ.homogeneousOddMap T)) =
        (γ.fibre t).homogeneousOddMap (hilbertModuleFibreOperator t T) := by
  apply AdjointableMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (γ.evenModuleFibreEquiv t).surjective x
  obtain ⟨v, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := γ.EvenModule) t z
  apply Subtype.ext
  simp only [HilbertModuleEquiv.transportMap_apply, HilbertModuleEquiv.symm_apply_apply,
    hilbertModuleFibreRectangularMap_mk, γ.oddModuleFibreEquiv_mk_coe,
    γ.homogeneousOddMap_coe T hOdd,
    (γ.fibre t).homogeneousOddMap_coe (hilbertModuleFibreOperator t T) (γ.isOdd_fibre t hOdd),
    γ.evenModuleFibreEquiv_mk_coe, hilbertModuleFibreOperator_mk]

end GradedHilbertModule
end BC4lean.KKTheory
