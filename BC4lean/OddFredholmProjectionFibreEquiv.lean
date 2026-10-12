import BC4lean.OddFredholmModuleFibreEquiv
import BC4lean.ProjectionHilbertModule

/-! # True fibres of arbitrary projection range modules

The fibre of the actual range inclusion is an adjointable isometry. Its range
projection is exactly the evaluated ambient projection. Restricting that
actual partial isometry gives the whole range-fibre unitary, without assuming
the interval module is a continuous-section module.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace CStarAlgebra

section IsometricRange
variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- An actual adjointable isometry is unitary onto its actual projection range. -/
def oddFredholmIsometricRangeEquiv (T : AdjointableMap B E F) (Q : AdjointableMap B F F)
    (hT : T.adjoint.comp T = AdjointableMap.id) (hQ : T.comp T.adjoint = Q) :
    HilbertModuleEquiv B E (ProjectionModule Q) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := ⟨T x, by
            change Q (T x) = T x
            rw [← hQ, AdjointableMap.comp_apply, ← AdjointableMap.comp_apply T.adjoint T,
              hT, AdjointableMap.id_apply]⟩
          invFun x := T.adjoint (x : F)
          left_inv x := by
            change T.adjoint (T x) = x
            rw [← AdjointableMap.comp_apply, hT, AdjointableMap.id_apply]
          right_inv x := by
            apply Subtype.ext
            change T (T.adjoint (x : F)) = (x : F)
            rw [← AdjointableMap.comp_apply, hQ, x.property]
          map_add' x y := Subtype.ext (T.toCLM.map_add x y)
          map_smul' c x := Subtype.ext (T.toCLM.map_smul c x) }
      norm_map' x := by
        change ‖T x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (T x), T.adjoint_identity]
        change Real.sqrt ‖⟪x, T.adjoint (T x)⟫_(Bᵐᵒᵖ)‖ = ‖x‖
        rw [← AdjointableMap.comp_apply, hT, AdjointableMap.id_apply]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map x y := by
    change ⟪T x, T y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [T.adjoint_identity]
    change ⟪x, T.adjoint (T y)⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [← AdjointableMap.comp_apply, hT, AdjointableMap.id_apply]

end IsometricRange

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

def oddFredholmProjectionFibreInclusion (P : AdjointableMap C(X, B) M M)
    (hP : IsStarProjection P) (t : X) :
    AdjointableMap B (HilbertModuleFibre B (ProjectionModule P) t) (HilbertModuleFibre B M t) :=
  hilbertModuleFibreRectangularMap t (projectionInclusion P hP)

theorem oddFredholmProjectionFibreInclusion_adjoint_comp
    (P : AdjointableMap C(X, B) M M) (hP : IsStarProjection P) (t : X) :
    (oddFredholmProjectionFibreInclusion P hP t).adjoint.comp
      (oddFredholmProjectionFibreInclusion P hP t) = AdjointableMap.id := by
  rw [oddFredholmProjectionFibreInclusion, hilbertModuleFibreRectangularMap_adjoint,
    ← hilbertModuleFibreRectangularMap_comp]
  change hilbertModuleFibreRectangularMap t
    ((projectionCorestrict P hP).comp (projectionInclusion P hP)) = _
  rw [projectionCorestrict_comp_inclusion, hilbertModuleFibreRectangularMap_eq_operator]
  exact hilbertModuleFibreOperator_one t

theorem oddFredholmProjectionFibreInclusion_comp_adjoint
    (P : AdjointableMap C(X, B) M M) (hP : IsStarProjection P) (t : X) :
    (oddFredholmProjectionFibreInclusion P hP t).comp
      (oddFredholmProjectionFibreInclusion P hP t).adjoint = hilbertModuleFibreOperator (B := B) t P := by
  rw [oddFredholmProjectionFibreInclusion, hilbertModuleFibreRectangularMap_adjoint,
    ← hilbertModuleFibreRectangularMap_comp]
  change hilbertModuleFibreRectangularMap t
    ((projectionInclusion P hP).comp (projectionCorestrict P hP)) = _
  rw [projectionInclusion_comp_corestrict, hilbertModuleFibreRectangularMap_eq_operator]

/-- The actual completed fibre of the supported module equals the actual
support range of the completed ambient fibre. -/
def oddFredholmProjectionFibreEquiv (P : AdjointableMap C(X, B) M M)
    (hP : IsStarProjection P) (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (ProjectionModule P) t)
      (ProjectionModule (hilbertModuleFibreOperator (B := B) t P)) :=
  oddFredholmIsometricRangeEquiv (oddFredholmProjectionFibreInclusion P hP t)
    (hilbertModuleFibreOperator (B := B) t P)
    (oddFredholmProjectionFibreInclusion_adjoint_comp P hP t)
    (oddFredholmProjectionFibreInclusion_comp_adjoint P hP t)

@[simp] theorem oddFredholmProjectionFibreEquiv_mk
    (P : AdjointableMap C(X, B) M M) (hP : IsStarProjection P) (t : X) (x : ProjectionModule P) :
    ((oddFredholmProjectionFibreEquiv P hP t (hilbertModuleFibreMk (B := B) t x) :
      ProjectionModule (hilbertModuleFibreOperator (B := B) t P)) : HilbertModuleFibre B M t) =
      hilbertModuleFibreMk (B := B) t (x : M) :=
  hilbertModuleFibreRectangularMap_mk t (projectionInclusion P hP) x

end BC4lean.KKTheory
