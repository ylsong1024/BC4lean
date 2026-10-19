import BC4lean.ScalarKasparovK0ComparisonNaturality
import BC4lean.GroupUniverseParityMapCoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Scalar K0 comparison for the actual native parity coefficient map

The native coefficient map is the established
homomorphism-cycle product. Its existing graded coherence identifies it with
the independently constructed ordinary scalar coefficient map. The proved
scalar index naturality therefore applies to that exact native product map.
No equality between coefficient maps is assumed.
-/

noncomputable section
universe uB uC u
namespace BC4lean.Assembly
open KKTheory OperatorKTheory
open KKTheory.GroupUniverseParityGroup
open KKTheory.GroupUniverseParityFunctoriality
open scoped ComplexOrder

variable {B : Type uB} {C : Type uC}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]

/-- Coherence with the actual graded product identifies these native maps. -/
theorem scalar_native_coefficientPushforward_eq
    (f : B →⋆ₙₐ[ℂ] C)
    (x : KasparovHomotopyClass.{0, 0, uB, max u (max uB uC)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) :
    coefficientPushforward.{0, 0, uB, uC, u} false f (fun _ _ => rfl) x =
      GroupUniverseOrdinaryEven.coefficientPushforward f x := by
  let hact : ∀ (k : Unit) (b : B),
      f ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B).automorphism k b) =
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C).automorphism k (f b) :=
    fun _ _ => rfl
  let y : GradedKasparovHomotopyClass.{0, 0, uC, max u (max uB uC)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C)
      CStarGrading.trivial CStarGrading.trivial :=
    GroupUniverseCoefficientPushforward.coefficientPushforward.{0, 0, uB, uC, max u (max uB uC)}
      (Γ := Unit) (A := ℂ) (B := B) (C := C)
      (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
      (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))
      (γ := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C))
      (δA := CStarGrading.trivial) (δB := CStarGrading.trivial) (δC := CStarGrading.trivial)
      (CStarAlgebraAction.preservesGrading_trivial
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))
      (CStarAlgebraAction.preservesGrading_trivial
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C))
      f hact (fun _ => rfl) (GroupUniverseEvenBridge.gradedClass x)
  have hnative : GroupUniverseEvenBridge.gradedClass
      (coefficientPushforward.{0, 0, uB, uC, u} false f hact x) = y :=
    coefficientPushforward_graded_even.{0, 0, uB, uC, u}
      (Γ := Unit) (A := ℂ) (B := B) (C := C)
      (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
      (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))
      (γ := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C)) f hact x
  have hordinary : GroupUniverseEvenBridge.gradedClass
      (GroupUniverseOrdinaryEven.coefficientPushforward f x) = y :=
    GroupUniverseEvenBridge.gradedClass_evenClass.{0, 0, uC, max u (max uB uC)}
      (Γ := Unit) (A := ℂ) (B := C)
      (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
      (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C)) y
  exact (GroupUniverseEvenBridge.gradedClass_injective.{0, 0, uC, max u (max uB uC)}
    (Γ := Unit) (A := ℂ) (B := C)
    (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
    (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C)))
      (hnative.trans hordinary.symm)

/-- Naturality of the genuine scalar comparison for the native product-defined
coefficient map at the exact common module universe. -/
theorem scalarKKOperatorK0_native_coefficient_natural
    (f : B →⋆ₙₐ[ℂ] C)
    (x : KasparovHomotopyClass.{0, 0, uB, max u (max uB uC)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) :
    scalarKKOperatorK0AddEquiv
        (coefficientPushforward.{0, 0, uB, uC, u} false f (fun _ _ => rfl) x) =
      operatorK0Map f (scalarKKOperatorK0AddEquiv x) := by
  rw [scalar_native_coefficientPushforward_eq]
  exact scalarKKOperatorK0AddEquiv_natural f x

end BC4lean.Assembly
