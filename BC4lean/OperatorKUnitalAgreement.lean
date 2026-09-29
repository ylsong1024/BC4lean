import BC4lean.NonunitalOperatorK
import BC4lean.UnitizationSplitting
import BC4lean.OperatorK0Equivalence
import BC4lean.OperatorK1Equivalence
import BC4lean.OperatorK0Product
import BC4lean.OperatorK1Product
import BC4lean.KernelProductEquiv

/-! # Agreement of the unitization-kernel and unital definitions

Split the forced unitization as ℂ × A, split the K-groups of that product,
and identify the scalar kernel with the second factor. The construction uses
canonical spectral orders throughout.
-/
noncomputable section
namespace BC4lean.OperatorKTheory

local instance comparisonSpectralOrder (B : Type*) [CStarAlgebra B] : PartialOrder B :=
  CStarAlgebra.spectralOrder B
local instance comparisonSpectralOrderedRing (B : Type*) [CStarAlgebra B] : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

variable (A : Type*) [CStarAlgebra A]

theorem unitizationProduct_fst :
    (StarAlgHom.fst ℂ ℂ A).comp (unitizationProductEquiv A).toStarAlgHom = scalarQuotient A := by
  apply DFunLike.ext
  intro x
  rfl

theorem unitizationProduct_snd :
    (StarAlgHom.snd ℂ ℂ A).comp (unitizationProductEquiv A).toStarAlgHom = unitizationEval A := by
  apply DFunLike.ext
  intro x
  rfl

/-- The degree-zero kernel definition agrees canonically with unital projection K₀. -/
def operatorK0UnitalEquiv : OperatorK0 A ≃+ K0 A :=
  kernelProductEquiv
    ((k0Equiv (unitizationProductEquiv A)).trans (k0ProductEquiv ℂ A))
    (k0Map (scalarQuotient A)) (by
      intro x
      change k0Map (StarAlgHom.fst ℂ ℂ A) (k0Map (unitizationProductEquiv A).toStarAlgHom x) = _
      rw [← AddMonoidHom.comp_apply, ← k0Map_comp, unitizationProduct_fst])

/-- The degree-one kernel definition agrees canonically with stable unitary K₁. -/
def operatorK1UnitalEquiv : OperatorK1 A ≃+ K1 A :=
  kernelProductEquiv
    ((k1Equiv (unitizationProductEquiv A)).trans (k1ProductEquiv ℂ A))
    (k1Map (scalarQuotient A)) (by
      intro x
      change k1Map (StarAlgHom.fst ℂ ℂ A) (k1Map (unitizationProductEquiv A).toStarAlgHom x) = _
      rw [← AddMonoidHom.comp_apply, ← k1Map_comp, unitizationProduct_fst])

/-- The comparison sends a kernel class by evaluation using the original unit. -/
theorem operatorK0UnitalEquiv_apply (x : OperatorK0 A) :
    operatorK0UnitalEquiv A x = k0Map (unitizationEval A) (operatorK0Inclusion A x) := by
  change k0Map (StarAlgHom.snd ℂ ℂ A) (k0Map (unitizationProductEquiv A).toStarAlgHom x.val) = _
  rw [← AddMonoidHom.comp_apply, ← k0Map_comp, unitizationProduct_snd]
  rfl

theorem operatorK1UnitalEquiv_apply (x : OperatorK1 A) :
    operatorK1UnitalEquiv A x = k1Map (unitizationEval A) (operatorK1Inclusion A x) := by
  change k1Map (StarAlgHom.snd ℂ ℂ A) (k1Map (unitizationProductEquiv A).toStarAlgHom x.val) = _
  rw [← AddMonoidHom.comp_apply, ← k1Map_comp, unitizationProduct_snd]
  rfl

variable {A} {B : Type*} [CStarAlgebra B]

theorem unitizationEval_natural (φ : A →⋆ₐ[ℂ] B) :
    (unitizationEval B).comp (Unitization.starMap φ.toNonUnitalStarAlgHom) =
      φ.comp (unitizationEval A) := by
  ext x
  change unitizationEval B (Unitization.starMap φ.toNonUnitalStarAlgHom (x : Unitization ℂ A)) =
    φ (unitizationEval A (x : Unitization ℂ A))
  simp [unitizationEval_apply]

/-- Agreement with the unital definition is natural for unital star homomorphisms. -/
theorem operatorK0UnitalEquiv_natural (φ : A →⋆ₐ[ℂ] B) (x : OperatorK0 A) :
    operatorK0UnitalEquiv B (operatorK0Map φ.toNonUnitalStarAlgHom x) =
      k0Map φ (operatorK0UnitalEquiv A x) := by
  rw [operatorK0UnitalEquiv_apply, operatorK0UnitalEquiv_apply]
  change k0Map (unitizationEval B) (k0Map (Unitization.starMap φ.toNonUnitalStarAlgHom) x.val) =
    k0Map φ (k0Map (unitizationEval A) x.val)
  have h := congrArg k0Map (unitizationEval_natural φ)
  simpa only [k0Map_comp, AddMonoidHom.comp_apply] using DFunLike.congr_fun h x.val

theorem operatorK1UnitalEquiv_natural (φ : A →⋆ₐ[ℂ] B) (x : OperatorK1 A) :
    operatorK1UnitalEquiv B (operatorK1Map φ.toNonUnitalStarAlgHom x) =
      k1Map φ (operatorK1UnitalEquiv A x) := by
  rw [operatorK1UnitalEquiv_apply, operatorK1UnitalEquiv_apply]
  change k1Map (unitizationEval B) (k1Map (Unitization.starMap φ.toNonUnitalStarAlgHom) x.val) =
    k1Map φ (k1Map (unitizationEval A) x.val)
  have h := congrArg k1Map (unitizationEval_natural φ)
  simpa only [k1Map_comp, AddMonoidHom.comp_apply] using DFunLike.congr_fun h x.val

end BC4lean.OperatorKTheory
