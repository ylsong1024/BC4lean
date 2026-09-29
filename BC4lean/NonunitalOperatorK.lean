import BC4lean.OperatorK0Functoriality
import BC4lean.OperatorK1Functoriality
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Operator K-groups through forced unitization

For a possibly nonunital complex C*-algebra, take the kernels of the scalar
quotient maps in degrees zero and one. All matrix orders are spectral orders.
-/
noncomputable section
namespace BC4lean.OperatorKTheory
universe u v w

local instance operatorSpectralOrder (B : Type*) [CStarAlgebra B] : PartialOrder B :=
  CStarAlgebra.spectralOrder B
local instance operatorSpectralOrderedRing (B : Type*) [CStarAlgebra B] : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

variable (A : Type u) [NonUnitalCStarAlgebra A]

/-- The scalar quotient of the forced unitization. -/
def scalarQuotient : Unitization ℂ A →⋆ₐ[ℂ] ℂ :=
  { Unitization.fstHom ℂ A with map_star' := Unitization.fst_star }

/-- The scalar inclusion is a unital section. -/
def scalarSection : ℂ →⋆ₐ[ℂ] Unitization ℂ A := StarAlgHom.ofId ℂ _

@[simp] theorem scalarQuotient_section :
    (scalarQuotient A).comp (scalarSection A) = StarAlgHom.id ℂ ℂ := by
  ext z
  rfl

/-- Degree-zero operator K-theory for a possibly nonunital algebra. -/
def OperatorK0 : Type _ := (k0Map (scalarQuotient A)).ker

/-- Degree-one operator K-theory for a possibly nonunital algebra. -/
def OperatorK1 : Type _ := (k1Map (scalarQuotient A)).ker

instance operatorK0AddCommGroup : AddCommGroup (OperatorK0 A) :=
  inferInstanceAs (AddCommGroup (k0Map (scalarQuotient A)).ker)
instance operatorK1AddCommGroup : AddCommGroup (OperatorK1 A) :=
  inferInstanceAs (AddCommGroup (k1Map (scalarQuotient A)).ker)

/-- Inclusion of the degree-zero kernel into the K-group of the unitization. -/
def operatorK0Inclusion : OperatorK0 A →+ K0 (Unitization ℂ A) :=
  (k0Map (scalarQuotient A)).ker.subtype

/-- Inclusion of the degree-one kernel into the K-group of the unitization. -/
def operatorK1Inclusion : OperatorK1 A →+ K1 (Unitization ℂ A) :=
  (k1Map (scalarQuotient A)).ker.subtype

theorem operatorK0Inclusion_injective : Function.Injective (operatorK0Inclusion A) := Subtype.val_injective
theorem operatorK1Inclusion_injective : Function.Injective (operatorK1Inclusion A) := Subtype.val_injective

theorem operatorK0_scalar_zero (x : OperatorK0 A) : k0Map (scalarQuotient A) (operatorK0Inclusion A x) = 0 := x.property
theorem operatorK1_scalar_zero (x : OperatorK1 A) : k1Map (scalarQuotient A) (operatorK1Inclusion A x) = 0 := x.property

variable {A} {B : Type v} {C : Type w} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

theorem scalarQuotient_natural (φ : A →⋆ₙₐ[ℂ] B) :
    (scalarQuotient B).comp (Unitization.starMap φ) = scalarQuotient A := by
  ext x
  change (Unitization.starMap φ (x : Unitization ℂ A)).fst = 0
  simp

def operatorK0Map (φ : A →⋆ₙₐ[ℂ] B) : OperatorK0 A →+ OperatorK0 B where
  toFun x := ⟨k0Map (Unitization.starMap φ) x.val, by
    change k0Map (scalarQuotient B) (k0Map (Unitization.starMap φ) x.val) = 0
    rw [← AddMonoidHom.comp_apply, ← k0Map_comp, scalarQuotient_natural]
    exact x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

def operatorK1Map (φ : A →⋆ₙₐ[ℂ] B) : OperatorK1 A →+ OperatorK1 B where
  toFun x := ⟨k1Map (Unitization.starMap φ) x.val, by
    change k1Map (scalarQuotient B) (k1Map (Unitization.starMap φ) x.val) = 0
    rw [← AddMonoidHom.comp_apply, ← k1Map_comp, scalarQuotient_natural]
    exact x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

@[simp] theorem operatorK0Map_id : operatorK0Map (NonUnitalStarAlgHom.id ℂ A) = AddMonoidHom.id (OperatorK0 A) := by
  ext x
  apply Subtype.ext
  change k0Map (Unitization.starMap (NonUnitalStarAlgHom.id ℂ A)) x.val = x.val
  rw [Unitization.starMap_id, k0Map_id]
  rfl

@[simp] theorem operatorK1Map_id : operatorK1Map (NonUnitalStarAlgHom.id ℂ A) = AddMonoidHom.id (OperatorK1 A) := by
  ext x
  apply Subtype.ext
  change k1Map (Unitization.starMap (NonUnitalStarAlgHom.id ℂ A)) x.val = x.val
  rw [Unitization.starMap_id, k1Map_id]
  rfl

@[simp] theorem operatorK0Map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    operatorK0Map (ψ.comp φ) = (operatorK0Map ψ).comp (operatorK0Map φ) := by
  ext x
  apply Subtype.ext
  change k0Map (Unitization.starMap (ψ.comp φ)) x.val = _
  rw [Unitization.starMap_comp, k0Map_comp]
  rfl

@[simp] theorem operatorK1Map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    operatorK1Map (ψ.comp φ) = (operatorK1Map ψ).comp (operatorK1Map φ) := by
  ext x
  apply Subtype.ext
  change k1Map (Unitization.starMap (ψ.comp φ)) x.val = _
  rw [Unitization.starMap_comp, k1Map_comp]
  rfl

end BC4lean.OperatorKTheory
