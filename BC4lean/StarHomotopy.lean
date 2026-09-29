import BC4lean.OperatorK1Functoriality
import Mathlib.Analysis.CStarAlgebra.Unitization

/-! # Point-norm homotopies of complex star homomorphisms

Continuity is required separately at every fixed algebra element; no continuity
in the operator norm on the space of homomorphisms is assumed.
-/
noncomputable section
namespace BC4lean.OperatorKTheory

/-- A point-norm homotopy through unital complex star homomorphisms. -/
structure UnitalStarHomotopy {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ ψ : A →⋆ₐ[ℂ] B) where
  toFun : unitInterval → A →⋆ₐ[ℂ] B
  continuous_apply : ∀ a : A, Continuous (fun t => toFun t a)
  source : toFun 0 = φ
  target : toFun 1 = ψ

/-- A point-norm homotopy through possibly nonunital complex star homomorphisms. -/
structure StarHomotopy {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ ψ : A →⋆ₙₐ[ℂ] B) where
  toFun : unitInterval → A →⋆ₙₐ[ℂ] B
  continuous_apply : ∀ a : A, Continuous (fun t => toFun t a)
  source : toFun 0 = φ
  target : toFun 1 = ψ

namespace UnitalStarHomotopy
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable {φ ψ : A →⋆ₐ[ℂ] B}

/-- A constant family is a point-norm homotopy. -/
def refl (φ : A →⋆ₐ[ℂ] B) : UnitalStarHomotopy φ φ where
  toFun _ := φ
  continuous_apply _ := continuous_const
  source := rfl
  target := rfl

/-- Forget preservation of the unit without changing the point-norm continuity. -/
def toStarHomotopy (h : UnitalStarHomotopy φ ψ) :
    StarHomotopy φ.toNonUnitalStarAlgHom ψ.toNonUnitalStarAlgHom where
  toFun t := (h.toFun t).toNonUnitalStarAlgHom
  continuous_apply := h.continuous_apply
  source := congrArg StarAlgHom.toNonUnitalStarAlgHom h.source
  target := congrArg StarAlgHom.toNonUnitalStarAlgHom h.target

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Point-norm continuity gives norm continuity on each fixed finite matrix. -/
theorem continuous_matrixMap (h : UnitalStarHomotopy φ ψ) (M : CStarMatrix ι ι A) :
    Continuous (fun t => matrixMap (h.toFun t) M) := by
  apply CStarMatrix.ofMatrixL.continuous.comp
  exact continuous_pi (fun i => continuous_pi (fun j => h.continuous_apply (M i j)))

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- Evaluate a point-norm homotopy on a matrix projection. -/
def projectionPath (h : UnitalStarHomotopy φ ψ) (p : MatrixProjection A ι) :
    Path (matrixProjectionMap φ p) (matrixProjectionMap ψ p) where
  toFun t := matrixProjectionMap (h.toFun t) p
  continuous_toFun := (h.continuous_matrixMap p.val).subtype_mk _
  source' := by rw [h.source]
  target' := by rw [h.target]

/-- Evaluate a point-norm homotopy on a matrix unitary. -/
def unitaryPath (h : UnitalStarHomotopy φ ψ) (u : MatrixUnitary A ι) :
    Path (⟨matrixMap φ u, Unitary.map_mem (matrixMap φ) u.property⟩ : MatrixUnitary B ι)
      ⟨matrixMap ψ u, Unitary.map_mem (matrixMap ψ) u.property⟩ where
  toFun t := ⟨matrixMap (h.toFun t) u, Unitary.map_mem (matrixMap (h.toFun t)) u.property⟩
  continuous_toFun := (h.continuous_matrixMap u.val).subtype_mk _
  source' := by rw [h.source]
  target' := by rw [h.target]
end UnitalStarHomotopy

namespace StarHomotopy
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {φ ψ : A →⋆ₙₐ[ℂ] B}

def refl (φ : A →⋆ₙₐ[ℂ] B) : StarHomotopy φ φ where
  toFun _ := φ
  continuous_apply _ := continuous_const
  source := rfl
  target := rfl

/-- Forced unitization preserves point-norm homotopies. -/
def unitization (h : StarHomotopy φ ψ) :
    UnitalStarHomotopy (Unitization.starMap φ) (Unitization.starMap ψ) where
  toFun t := Unitization.starMap (h.toFun t)
  continuous_apply x := by
    have hx : (fun t => Unitization.starMap (h.toFun t) x) =
        fun t => algebraMap ℂ (Unitization ℂ B) x.fst + (h.toFun t x.snd : Unitization ℂ B) := by
      funext t
      conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq x]
      rw [map_add, Unitization.starMap_inl, Unitization.starMap_inr]
    rw [hx]
    exact continuous_const.add (Unitization.continuous_inr.comp (h.continuous_apply x.snd))
  source := congrArg Unitization.starMap h.source
  target := congrArg Unitization.starMap h.target
end StarHomotopy
end BC4lean.OperatorKTheory
