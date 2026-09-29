import BC4lean.ProjectionHomotopy
import BC4lean.StarHomotopy
import BC4lean.NonunitalOperatorK

/-! # Homotopy invariance of maps on operator K-theory -/
noncomputable section
namespace BC4lean.OperatorKTheory
section Unital
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable {φ ψ : A →⋆ₐ[ℂ] B}

/-- Point-norm homotopic unital homomorphisms have equivalent images of projections. -/
theorem finiteProjection_equivalent_of_homotopy (h : UnitalStarHomotopy φ ψ)
    (p : FiniteProjection A) : FiniteProjection.Equivalent (FiniteProjection.map φ p)
      (FiniteProjection.map ψ p) := by
  obtain ⟨v, hv, hv'⟩ := Projection.equivalent_of_path (h.projectionPath p.projection)
  change ∃ w : CStarMatrix p.Index p.Index B,
    w * star w = (matrixProjectionMap φ p.projection).val ∧
    star w * w = (matrixProjectionMap ψ p.projection).val
  exact ⟨star v, by simpa using hv, by simpa using hv'⟩

/-- Point-norm homotopic unital homomorphisms induce the same map on V(A). -/
theorem stableProjectionMap_homotopy (h : UnitalStarHomotopy φ ψ) :
    StableProjectionMonoid.map φ = StableProjectionMonoid.map ψ := by
  ext x
  refine Quotient.inductionOn x ?_
  intro p
  exact Quotient.sound (finiteProjection_equivalent_of_homotopy h p)

/-- Point-norm homotopic unital homomorphisms induce the same K₀ map. -/
theorem k0Map_homotopy (h : UnitalStarHomotopy φ ψ) : k0Map φ = k0Map ψ := by
  apply k0Hom_ext
  intro p
  rw [k0Map_projection, k0Map_projection]
  exact k0Projection_eq_of_equivalent (finiteProjection_equivalent_of_homotopy h p)

/-- Point-norm homotopic unital homomorphisms induce the same K₁ map. -/
theorem k1Map_homotopy (h : UnitalStarHomotopy φ ψ) : k1Map φ = k1Map ψ := by
  ext x
  refine Quotient.inductionOn x ?_
  intro u
  change k1Map φ (K1.of u) = k1Map ψ (K1.of u)
  rw [k1Map_of, k1Map_of]
  exact K1.of_homotopic ⟨h.unitaryPath u.val⟩
end Unital

section Nonunital
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- Point-norm homotopic possibly nonunital homomorphisms induce the same operator K₀ map. -/
theorem operatorK0Map_homotopy (h : StarHomotopy φ ψ) : operatorK0Map φ = operatorK0Map ψ := by
  let _ := CStarAlgebra.spectralOrder (Unitization ℂ A)
  let _ := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  let _ := CStarAlgebra.spectralOrder (Unitization ℂ B)
  let _ := CStarAlgebra.spectralOrderedRing (Unitization ℂ B)
  ext x
  apply Subtype.ext
  exact DFunLike.congr_fun (k0Map_homotopy h.unitization) x.val

/-- Point-norm homotopic possibly nonunital homomorphisms induce the same operator K₁ map. -/
theorem operatorK1Map_homotopy (h : StarHomotopy φ ψ) : operatorK1Map φ = operatorK1Map ψ := by
  let _ := CStarAlgebra.spectralOrder (Unitization ℂ A)
  let _ := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  let _ := CStarAlgebra.spectralOrder (Unitization ℂ B)
  let _ := CStarAlgebra.spectralOrderedRing (Unitization ℂ B)
  ext x
  apply Subtype.ext
  exact DFunLike.congr_fun (k1Map_homotopy h.unitization) x.val
end Nonunital
end BC4lean.OperatorKTheory
