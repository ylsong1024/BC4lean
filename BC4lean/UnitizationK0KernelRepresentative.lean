import BC4lean.UnitizationRelativeProjectionK0
import BC4lean.ProjectionHalmosUnitary

/-! # Finite representatives for the scalar K0 kernel

The group-completion relation supplies a common scalar projection to add to
both sides. Lifting it through the scalar section produces an actual pair
with scalar projections Murray--von Neumann equivalent. No cancellation or
rank calculation for scalar projections is used.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

local instance kernelRepresentativeSpectralOrder (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A
local instance kernelRepresentativeSpectralOrderedRing (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- Every Grothendieck class has an actual difference of finite projections. -/
theorem k0_exists_projection_difference {A : Type*} [CStarAlgebra A] (x : K0 A) :
    ∃ p q : FiniteProjection A, k0Projection p - k0Projection q = x := by
  refine AddLocalization.induction_on x ?_
  rintro ⟨a, b⟩
  obtain ⟨p, hp⟩ : ∃ p : FiniteProjection A, StableProjectionMonoid.of p = a :=
    Quotient.exists_rep a
  obtain ⟨q, hq⟩ : ∃ q : FiniteProjection A, StableProjectionMonoid.of q = (b : StableProjectionMonoid A) :=
    Quotient.exists_rep (b : StableProjectionMonoid A)
  refine ⟨p, q, ?_⟩
  rw [k0Projection, k0Projection, hp, hq]
  change AddLocalization.mk a (0 : (⊤ : AddSubmonoid (StableProjectionMonoid A))) -
      AddLocalization.mk (b : StableProjectionMonoid A)
        (0 : (⊤ : AddSubmonoid (StableProjectionMonoid A))) = AddLocalization.mk a b
  rw [sub_eq_add_neg, Algebra.GrothendieckAddGroup.neg_mk, AddLocalization.mk_add]
  simp only [AddSubmonoid.coe_zero, add_zero, zero_add]

/-- Equality in the group completion gives genuine common finite stabilization
in the projection monoid; injectivity of its canonical map is not required. -/
theorem k0_projection_eq_exists_common_projection {A : Type*} [CStarAlgebra A]
    (p q : FiniteProjection A) (h : k0Projection p = k0Projection q) :
    ∃ r : FiniteProjection A,
      FiniteProjection.Equivalent (FiniteProjection.blockSum p r) (FiniteProjection.blockSum q r) := by
  obtain ⟨c, hc⟩ := (AddLocalization.addMonoidOf
    (⊤ : AddSubmonoid (StableProjectionMonoid A))).exists_of_eq h
  obtain ⟨r, hr⟩ : ∃ r : FiniteProjection A,
      StableProjectionMonoid.of r = (c : StableProjectionMonoid A) :=
    Quotient.exists_rep (c : StableProjectionMonoid A)
  refine ⟨r, (StableProjectionMonoid.of_eq_iff _ _).mp ?_⟩
  simp only [StableProjectionMonoid.of_blockSum, hr]
  simpa only [add_comm] using hc

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- A common scalar projection is lifted through the actual scalar section. -/
theorem unitizationK0_kernel_exists_scalar_equivalent_pair (x : OperatorK0 B) :
    ∃ p q : FiniteProjection (Unitization ℂ B),
      k0Projection p - k0Projection q = operatorK0Inclusion B x ∧
      FiniteProjection.Equivalent (FiniteProjection.map (scalarQuotient B) p)
        (FiniteProjection.map (scalarQuotient B) q) := by
  obtain ⟨p, q, hpq⟩ := k0_exists_projection_difference (operatorK0Inclusion B x)
  have hs : k0Projection (FiniteProjection.map (scalarQuotient B) p) =
      k0Projection (FiniteProjection.map (scalarQuotient B) q) := by
    apply sub_eq_zero.mp
    rw [← k0Map_projection, ← k0Map_projection, ← map_sub, hpq]
    exact operatorK0_scalar_zero B x
  obtain ⟨r, hr⟩ := k0_projection_eq_exists_common_projection _ _ hs
  let R := FiniteProjection.map (scalarSection B) r
  refine ⟨FiniteProjection.blockSum p R, FiniteProjection.blockSum q R, ?_, ?_⟩
  · rw [k0Projection_blockSum, k0Projection_blockSum]
    simpa only [add_sub_add_right_eq_sub] using hpq
  · have hR : FiniteProjection.map (scalarQuotient B) R = r := by
      dsimp only [R]
      rw [← FiniteProjection.map_comp, scalarQuotient_section, FiniteProjection.map_id]
    rw [FiniteProjection.map_blockSum, FiniteProjection.map_blockSum, hR]
    exact hr

/-- After actual zero padding the scalar projections are equivalent in one
matrix algebra, so their Halmos unitary can be lifted entrywise. -/
theorem unitizationK0_kernel_exists_common_size_scalar_equivalent_pair (x : OperatorK0 B) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (p q : MatrixProjection (Unitization ℂ B) ι),
      k0Projection (FiniteProjection.ofProjection p) - k0Projection (FiniteProjection.ofProjection q) =
        operatorK0Inclusion B x ∧
      Projection.Equivalent (matrixProjectionMap (scalarQuotient B) p)
        (matrixProjectionMap (scalarQuotient B) q) := by
  obtain ⟨P, Q, hPQ, hs⟩ := unitizationK0_kernel_exists_scalar_equivalent_pair x
  let p := projectionBlockSum P.projection (Projection.zero : MatrixProjection (Unitization ℂ B) Q.Index)
  let q := projectionBlockSum (Projection.zero : MatrixProjection (Unitization ℂ B) P.Index) Q.projection
  have hP : FiniteProjection.Equivalent P (FiniteProjection.ofProjection p) :=
    rectEquivalent_stabilize P.projection
  have hQ : FiniteProjection.Equivalent Q (FiniteProjection.ofProjection q) :=
    rectEquivalent_trans (rectEquivalent_stabilize Q.projection)
      (rectEquivalent_block_comm Q.projection (Projection.zero : MatrixProjection (Unitization ℂ B) P.Index))
  refine ⟨P.Index ⊕ Q.Index, inferInstance, inferInstance, p, q, ?_, ?_⟩
  · rw [← k0Projection_eq_of_equivalent hP, ← k0Projection_eq_of_equivalent hQ]
    exact hPQ
  · change Projection.Equivalent
      (matrixProjectionMap (scalarQuotient B)
        (projectionBlockSum P.projection (Projection.zero : MatrixProjection (Unitization ℂ B) Q.Index)))
      (matrixProjectionMap (scalarQuotient B)
        (projectionBlockSum (Projection.zero : MatrixProjection (Unitization ℂ B) P.Index) Q.projection))
    rw [matrixProjectionMap_blockSum, matrixProjectionMap_blockSum,
      matrixProjectionMap_zero, matrixProjectionMap_zero]
    exact (rectEquivalent_iff_padded _ _).mp hs

/-- Every actual nonunital K0 kernel element has a genuine finite projection
pair with identical full scalar matrices. The scalar unitary is the explicit
Halmos matrix and is lifted through the proved scalar section. -/
theorem unitizationK0_kernel_exists_equal_scalar_pair (x : OperatorK0 B) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (P Q : CStarMatrix ι ι (Unitization ℂ B))
      (hP : IsStarProjection P) (hQ : IsStarProjection Q),
      unitizationScalarMatrix P = unitizationScalarMatrix Q ∧
      k0Projection (unitizationFiniteProjection P hP) -
        k0Projection (unitizationFiniteProjection Q hQ) = operatorK0Inclusion B x := by
  obtain ⟨ι, hι, dι, p, q, hpq, hs⟩ :=
    unitizationK0_kernel_exists_common_size_scalar_equivalent_pair x
  let := hι
  let := dι
  let sp := matrixProjectionMap (scalarQuotient B) p
  let sq := matrixProjectionMap (scalarQuotient B) q
  obtain ⟨v, hvp, hvq⟩ := hs
  let w := projectionHalmosUnitary sp sq v hvp hvq
  let lift : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ →⋆ₐ[ℂ]
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B) :=
    matrixMap (ι := ι ⊕ ι) (scalarSection B)
  let liftStar : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ →⋆*
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B) :=
    StarMonoidHom.ofClass lift
  let W : unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) :=
    Unitary.map liftStar w
  let p0 := projectionBlockSum p (Projection.zero : MatrixProjection (Unitization ℂ B) ι)
  let q0 := projectionBlockSum q (Projection.zero : MatrixProjection (Unitization ℂ B) ι)
  let P := unitaryProjectionConjugate W p0
  refine ⟨ι ⊕ ι, inferInstance, inferInstance, P.val, q0.val, P.property, q0.property, ?_, ?_⟩
  · change matrixMap (scalarQuotient B) P.val = matrixMap (scalarQuotient B) q0.val
    have hW : matrixMap (scalarQuotient B) W.val = w.val := by
      change matrixMap (ι := ι ⊕ ι) (scalarQuotient B)
        (matrixMap (ι := ι ⊕ ι) (scalarSection B) w.val) = w.val
      rw [← StarAlgHom.comp_apply, ← matrixMap_comp, scalarQuotient_section, matrixMap_id]
      rfl
    have hp0 : matrixMap (scalarQuotient B) p0.val = matrixBlockSum sp.val 0 := by
      exact congrArg Subtype.val
        (matrixProjectionMap_blockSum (scalarQuotient B) p
          (Projection.zero : MatrixProjection (Unitization ℂ B) ι)) |>.trans
            (by rw [matrixProjectionMap_zero]; rfl)
    have hq0 : matrixMap (scalarQuotient B) q0.val = matrixBlockSum sq.val 0 := by
      exact congrArg Subtype.val
        (matrixProjectionMap_blockSum (scalarQuotient B) q
          (Projection.zero : MatrixProjection (Unitization ℂ B) ι)) |>.trans
            (by rw [matrixProjectionMap_zero]; rfl)
    change matrixMap (scalarQuotient B) (W.val * p0.val * star W.val) = _
    rw [map_mul, map_mul, map_star, hW, hp0, hq0]
    exact projectionHalmosMatrix_conjugate sp sq v hvp hvq
  · have hP : k0Projection (FiniteProjection.ofProjection P) =
        k0Projection (FiniteProjection.ofProjection p0) :=
      (k0Projection_eq_of_equivalent
        (p := FiniteProjection.ofProjection p0) (q := FiniteProjection.ofProjection P)
        ((rectEquivalent_iff_equivalent p0 P).mpr
          (unitaryProjectionConjugate_equivalent W p0))).symm
    have hp0 : k0Projection (FiniteProjection.ofProjection p0) =
        k0Projection (FiniteProjection.ofProjection p) := by
      have h : FiniteProjection.Equivalent
          (FiniteProjection.ofProjection p) (FiniteProjection.ofProjection p0) := by
        change RectEquivalent p p0
        exact rectEquivalent_stabilize (κ := ι) p
      exact (k0Projection_eq_of_equivalent h).symm
    have hq0 : k0Projection (FiniteProjection.ofProjection q0) =
        k0Projection (FiniteProjection.ofProjection q) := by
      have h : FiniteProjection.Equivalent
          (FiniteProjection.ofProjection q) (FiniteProjection.ofProjection q0) := by
        change RectEquivalent q q0
        exact rectEquivalent_stabilize (κ := ι) q
      exact (k0Projection_eq_of_equivalent h).symm
    change k0Projection (FiniteProjection.ofProjection P) -
      k0Projection (FiniteProjection.ofProjection q0) = operatorK0Inclusion B x
    rw [hP, hp0, hq0]
    exact hpq

/-- The finite equal-scalar-pair constructor reaches every element of the
already defined scalar-quotient kernel, by the constructed normal form. -/
theorem unitizationRelativeProjectionK0_surjective (x : OperatorK0 B) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (P Q : CStarMatrix ι ι (Unitization ℂ B))
      (hP : IsStarProjection P) (hQ : IsStarProjection Q)
      (hs : unitizationScalarMatrix P = unitizationScalarMatrix Q),
      unitizationRelativeProjectionK0 P Q hP hQ hs = x := by
  obtain ⟨ι, hι, dι, P, Q, hP, hQ, hs, hx⟩ := unitizationK0_kernel_exists_equal_scalar_pair x
  let := hι
  let := dι
  refine ⟨ι, hι, dι, P, Q, hP, hQ, hs, ?_⟩
  apply operatorK0Inclusion_injective B
  rw [operatorK0Inclusion_unitizationRelativeProjectionK0]
  exact hx

end BC4lean.KKTheory
