import BC4lean.ReducedCrossedScalarHilbert
import BC4lean.ReducedCrossedProduct
import BC4lean.ReducedGroupCStar

/-! # The trivial scalar crossed product is the existing reduced group algebra

The actual completed scalar module unitary intertwines translations and scalar
coefficient multiplication. Its operator star-algebra equivalence therefore
identifies the closed crossed-product algebra with the existing concrete
`ReducedGroupCStar Γ`.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace ComplexOrder ScalarHilbertModule

variable {Γ : Type*} [Group Γ]

/-- The scalar unitary intertwines the two actual regular representations. -/
theorem reducedCrossedScalarEquiv_regular (g : Γ) (x : ReducedCrossedHilbertModule ℂ Γ) :
    reducedCrossedScalarEquiv (reducedCrossedRegular g x) =
      regularOperator g (reducedCrossedScalarEquiv x) := by
  refine reducedCrossedMk_denseRange.induction_on x ?_ ?_
  · exact isClosed_eq
      (reducedCrossedScalarEquiv.continuous.comp (reducedCrossedRegular g).toCLM.continuous)
      ((regularOperator g).continuous.comp reducedCrossedScalarEquiv.continuous)
  · intro a
    rw [reducedCrossedRegular_mk, reducedCrossedScalarEquiv_mk,
      reducedCrossedScalarEquiv_mk]
    ext i
    simp only [reducedCrossedScalarFinite_apply,
      reducedCrossedRegular_finite_apply, regularOperator_apply]

/-- Trivial scalar coefficients act by their ordinary complex scalars. -/
theorem reducedCrossedScalarEquiv_coefficient (z : ℂ)
    (x : ReducedCrossedHilbertModule ℂ Γ) :
    reducedCrossedScalarEquiv
        (reducedCrossedCoefficient (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) z x) =
      z • reducedCrossedScalarEquiv x := by
  refine reducedCrossedMk_denseRange.induction_on x ?_ ?_
  · exact isClosed_eq
      (reducedCrossedScalarEquiv.continuous.comp
        (reducedCrossedCoefficient CStarAlgebraAction.trivial z).toCLM.continuous)
      (reducedCrossedScalarEquiv.continuous.const_smul z)
  · intro a
    rw [reducedCrossedCoefficient_mk, reducedCrossedScalarEquiv_mk,
      reducedCrossedScalarEquiv_mk]
    ext i
    simp [reducedCrossedScalarFinite_apply, reducedCrossedFiniteDiagonal_apply,
      CStarAlgebraAction.trivial]

/-- A scalar crossed-product generator becomes the same scalar regular operator. -/
@[simp] theorem reducedCrossedScalarOperatorEquiv_generator (z : ℂ) (g : Γ) :
    reducedCrossedScalarOperatorEquiv
      (reducedCrossedGenerator (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) z g) =
        z • regularOperator g := by
  apply ContinuousLinearMap.ext
  intro ξ
  obtain ⟨x, rfl⟩ := reducedCrossedScalarEquiv.surjective ξ
  rw [show reducedCrossedScalarEquiv x = reducedCrossedScalarHilbertEquiv x from rfl,
    reducedCrossedScalarOperatorEquiv_apply]
  change reducedCrossedScalarEquiv
    (reducedCrossedCoefficient CStarAlgebraAction.trivial z (reducedCrossedRegular g x)) = _
  rw [reducedCrossedScalarEquiv_coefficient, reducedCrossedScalarEquiv_regular]
  rfl

private theorem scalarOperatorEquiv_mem_reduced (T :
    ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) :
    reducedCrossedScalarOperatorEquiv (T : AdjointableMap ℂ
      (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) ∈
      reducedAlgebra Γ := by
  let S := (reducedAlgebra Γ).toNonUnitalStarSubalgebra.comap
    reducedCrossedScalarOperatorEquiv.toNonUnitalStarAlgHom
  have hclosed : IsClosed (S : Set (AdjointableMap ℂ
      (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ))) :=
    reducedAlgebra_isClosed.preimage
      (StarAlgEquiv.isometry (reducedCrossedScalarOperatorEquiv (Γ := Γ))).continuous
  have hsub := reducedCrossedAlgebra_minimal CStarAlgebraAction.trivial S hclosed (by
    intro z g
    change reducedCrossedScalarOperatorEquiv
      (reducedCrossedGenerator CStarAlgebraAction.trivial z g) ∈ reducedAlgebra Γ
    rw [reducedCrossedScalarOperatorEquiv_generator]
    exact (reducedAlgebra Γ).smul_mem (regularOperator_mem_reducedAlgebra g) z)
  exact hsub T.property

private theorem scalarOperatorEquiv_symm_mem_crossed (T : ReducedGroupCStar Γ) :
    reducedCrossedScalarOperatorEquiv.symm
      (T : L2Group Γ →L[ℂ] L2Group Γ) ∈
        reducedCrossedAlgebra (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) := by
  let eLin : (L2Group Γ →L[ℂ] L2Group Γ) →ₗ[ℂ]
      AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
        (ReducedCrossedHilbertModule ℂ Γ) :=
    { toFun := reducedCrossedScalarOperatorEquiv.symm
      map_add' := map_add reducedCrossedScalarOperatorEquiv.symm
      map_smul' := map_smul reducedCrossedScalarOperatorEquiv.symm }
  let S := (reducedCrossedAlgebra
    (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)).toSubmodule.comap
      eLin
  have hclosed : IsClosed (S : Set (L2Group Γ →L[ℂ] L2Group Γ)) :=
    (reducedCrossedAlgebra_isClosed CStarAlgebraAction.trivial).preimage
      (StarAlgEquiv.isometry (reducedCrossedScalarOperatorEquiv (Γ := Γ)).symm).continuous
  have hsub : Submodule.span ℂ (Set.range (regularOperator (Γ := Γ))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change reducedCrossedScalarOperatorEquiv.symm (regularOperator g) ∈
      reducedCrossedAlgebra (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
    have h := reducedCrossedGenerator_mem
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) (1 : ℂ) g
    have he : reducedCrossedScalarOperatorEquiv
        (reducedCrossedGenerator CStarAlgebraAction.trivial (1 : ℂ) g) =
          regularOperator g := by simp
    rw [← he, StarAlgEquiv.symm_apply_apply]
    exact h
  have hclosure : closure
      (Submodule.span ℂ (Set.range (regularOperator (Γ := Γ))) :
        Set (L2Group Γ →L[ℂ] L2Group Γ)) ⊆ S :=
    closure_minimal hsub hclosed
  apply hclosure
  rw [← reducedAlgebra_coe_eq_closure_span]
  exact T.property

/-- The actual scalar reduced crossed product is the established reduced group C⋆-algebra. -/
def reducedCrossedScalarProductEquiv :
    ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) ≃⋆ₐ[ℂ]
      ReducedGroupCStar Γ where
  toFun T := ⟨reducedCrossedScalarOperatorEquiv (Γ := Γ)
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)),
      scalarOperatorEquiv_mem_reduced T⟩
  invFun T := ⟨(reducedCrossedScalarOperatorEquiv (Γ := Γ)).symm
    (T : L2Group Γ →L[ℂ] L2Group Γ),
    scalarOperatorEquiv_symm_mem_crossed T⟩
  left_inv T := Subtype.ext ((reducedCrossedScalarOperatorEquiv (Γ := Γ)).symm_apply_apply
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)))
  right_inv T := Subtype.ext ((reducedCrossedScalarOperatorEquiv (Γ := Γ)).apply_symm_apply
    (T : L2Group Γ →L[ℂ] L2Group Γ))
  map_mul' S T := Subtype.ext (map_mul (reducedCrossedScalarOperatorEquiv (Γ := Γ))
    (S : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ))
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)))
  map_add' S T := Subtype.ext (map_add (reducedCrossedScalarOperatorEquiv (Γ := Γ))
    (S : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ))
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)))
  map_smul' z T := Subtype.ext (map_smul (reducedCrossedScalarOperatorEquiv (Γ := Γ)) z
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)))
  map_star' T := Subtype.ext (map_star (reducedCrossedScalarOperatorEquiv (Γ := Γ))
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)))

@[simp] theorem reducedCrossedScalarProductEquiv_coe (T :
    ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) :
    (reducedCrossedScalarProductEquiv T : L2Group Γ →L[ℂ] L2Group Γ) =
      reducedCrossedScalarOperatorEquiv T := rfl

/-- The scalar coefficient identity becomes the usual reduced group-algebra unit. -/
@[simp] theorem reducedCrossedScalarProductEquiv_oneCoefficient :
    reducedCrossedScalarProductEquiv
      (coefficientToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (1 : ℂ)) = (1 : ReducedGroupCStar Γ) := by
  apply Subtype.ext
  change reducedCrossedScalarOperatorEquiv
    (reducedCrossedCoefficient CStarAlgebraAction.trivial (1 : ℂ)) = 1
  have h := reducedCrossedScalarOperatorEquiv_generator (Γ := Γ) (1 : ℂ) (1 : Γ)
  simpa only [reducedCrossedGenerator, reducedCrossedRegular_one, mul_one,
    one_smul, regularOperator_one] using h

end BC4lean.KKTheory
