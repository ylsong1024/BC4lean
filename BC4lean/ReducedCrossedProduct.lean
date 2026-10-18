import BC4lean.ReducedCrossedRegularOperators

/-! # The concrete reduced crossed product

The reduced crossed product is the closed nonunital star subalgebra generated
by the concrete regular operators π(b)λ(g) on the coefficient Hilbert module.
The coefficient algebra may be nonunital and the discrete group arbitrary.
No representation, norm, or existence statement is supplied as an assumption.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- The regular operator associated to one finite-support coefficient. -/
def reducedCrossedGenerator (α : CStarAlgebraAction Γ B) (b : B) (g : Γ) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  reducedCrossedCoefficient α b * reducedCrossedRegular g

@[simp] theorem reducedCrossedGenerator_mul (α : CStarAlgebraAction Γ B)
    (b c : B) (g h : Γ) :
    reducedCrossedGenerator α b g * reducedCrossedGenerator α c h =
      reducedCrossedGenerator α (b * α.automorphism g c) (g * h) := by
  unfold reducedCrossedGenerator
  calc
    _ = reducedCrossedCoefficient α b *
        (reducedCrossedRegular g * reducedCrossedCoefficient α c) * reducedCrossedRegular h :=
      by simp only [mul_assoc]
    _ = reducedCrossedCoefficient α b *
        (reducedCrossedCoefficient α (α.automorphism g c) * reducedCrossedRegular g) *
          reducedCrossedRegular h := by rw [← reducedCrossed_covariance]
    _ = (reducedCrossedCoefficient α b * reducedCrossedCoefficient α (α.automorphism g c)) *
        (reducedCrossedRegular g * reducedCrossedRegular h) := by simp only [mul_assoc]
    _ = _ := by
      rw [← reducedCrossedRegular_mul]
      exact congrArg (fun T => T * reducedCrossedRegular (g * h))
        (map_mul (reducedCrossedCoefficientHom α) b (α.automorphism g c)).symm

@[simp] theorem reducedCrossedGenerator_star (α : CStarAlgebraAction Γ B)
    (b : B) (g : Γ) :
    star (reducedCrossedGenerator α b g) =
      reducedCrossedGenerator α (α.automorphism g⁻¹ (star b)) g⁻¹ := by
  simp only [reducedCrossedGenerator, star_mul, reducedCrossedRegular_star,
    ← reducedCrossedCoefficient_star]
  exact (reducedCrossed_covariance α g⁻¹ (star b)).symm

/-- The actual operator-norm closed regular crossed-product algebra. -/
def reducedCrossedAlgebra (α : CStarAlgebraAction Γ B) :
    NonUnitalStarSubalgebra ℂ
      (AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) :=
  (NonUnitalStarAlgebra.adjoin ℂ
    (Set.range (fun p : B × Γ => reducedCrossedGenerator α p.1 p.2))).topologicalClosure

/-- The reduced crossed product of a possibly nonunital coefficient C⋆-algebra. -/
abbrev ReducedCrossedProduct (α : CStarAlgebraAction Γ B) := ↥(reducedCrossedAlgebra α)

theorem reducedCrossedAlgebra_isClosed (α : CStarAlgebraAction Γ B) :
    IsClosed (reducedCrossedAlgebra α :
      Set (AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ))) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

instance reducedCrossedProduct_nonUnitalCStarAlgebra (α : CStarAlgebraAction Γ B) :
    NonUnitalCStarAlgebra (ReducedCrossedProduct α) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _
    (h_closed := reducedCrossedAlgebra_isClosed α)

theorem reducedCrossedGenerator_mem (α : CStarAlgebraAction Γ B) (b : B) (g : Γ) :
    reducedCrossedGenerator α b g ∈ reducedCrossedAlgebra α :=
  NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨(b, g), rfl⟩)

/-- Minimality among closed regular-operator star subalgebras. -/
theorem reducedCrossedAlgebra_minimal (α : CStarAlgebraAction Γ B)
    (S : NonUnitalStarSubalgebra ℂ
      (AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)))
    (hS : IsClosed (S :
      Set (AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ))))
    (h : ∀ b g, reducedCrossedGenerator α b g ∈ S) : reducedCrossedAlgebra α ≤ S := by
  apply NonUnitalStarSubalgebra.topologicalClosure_minimal _ _ hS
  apply NonUnitalStarAlgebra.adjoin_le
  rintro _ ⟨⟨b, g⟩, rfl⟩
  exact h b g

/-- The coefficient algebra embeds into the concrete reduced crossed product. -/
def coefficientToReducedCrossed (α : CStarAlgebraAction Γ B) :
    B →⋆ₙₐ[ℂ] ReducedCrossedProduct α :=
  NonUnitalStarAlgHom.codRestrict (reducedCrossedCoefficientHom α)
    (reducedCrossedAlgebra α) (fun b => by
    rw [show reducedCrossedCoefficientHom α b = reducedCrossedCoefficient α b from rfl]
    have h := reducedCrossedGenerator_mem α b (1 : Γ)
    simpa only [reducedCrossedGenerator, reducedCrossedRegular_one, mul_one] using h)

@[simp] theorem coefficientToReducedCrossed_coe (α : CStarAlgebraAction Γ B) (b : B) :
    (coefficientToReducedCrossed α b :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) =
      reducedCrossedCoefficient α b := rfl

@[simp] theorem norm_coefficientToReducedCrossed (α : CStarAlgebraAction Γ B) (b : B) :
    ‖coefficientToReducedCrossed α b‖ = ‖b‖ := norm_reducedCrossedCoefficient α b

theorem coefficientToReducedCrossed_injective (α : CStarAlgebraAction Γ B) :
    Function.Injective (coefficientToReducedCrossed α) := by
  intro a b h
  exact reducedCrossedCoefficient_injective α (congrArg Subtype.val h)

end BC4lean.KKTheory
