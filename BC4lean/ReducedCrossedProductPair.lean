import BC4lean.ReducedCrossedProductMap
import BC4lean.ReducedCrossedProductGrading
import BC4lean.CliffordCoefficientGrading
import BC4lean.ReducedCrossedLeftRegular

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual reduced crossed products of the Clifford coordinate algebra

For the diagonal action on `B × B`, the two coefficient projections and the
two coefficient inclusions are actual equivariant nonunital star homomorphisms.
Their completed reduced maps give the coordinate maps below. The two included
images multiply to zero: this is proved for finite convolution sums from their
actual coordinate coefficients, then extended to the concrete completions by
density. Consequently the sum of the two inclusions is a star homomorphism.

The inverse equations are proved on finite regular generators and extended
using the actual dense-generator extensionality theorem. They produce the
actual crossed-product star equivalence; no norm estimate, inverse map,
nondegeneracy, or factorization statement is an input hypothesis. The final
grading theorem identifies the actual induced crossed-product grading with
the coordinate-swap grading on the product of the two reduced algebras.


-/

noncomputable section
namespace BC4lean.KKTheory.ReducedCrossedProductPair

open scoped CStarAlgebra Topology

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
private theorem inl_equivariant (β : CStarAlgebraAction Γ B) :
    ∀ g b, NonUnitalStarAlgHom.inl ℂ B B (β.automorphism g b) =
      (cliffordCoefficientAction β).automorphism g
        (NonUnitalStarAlgHom.inl ℂ B B b) := by
  intro g b
  change (β.automorphism g b, 0) =
    (β.automorphism g b, β.automorphism g 0)
  rw [map_zero]

omit [PartialOrder B] [StarOrderedRing B] in
private theorem inr_equivariant (β : CStarAlgebraAction Γ B) :
    ∀ g b, NonUnitalStarAlgHom.inr ℂ B B (β.automorphism g b) =
      (cliffordCoefficientAction β).automorphism g
        (NonUnitalStarAlgHom.inr ℂ B B b) := by
  intro g b
  change (0, β.automorphism g b) =
    (β.automorphism g 0, β.automorphism g b)
  rw [map_zero]

/-- First actual reduced coordinate map. -/
def fst (β : CStarAlgebraAction Γ B) :
    ReducedCrossedProduct (cliffordCoefficientAction β) →⋆ₙₐ[ℂ]
      ReducedCrossedProduct β :=
  reducedCrossedMap (cliffordCoefficientAction β) β
    (NonUnitalStarAlgHom.fst ℂ B B) (fun _ _ => rfl)

/-- Second actual reduced coordinate map. -/
def snd (β : CStarAlgebraAction Γ B) :
    ReducedCrossedProduct (cliffordCoefficientAction β) →⋆ₙₐ[ℂ]
      ReducedCrossedProduct β :=
  reducedCrossedMap (cliffordCoefficientAction β) β
    (NonUnitalStarAlgHom.snd ℂ B B) (fun _ _ => rfl)

/-- Actual reduced inclusion into the first coefficient summand. -/
def inl (β : CStarAlgebraAction Γ B) :
    ReducedCrossedProduct β →⋆ₙₐ[ℂ]
      ReducedCrossedProduct (cliffordCoefficientAction β) :=
  reducedCrossedMap β (cliffordCoefficientAction β)
    (NonUnitalStarAlgHom.inl ℂ B B) (inl_equivariant β)

/-- Actual reduced inclusion into the second coefficient summand. -/
def inr (β : CStarAlgebraAction Γ B) :
    ReducedCrossedProduct β →⋆ₙₐ[ℂ]
      ReducedCrossedProduct (cliffordCoefficientAction β) :=
  reducedCrossedMap β (cliffordCoefficientAction β)
    (NonUnitalStarAlgHom.inr ℂ B B) (inr_equivariant β)

private def finiteInl (β : CStarAlgebraAction Γ B) :
    AlgebraicCrossedProduct β →⋆ₙₐ[ℂ]
      AlgebraicCrossedProduct (cliffordCoefficientAction β) :=
  AlgebraicCrossedProduct.map β (cliffordCoefficientAction β)
    (NonUnitalStarAlgHom.inl ℂ B B) (inl_equivariant β)

private def finiteInr (β : CStarAlgebraAction Γ B) :
    AlgebraicCrossedProduct β →⋆ₙₐ[ℂ]
      AlgebraicCrossedProduct (cliffordCoefficientAction β) :=
  AlgebraicCrossedProduct.map β (cliffordCoefficientAction β)
    (NonUnitalStarAlgHom.inr ℂ B B) (inr_equivariant β)

@[simp] theorem fst_generator (β : CStarAlgebraAction Γ B) (b : B × B) (g : Γ) :
    fst β ⟨reducedCrossedGenerator (cliffordCoefficientAction β) b g,
      reducedCrossedGenerator_mem (cliffordCoefficientAction β) b g⟩ =
      ⟨reducedCrossedGenerator β b.1 g, reducedCrossedGenerator_mem β b.1 g⟩ :=
  reducedCrossedMap_generator _ _ _ _ b g

@[simp] theorem snd_generator (β : CStarAlgebraAction Γ B) (b : B × B) (g : Γ) :
    snd β ⟨reducedCrossedGenerator (cliffordCoefficientAction β) b g,
      reducedCrossedGenerator_mem (cliffordCoefficientAction β) b g⟩ =
      ⟨reducedCrossedGenerator β b.2 g, reducedCrossedGenerator_mem β b.2 g⟩ :=
  reducedCrossedMap_generator _ _ _ _ b g

@[simp] theorem inl_generator (β : CStarAlgebraAction Γ B) (b : B) (g : Γ) :
    inl β ⟨reducedCrossedGenerator β b g, reducedCrossedGenerator_mem β b g⟩ =
      ⟨reducedCrossedGenerator (cliffordCoefficientAction β) (b, 0) g,
        reducedCrossedGenerator_mem (cliffordCoefficientAction β) (b, 0) g⟩ :=
  reducedCrossedMap_generator _ _ _ _ b g

@[simp] theorem inr_generator (β : CStarAlgebraAction Γ B) (b : B) (g : Γ) :
    inr β ⟨reducedCrossedGenerator β b g, reducedCrossedGenerator_mem β b g⟩ =
      ⟨reducedCrossedGenerator (cliffordCoefficientAction β) (0, b) g,
        reducedCrossedGenerator_mem (cliffordCoefficientAction β) (0, b) g⟩ :=
  reducedCrossedMap_generator _ _ _ _ b g

private theorem generator_zero {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (δ : CStarAlgebraAction Γ D) (g : Γ) :
    (⟨reducedCrossedGenerator δ 0 g, reducedCrossedGenerator_mem δ 0 g⟩ :
      ReducedCrossedProduct δ) = 0 := by
  apply Subtype.ext
  change reducedCrossedCoefficientHom δ 0 * reducedCrossedRegular g = 0
  rw [map_zero, zero_mul]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The two finite coordinate images have genuinely zero product. -/
theorem finiteInl_mul_finiteInr (β : CStarAlgebraAction Γ B)
    (f h : AlgebraicCrossedProduct β) :
    finiteInl β f * finiteInr β h = 0 := by
  induction f using AlgebraicCrossedProduct.induction_on β with
  | zero => simp
  | single g b =>
    induction h using AlgebraicCrossedProduct.induction_on β with
    | zero => simp
    | single k c =>
      change AlgebraicCrossedProduct.map β (cliffordCoefficientAction β)
          (NonUnitalStarAlgHom.inl ℂ B B) (inl_equivariant β)
          (AlgebraicCrossedProduct.single β g b) *
        AlgebraicCrossedProduct.map β (cliffordCoefficientAction β)
          (NonUnitalStarAlgHom.inr ℂ B B) (inr_equivariant β)
          (AlgebraicCrossedProduct.single β k c) = 0
      rw [AlgebraicCrossedProduct.map_single, AlgebraicCrossedProduct.map_single,
        AlgebraicCrossedProduct.single_mul_single]
      have hcoeff : NonUnitalStarAlgHom.inl ℂ B B b *
          (cliffordCoefficientAction β).automorphism g
            (NonUnitalStarAlgHom.inr ℂ B B c) = 0 := by
        change (b * β.automorphism g 0, 0 * β.automorphism g c) = (0, 0)
        simp only [map_zero, mul_zero, zero_mul]
      rw [hcoeff, AlgebraicCrossedProduct.single_zero]
    | add h₁ h₂ ih₁ ih₂ => simp only [map_add, mul_add, ih₁, ih₂, add_zero]
  | add f₁ f₂ ih₁ ih₂ => simp only [map_add, add_mul, ih₁, ih₂, add_zero]

/-- Dense finite convolution upgrades coordinate cross-orthogonality to all
elements of the actual completed reduced algebras. -/
theorem inl_mul_inr (β : CStarAlgebraAction Γ B)
    (x y : ReducedCrossedProduct β) : inl β x * inr β y = 0 := by
  apply (algebraicToReducedCrossed_denseRange β).induction_on₂
    (p := fun x y => inl β x * inr β y = 0)
    (isClosed_eq (((map_continuous (inl β)).comp continuous_fst).mul
      ((map_continuous (inr β)).comp continuous_snd)) continuous_const) ?_ x y
  intro f h
  change reducedCrossedMap β (cliffordCoefficientAction β)
      (NonUnitalStarAlgHom.inl ℂ B B) (inl_equivariant β)
      (algebraicToReducedCrossed β f) *
    reducedCrossedMap β (cliffordCoefficientAction β)
      (NonUnitalStarAlgHom.inr ℂ B B) (inr_equivariant β)
      (algebraicToReducedCrossed β h) = 0
  rw [reducedCrossedMap_algebraic, reducedCrossedMap_algebraic, ← map_mul]
  change algebraicToReducedCrossed (cliffordCoefficientAction β)
    (finiteInl β f * finiteInr β h) = 0
  rw [finiteInl_mul_finiteInr, map_zero]

/-- The reverse mixed product vanishes too, by the actual star operation. -/
theorem inr_mul_inl (β : CStarAlgebraAction Γ B)
    (x y : ReducedCrossedProduct β) : inr β x * inl β y = 0 := by
  have h := congrArg star (inl_mul_inr β (star y) (star x))
  simpa only [star_mul, ← map_star, star_star, star_zero] using h

/-- Both completed coordinate maps together. -/
def toPair (β : CStarAlgebraAction Γ B) :
    ReducedCrossedProduct (cliffordCoefficientAction β) →⋆ₙₐ[ℂ]
      (ReducedCrossedProduct β × ReducedCrossedProduct β) :=
  (fst β).prod (snd β)

@[simp] theorem toPair_apply (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct (cliffordCoefficientAction β)) :
    toPair β x = (fst β x, snd β x) := rfl

private theorem orthogonal_add_mul {R : Type*}
    [NonUnitalNonAssocSemiring R] (a b c d : R)
    (had : a * d = 0) (hbc : b * c = 0) :
    (a + b) * (c + d) = a * c + b * d := by
  calc
    _ = a * (c + d) + b * (c + d) := add_mul a b (c + d)
    _ = (a * c + a * d) + (b * c + b * d) :=
      congrArg₂ (fun x y : R => x + y)
        (mul_add a c d) (mul_add b c d)
    _ = (a * c + 0) + (0 + b * d) :=
      congrArg₂ (fun x y : R => x + y)
        (congrArg (fun t : R => a * c + t) had)
        (congrArg (fun t : R => t + b * d) hbc)
    _ = a * c + b * d :=
      congrArg₂ (fun x y : R => x + y)
        (add_zero (a * c)) (zero_add (b * d))

/-- The sum of the two actual orthogonal completed inclusions is a star
homomorphism, not merely a linear right inverse. -/
def fromPair (β : CStarAlgebraAction Γ B) :
    (ReducedCrossedProduct β × ReducedCrossedProduct β) →⋆ₙₐ[ℂ]
      ReducedCrossedProduct (cliffordCoefficientAction β) where
  toFun x := inl β x.1 + inr β x.2
  map_zero' := by simp
  map_add' x y := by
    change inl β (x.1 + y.1) + inr β (x.2 + y.2) = _
    simp only [map_add]
    abel
  map_mul' x y := by
    change inl β (x.1 * y.1) + inr β (x.2 * y.2) =
      (inl β x.1 + inr β x.2) * (inl β y.1 + inr β y.2)
    exact (congrArg₂
      (fun a b : ReducedCrossedProduct (cliffordCoefficientAction β) => a + b)
      (map_mul (inl β) x.1 y.1) (map_mul (inr β) x.2 y.2)).trans
        (orthogonal_add_mul
          (inl β x.1) (inr β x.2) (inl β y.1) (inr β y.2)
          (inl_mul_inr β x.1 y.2) (inr_mul_inl β x.2 y.1)).symm
  map_smul' z x := by
    change inl β (z • x.1) + inr β (z • x.2) =
      z • (inl β x.1 + inr β x.2)
    exact (congrArg₂
      (fun a b : ReducedCrossedProduct (cliffordCoefficientAction β) => a + b)
      (map_smul (inl β) z x.1) (map_smul (inr β) z x.2)).trans
        (smul_add z (inl β x.1) (inr β x.2)).symm
  map_star' x := by
    change inl β (star x.1) + inr β (star x.2) =
      star (inl β x.1 + inr β x.2)
    exact (congrArg₂
      (fun a b : ReducedCrossedProduct (cliffordCoefficientAction β) => a + b)
      (map_star (inl β) x.1) (map_star (inr β) x.2)).trans
        (star_add (inl β x.1) (inr β x.2)).symm

@[simp] theorem fromPair_apply (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct β × ReducedCrossedProduct β) :
    fromPair β x = inl β x.1 + inr β x.2 := rfl

@[simp] theorem fst_inl (β : CStarAlgebraAction Γ B) (x : ReducedCrossedProduct β) :
    fst β (inl β x) = x := by
  have h : (fst β).comp (inl β) = NonUnitalStarAlgHom.id ℂ (ReducedCrossedProduct β) := by
    apply reducedCrossedHom_ext β
    intro b g
    change fst β (inl β ⟨reducedCrossedGenerator β b g,
      reducedCrossedGenerator_mem β b g⟩) =
      ⟨reducedCrossedGenerator β b g, reducedCrossedGenerator_mem β b g⟩
    rw [inl_generator, fst_generator]
  exact congrArg (fun φ => φ x) h

@[simp] theorem snd_inr (β : CStarAlgebraAction Γ B) (x : ReducedCrossedProduct β) :
    snd β (inr β x) = x := by
  have h : (snd β).comp (inr β) = NonUnitalStarAlgHom.id ℂ (ReducedCrossedProduct β) := by
    apply reducedCrossedHom_ext β
    intro b g
    change snd β (inr β ⟨reducedCrossedGenerator β b g,
      reducedCrossedGenerator_mem β b g⟩) =
      ⟨reducedCrossedGenerator β b g, reducedCrossedGenerator_mem β b g⟩
    rw [inr_generator, snd_generator]
  exact congrArg (fun φ => φ x) h

@[simp] theorem fst_inr (β : CStarAlgebraAction Γ B) (x : ReducedCrossedProduct β) :
    fst β (inr β x) = 0 := by
  have h : (fst β).comp (inr β) = 0 := by
    apply reducedCrossedHom_ext β
    intro b g
    simp only [NonUnitalStarAlgHom.comp_apply, inr_generator, fst_generator,
      NonUnitalStarAlgHom.zero_apply, generator_zero]
  exact congrArg (fun φ => φ x) h

@[simp] theorem snd_inl (β : CStarAlgebraAction Γ B) (x : ReducedCrossedProduct β) :
    snd β (inl β x) = 0 := by
  have h : (snd β).comp (inl β) = 0 := by
    apply reducedCrossedHom_ext β
    intro b g
    simp only [NonUnitalStarAlgHom.comp_apply, inl_generator, snd_generator,
      NonUnitalStarAlgHom.zero_apply, generator_zero]
  exact congrArg (fun φ => φ x) h

@[simp] theorem toPair_fromPair (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct β × ReducedCrossedProduct β) :
    toPair β (fromPair β x) = x := by
  apply Prod.ext
  · change fst β (inl β x.1 + inr β x.2) = x.1
    rw [map_add, fst_inl, fst_inr, add_zero]
  · change snd β (inl β x.1 + inr β x.2) = x.2
    rw [map_add, snd_inl, snd_inr, zero_add]

@[simp] theorem fromPair_toPair (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct (cliffordCoefficientAction β)) :
    fromPair β (toPair β x) = x := by
  have h : (fromPair β).comp (toPair β) =
      NonUnitalStarAlgHom.id ℂ (ReducedCrossedProduct (cliffordCoefficientAction β)) := by
    apply reducedCrossedHom_ext (cliffordCoefficientAction β)
    intro b g
    change inl β (fst β ⟨reducedCrossedGenerator (cliffordCoefficientAction β) b g,
        reducedCrossedGenerator_mem (cliffordCoefficientAction β) b g⟩) +
      inr β (snd β ⟨reducedCrossedGenerator (cliffordCoefficientAction β) b g,
        reducedCrossedGenerator_mem (cliffordCoefficientAction β) b g⟩) = _
    rw [fst_generator, snd_generator, inl_generator, inr_generator]
    apply Subtype.ext
    change reducedCrossedCoefficientHom (cliffordCoefficientAction β) (b.1, 0) *
        reducedCrossedRegular g +
      reducedCrossedCoefficientHom (cliffordCoefficientAction β) (0, b.2) *
        reducedCrossedRegular g =
      reducedCrossedCoefficientHom (cliffordCoefficientAction β) b * reducedCrossedRegular g
    rw [← add_mul, ← map_add]
    exact congrArg
      (fun q : B × B => reducedCrossedCoefficientHom (cliffordCoefficientAction β) q *
        reducedCrossedRegular g)
      (Prod.ext (add_zero b.1) (zero_add b.2))
  exact congrArg (fun φ => φ x) h

/-- The actual product decomposition of the concrete reduced crossed algebra
for the Clifford coordinate coefficient algebra. -/
def equiv (β : CStarAlgebraAction Γ B) :
    ReducedCrossedProduct (cliffordCoefficientAction β) ≃⋆ₐ[ℂ]
      (ReducedCrossedProduct β × ReducedCrossedProduct β) where
  toFun := toPair β
  invFun := fromPair β
  left_inv := fromPair_toPair β
  right_inv := toPair_fromPair β
  map_add' := map_add (toPair β)
  map_mul' := map_mul (toPair β)
  map_star' := map_star (toPair β)
  map_smul' := map_smul (toPair β)

@[simp] theorem equiv_apply (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct (cliffordCoefficientAction β)) :
    equiv β x = (fst β x, snd β x) := rfl

@[simp] theorem equiv_symm_apply (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct β × ReducedCrossedProduct β) :
    (equiv β).symm x = inl β x.1 + inr β x.2 := rfl

@[simp] theorem equiv_generator (β : CStarAlgebraAction Γ B) (b : B × B) (g : Γ) :
    equiv β ⟨reducedCrossedGenerator (cliffordCoefficientAction β) b g,
      reducedCrossedGenerator_mem (cliffordCoefficientAction β) b g⟩ =
      (⟨reducedCrossedGenerator β b.1 g, reducedCrossedGenerator_mem β b.1 g⟩,
        ⟨reducedCrossedGenerator β b.2 g, reducedCrossedGenerator_mem β b.2 g⟩) := by
  simp only [equiv_apply, fst_generator, snd_generator]

/-- The coefficient inclusion is exactly coordinatewise under this equivalence. -/
@[simp] theorem equiv_coefficient (β : CStarAlgebraAction Γ B) (b : B × B) :
    equiv β (coefficientToReducedCrossed (cliffordCoefficientAction β) b) =
      (coefficientToReducedCrossed β b.1, coefficientToReducedCrossed β b.2) := by
  apply Prod.ext
  · exact reducedCrossedMap_coefficient (cliffordCoefficientAction β) β
      (NonUnitalStarAlgHom.fst ℂ B B) (fun _ _ => rfl) b
  · exact reducedCrossedMap_coefficient (cliffordCoefficientAction β) β
      (NonUnitalStarAlgHom.snd ℂ B B) (fun _ _ => rfl) b

/-- The inverse map recovers the original coefficient pair without a unit. -/
@[simp] theorem equiv_symm_coefficient (β : CStarAlgebraAction Γ B) (b : B × B) :
    (equiv β).symm
        (coefficientToReducedCrossed β b.1, coefficientToReducedCrossed β b.2) =
      coefficientToReducedCrossed (cliffordCoefficientAction β) b := by
  apply (equiv β).injective
  exact ((equiv β).apply_symm_apply _).trans (equiv_coefficient β b).symm

/-- The inverse map recovers every same-group finite coefficient pair. -/
@[simp] theorem equiv_symm_generator (β : CStarAlgebraAction Γ B) (b : B × B) (g : Γ) :
    (equiv β).symm
        (⟨reducedCrossedGenerator β b.1 g, reducedCrossedGenerator_mem β b.1 g⟩,
          ⟨reducedCrossedGenerator β b.2 g, reducedCrossedGenerator_mem β b.2 g⟩) =
      ⟨reducedCrossedGenerator (cliffordCoefficientAction β) b g,
        reducedCrossedGenerator_mem (cliffordCoefficientAction β) b g⟩ := by
  apply (equiv β).injective
  exact ((equiv β).apply_symm_apply _).trans (equiv_generator β b g).symm

/-- Each actual finite coefficient is sent to its two coordinate coefficients. -/
@[simp] theorem equiv_algebraic (β : CStarAlgebraAction Γ B)
    (f : AlgebraicCrossedProduct (cliffordCoefficientAction β)) :
    equiv β (algebraicToReducedCrossed (cliffordCoefficientAction β) f) =
      (algebraicToReducedCrossed β
          (AlgebraicCrossedProduct.map (cliffordCoefficientAction β) β
            (NonUnitalStarAlgHom.fst ℂ B B) (fun _ _ => rfl) f),
        algebraicToReducedCrossed β
          (AlgebraicCrossedProduct.map (cliffordCoefficientAction β) β
            (NonUnitalStarAlgHom.snd ℂ B B) (fun _ _ => rfl) f)) := by
  apply Prod.ext
  · exact reducedCrossedMap_algebraic (cliffordCoefficientAction β) β
      (NonUnitalStarAlgHom.fst ℂ B B) (fun _ _ => rfl) f
  · exact reducedCrossedMap_algebraic (cliffordCoefficientAction β) β
      (NonUnitalStarAlgHom.snd ℂ B B) (fun _ _ => rfl) f

/-- The completed algebra equivalence has the actual C⋆ norm on both sides. -/
theorem equiv_isometry (β : CStarAlgebraAction Γ B) : Isometry (equiv β) :=
  StarAlgEquiv.isometry (equiv β)

@[simp] theorem equiv_norm (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct (cliffordCoefficientAction β)) :
    ‖equiv β x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map (equiv β) (equiv β).injective x

/-- The Clifford swap grading commutes with the actual reduced product
decomposition. The left side is the grading constructed by regular Hilbert
module conjugation; the right side is the existing Clifford coordinate swap. -/
theorem equiv_grading (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct (cliffordCoefficientAction β)) :
    equiv β
        ((reducedCrossedProductGrading (cliffordCoefficientAction β)
          cliffordCoefficientGrading (cliffordCoefficientAction_preservesGrading β)).automorphism x) =
      (cliffordCoefficientGrading :
        CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism
        (equiv β x) := by
  let γ := reducedCrossedProductGrading (cliffordCoefficientAction β)
    cliffordCoefficientGrading (cliffordCoefficientAction_preservesGrading β)
  let δ : CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β) :=
    cliffordCoefficientGrading
  have h : (toPair β).comp γ.automorphism.toNonUnitalStarAlgHom =
      δ.automorphism.toNonUnitalStarAlgHom.comp (toPair β) := by
    apply reducedCrossedHom_ext (cliffordCoefficientAction β)
    intro b g
    have hγ : γ.automorphism
        ⟨reducedCrossedGenerator (cliffordCoefficientAction β) b g,
          reducedCrossedGenerator_mem (cliffordCoefficientAction β) b g⟩ =
        (⟨reducedCrossedGenerator (cliffordCoefficientAction β) (b.2, b.1) g,
          reducedCrossedGenerator_mem (cliffordCoefficientAction β) (b.2, b.1) g⟩ :
            ReducedCrossedProduct (cliffordCoefficientAction β)) := by
      apply Subtype.ext
      exact reducedCrossedProductGrading_generator (cliffordCoefficientAction β)
        cliffordCoefficientGrading (cliffordCoefficientAction_preservesGrading β) b g
    change toPair β (γ.automorphism _) = δ.automorphism (toPair β _)
    rw [hγ]
    change (fst β _, snd β _) = (snd β _, fst β _)
    rw [fst_generator, snd_generator, snd_generator, fst_generator]
  exact congrArg (fun φ => φ x) h

/-- The inverse equivalence also preserves the actual swap gradings. -/
theorem equiv_symm_grading (β : CStarAlgebraAction Γ B)
    (x : ReducedCrossedProduct β × ReducedCrossedProduct β) :
    (equiv β).symm
        ((cliffordCoefficientGrading :
          CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism x) =
      (reducedCrossedProductGrading (cliffordCoefficientAction β)
        cliffordCoefficientGrading (cliffordCoefficientAction_preservesGrading β)).automorphism
        ((equiv β).symm x) := by
  apply (equiv β).injective
  let δ : CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β) :=
    cliffordCoefficientGrading
  exact ((equiv β).apply_symm_apply (δ.automorphism x)).trans
    ((equiv_grading β ((equiv β).symm x)).trans
      (congrArg δ.automorphism ((equiv β).apply_symm_apply x))).symm

private theorem leftRegular_continuous {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (δ : CStarAlgebraAction Γ D) (g : Γ) :
    Continuous (KasparovDescent.leftRegular δ g) := by
  exact (continuous_const.mul continuous_subtype_val).subtype_mk _

private theorem leftRegular_zero {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (δ : CStarAlgebraAction Γ D) (g : Γ) :
    KasparovDescent.leftRegular δ g 0 = 0 := by
  apply Subtype.ext
  exact mul_zero _

private theorem leftRegular_add {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (δ : CStarAlgebraAction Γ D) (g : Γ)
    (c d : ReducedCrossedProduct δ) :
    KasparovDescent.leftRegular δ g (c + d) =
      KasparovDescent.leftRegular δ g c + KasparovDescent.leftRegular δ g d := by
  apply Subtype.ext
  exact mul_add _ _ _

private theorem leftRegular_generator {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (δ : CStarAlgebraAction Γ D)
    (g h : Γ) (d : D) :
    KasparovDescent.leftRegular δ g
        ⟨reducedCrossedGenerator δ d h, reducedCrossedGenerator_mem δ d h⟩ =
      ⟨reducedCrossedGenerator δ (δ.automorphism g d) (g * h),
        reducedCrossedGenerator_mem δ (δ.automorphism g d) (g * h)⟩ := by
  apply Subtype.ext
  exact KasparovDescent.regular_mul_generator δ g h d

/-- The actual nonunital left regular multiplier is coordinatewise under the
completed product equivalence. This is an equality of linear multipliers;
it does not assert that a regular unitary belongs to the crossed algebra. -/
theorem equiv_leftRegular (β : CStarAlgebraAction Γ B) (g : Γ)
    (c : ReducedCrossedProduct (cliffordCoefficientAction β)) :
    equiv β (KasparovDescent.leftRegular (cliffordCoefficientAction β) g c) =
      (KasparovDescent.leftRegular β g (equiv β c).1,
        KasparovDescent.leftRegular β g (equiv β c).2) := by
  have hcont := (equiv_isometry β).continuous
  refine (algebraicToReducedCrossed_denseRange (cliffordCoefficientAction β)).induction_on c
    (isClosed_eq (hcont.comp (leftRegular_continuous (cliffordCoefficientAction β) g))
      (((leftRegular_continuous β g).comp (continuous_fst.comp hcont)).prodMk
        ((leftRegular_continuous β g).comp (continuous_snd.comp hcont)))) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on (cliffordCoefficientAction β) with
  | zero =>
    simp only [map_zero, leftRegular_zero]
    change (0 : ReducedCrossedProduct β × ReducedCrossedProduct β) =
      (KasparovDescent.leftRegular β g 0, KasparovDescent.leftRegular β g 0)
    exact Prod.ext (leftRegular_zero β g).symm (leftRegular_zero β g).symm
  | single h b =>
    have hgen : algebraicToReducedCrossed (cliffordCoefficientAction β)
        (AlgebraicCrossedProduct.single (cliffordCoefficientAction β) h b) =
        (⟨reducedCrossedGenerator (cliffordCoefficientAction β) b h,
          reducedCrossedGenerator_mem (cliffordCoefficientAction β) b h⟩ :
            ReducedCrossedProduct (cliffordCoefficientAction β)) := by
      apply Subtype.ext
      exact algebraicToReducedCrossed_single (cliffordCoefficientAction β) h b
    rw [hgen, leftRegular_generator, equiv_generator, equiv_generator,
      leftRegular_generator, leftRegular_generator]
    rfl
  | add f h hf hh =>
    simpa only [map_add, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, leftRegular_add] using
      congrArg₂ (· + ·) hf hh

end BC4lean.KKTheory.ReducedCrossedProductPair
