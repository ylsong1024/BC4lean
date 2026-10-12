import BC4lean.CliffordPairModule
import BC4lean.GradedKasparovCycleIso
import Mathlib.Tactic.NoncommRing

/-! # Genuine odd cycles and Clifford-graded product-coefficient cycles

An odd cycle expands on the actual product-coefficient pair module, with
grading swap and Fredholm operator `(F,-F)`. Conversely the first actual
coordinate range gives an odd cycle. The grading exchanges ranges with the
required minus sign. These constructions concern cycle data; quotient-level
parity additionally requires their compatibility with arbitrary interval
homotopies, rather than just fixed-module operator paths.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ A B H E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H]
  [CStarModule Bᵐᵒᵖ H] [CompleteSpace H]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

omit [StarOrderedRing B] [CompleteSpace H] in
private theorem clifford_conjugate_neg (U : EquivariantHilbertModule β H)
    (g : Γ) (T : AdjointableMap B H H) :
    U.conjugateOperator g (-T) = -U.conjugateOperator g T := by
  ext x
  simp only [EquivariantHilbertModule.conjugateMap_apply, AdjointableMap.coe_neg_apply, map_neg]

/-- The actual Clifford expansion of an odd cycle. The first coordinate
is the +1 spectral range of ε = (1,-1), which fixes the parity convention. -/
def OddKasparovCycle.cliffordExpansion (c : OddKasparovCycle α β H) :
    GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading (CliffordPairModule B H) where
  sourceAction_preservesGrading := α.preservesGrading_trivial
  coefficientAction_preservesGrading := cliffordCoefficientAction_preservesGrading β
  countablyGenerated := c.countablyGenerated.cliffordPair
  grading := cliffordPairGrading
  groupAction := cliffordPairAction c.groupAction
  grading_preserved := cliffordPairAction_preservesGrading c.groupAction
  representation := cliffordPairDiagonalHom.toNonUnitalStarAlgHom.comp c.representation
  representation_graded a x := by
    rfl
  representation_equivariant g a := by
    change (cliffordPairAction c.groupAction).conjugateOperator g
      (cliffordPairMap (c.representation a) (c.representation a)) = _
    rw [cliffordPairAction_conjugate, c.representation_equivariant]
    rfl
  operator := cliffordPairMap c.operator (-c.operator)
  operator_odd x := by
    have hg (u : CliffordPairModule B H) : cliffordPairGrading.grading u =
        cliffordPairMk (B := B) u.2 u.1 := rfl
    rw [hg, hg]
    simp only [cliffordPairMap_apply, AdjointableMap.coe_neg_apply]
    change ((-c.operator x.2, c.operator x.1) : H × H) =
      (-c.operator x.2, -(-c.operator x.1))
    simp only [neg_neg]
  selfadjoint_mod_compact a := by
    change IsModuleCompact
      ((cliffordPairMap c.operator (-c.operator) - star (cliffordPairMap c.operator (-c.operator))) *
        cliffordPairMap (c.representation a) (c.representation a))
    rw [← cliffordPairMap_star, ← cliffordPairMap_sub, ← cliffordPairMap_mul]
    apply (c.selfadjoint_mod_compact a).cliffordPairMap
    convert (c.selfadjoint_mod_compact a).neg using 1
    simp only [star_neg]
    noncomm_ring
  square_mod_compact a := by
    change IsModuleCompact
      ((cliffordPairMap c.operator (-c.operator) * cliffordPairMap c.operator (-c.operator) - 1) *
        cliffordPairMap (c.representation a) (c.representation a))
    rw [← cliffordPairMap_mul, ← cliffordPairMap_one, ← cliffordPairMap_sub, ← cliffordPairMap_mul]
    apply (c.square_mod_compact a).cliffordPairMap
    simpa only [neg_mul_neg] using c.square_mod_compact a
  commutator_compact a := by
    change IsModuleCompact
      (cliffordPairMap c.operator (-c.operator) * cliffordPairMap (c.representation a) (c.representation a) -
        cliffordPairMap (c.representation a) (c.representation a) * cliffordPairMap c.operator (-c.operator))
    rw [← cliffordPairMap_mul, ← cliffordPairMap_mul, ← cliffordPairMap_sub]
    apply (c.commutator_compact a).cliffordPairMap
    convert (c.commutator_compact a).neg using 1
    noncomm_ring
  equivariance_mod_compact g a := by
    change IsModuleCompact
      (((cliffordPairAction c.groupAction).conjugateOperator g
          (cliffordPairMap c.operator (-c.operator)) - cliffordPairMap c.operator (-c.operator)) *
        cliffordPairMap (c.representation a) (c.representation a))
    rw [cliffordPairAction_conjugate, ← cliffordPairMap_sub, ← cliffordPairMap_mul, clifford_conjugate_neg]
    apply (c.equivariance_mod_compact g a).cliffordPairMap
    convert (c.equivariance_mod_compact g a).neg using 1
    noncomm_ring

section Reconstruction

variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (B × B)ᵐᵒᵖ E]
  [CStarModule (B × B)ᵐᵒᵖ E] [CompleteSpace E]

private theorem coordinateModuleProjection_complement_range (k : Bool)
    (x : CliffordCoefficientRange B E k) : coordinateModuleProjection (B := B) (!k) (x : E) = 0 := by
  have h := coordinateAdjointableProjection_mul_complement (B := B) (E := E) (!k)
  simp only [Bool.not_not] at h
  have hx := congrArg (fun T : AdjointableMap (B × B) E E => T (x : E)) h
  simpa only [AdjointableMap.mul_apply, coordinateAdjointableProjection_apply,
    cliffordCoefficientRange_projection, AdjointableMap.coe_zero_apply] using hx

/-- Every genuinely Clifford-graded module is reconstructed from the actual
first range. The inverse sends `(u,v)` to `u + J v`. -/
def cliffordModuleReconstruction
    (γ : GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (B × B)) E) :
    HilbertModuleEquiv (B × B) E
      (CliffordPairModule B (CliffordCoefficientRange B E true)) := by
  let L : E →ₗ[ℂ] CliffordPairModule B (CliffordCoefficientRange B E true) :=
    { toFun x := cliffordPairMk (cliffordCoefficientRangeProject true x)
        (cliffordRangeGradingEquiv γ false (cliffordCoefficientRangeProject false x))
      map_add' x y := by
        apply Prod.ext <;> apply Subtype.ext
        · exact coordinateModuleProjection_add true x y
        · change γ.grading (coordinateModuleProjection (B := B) false (x + y)) =
            γ.grading (coordinateModuleProjection (B := B) false x) +
              γ.grading (coordinateModuleProjection (B := B) false y)
          rw [coordinateModuleProjection_add, map_add]
      map_smul' c x := by
        apply Prod.ext <;> apply Subtype.ext
        · exact coordinateModuleProjection_smul_complex true c x
        · change γ.grading (coordinateModuleProjection (B := B) false (c • x)) =
            c • γ.grading (coordinateModuleProjection (B := B) false x)
          rw [coordinateModuleProjection_smul_complex, map_smul] }
  have hinner (x y : E) : ⟪L x, L y⟫_((B × B)ᵐᵒᵖ) = ⟪x, y⟫_((B × B)ᵐᵒᵖ) := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · change (MulOpposite.unop ⟪coordinateModuleProjection true x,
        coordinateModuleProjection true y⟫_((B × B)ᵐᵒᵖ)).1 = _
      rw [coordinateModuleProjection_inner_left, coordinateModuleProjection_inner_right,
        coordinateCoefficient_idempotent]
      rfl
    · change (MulOpposite.unop ⟪γ.grading (coordinateModuleProjection false x),
        γ.grading (coordinateModuleProjection false y)⟫_((B × B)ᵐᵒᵖ)).1 = _
      rw [γ.inner_grading, coordinateModuleProjection_inner_left,
        coordinateModuleProjection_inner_right, coordinateCoefficient_idempotent]
      rfl
  refine
    { linearIsometryEquiv :=
        { toFun := L
          invFun x := (x.1 : E) + γ.grading (x.2 : E)
          map_add' := L.map_add
          map_smul' := L.map_smul
          left_inv := ?_
          right_inv := ?_
          norm_map' := ?_ }
      inner_map := hinner }
  · intro x
    change coordinateModuleProjection true x +
      γ.grading (γ.grading (coordinateModuleProjection false x)) = x
    rw [γ.grading_sq]
    have htf : (!true : Bool) = false := rfl
    simpa only [AdjointableMap.coe_add_apply, coordinateAdjointableProjection_apply,
      AdjointableMap.one_apply, htf] using congrArg (fun T : AdjointableMap (B × B) E E => T x)
      (coordinateAdjointableProjection_add_complement (B := B) (E := E) true)
  · rintro ⟨u, v⟩
    have htf : (!true : Bool) = false := rfl
    have hft : (!false : Bool) = true := rfl
    have h0u : coordinateModuleProjection (B := B) false (u : E) = 0 := by
      simpa only [htf] using coordinateModuleProjection_complement_range true u
    have h0v : coordinateModuleProjection (B := B) false (v : E) = 0 := by
      simpa only [htf] using coordinateModuleProjection_complement_range true v
    have hJ : coordinateModuleProjection (B := B) true (γ.grading (v : E)) = 0 := by
      have h := coordinateModuleProjection_grading γ false (v : E)
      rw [hft, h0v, map_zero] at h
      exact h.symm
    have hP : coordinateModuleProjection (B := B) false (γ.grading (v : E)) = γ.grading (v : E) := by
      simpa only [htf, cliffordCoefficientRange_projection] using
        (coordinateModuleProjection_grading γ true (v : E)).symm
    apply Prod.ext <;> apply Subtype.ext
    · change coordinateModuleProjection (B := B) true ((u : E) + γ.grading (v : E)) = (u : E)
      rw [coordinateModuleProjection_add, cliffordCoefficientRange_projection, hJ, add_zero]
    · change γ.grading (coordinateModuleProjection (B := B) false
        ((u : E) + γ.grading (v : E))) = (v : E)
      rw [coordinateModuleProjection_add, h0u, hP, zero_add, γ.grading_sq]
  · intro x
    change ‖L x‖ = ‖x‖
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := (B × B)ᵐᵒᵖ), hinner,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := (B × B)ᵐᵒᵖ)]

end Reconstruction
end BC4lean.KKTheory
