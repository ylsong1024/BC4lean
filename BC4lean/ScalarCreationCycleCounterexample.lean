import BC4lean.ScalarCreationModule
import BC4lean.KasparovDirectSum

/-! # A creation-map compactness counterexample with complete cycle hypotheses

For the trivial group and scalar algebras, the first cycle is the all-even
scalar module with scalar representation and operator zero. The second is
the genuine Hilbert-module sum ℓ²(ℕ) ⊕ ℓ²(ℕ), graded by `diag(1,-1)`, with
scalar representation and the selfadjoint odd flip. All four defects of the
second cycle vanish. Both modules are complete and countably generated.

The second module also has its compatible ordinary Hilbert inner product;
this uses its existing sum norm. The actual scalar tensor creation map at 1
is adjointable and is not module compact. Thus the compactness assertion
fails even when both input objects satisfy all Kasparov-cycle hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BC4lean.KKTheory

open scoped InnerProductSpace TensorProduct ComplexOrder ScalarHilbertModule

namespace ScalarCreationCycleCounterexample

/-- A separable complex Hilbert space is countably generated as a right
scalar module; the coefficient 1 recovers every member of a dense sequence. -/
theorem countablyGenerated_of_separable (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] :
    IsCountablyGeneratedModule ℂ H := by
  obtain ⟨ξ, hξ⟩ := TopologicalSpace.exists_dense_seq H
  refine ⟨ξ, hξ.mono ?_⟩
  rintro x ⟨n, rfl⟩
  apply Submodule.subset_span
  exact ⟨n, MulOpposite.op 1, by simp⟩

/-- The concrete infinite-dimensional Hilbert space in the example. -/
abbrev H := BC4lean.L2Group ℕ

/-- Separability follows from the dense span of the countable delta family. -/
theorem hilbertSpace_separable : TopologicalSpace.SeparableSpace H := by
  have hs : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range (BC4lean.L2Group.delta : ℕ → H)) : Set H) :=
    (Set.countable_range (BC4lean.L2Group.delta : ℕ → H)).isSeparable.span
  have hd : Dense
      (Submodule.span ℂ (Set.range (BC4lean.L2Group.delta : ℕ → H)) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr BC4lean.L2Group.delta_dense_span
  exact hd.isSeparable_iff.mp hs

theorem hilbertSpace_countablyGenerated : IsCountablyGeneratedModule ℂ H := by
  let : TopologicalSpace.SeparableSpace H := hilbertSpace_separable
  exact countablyGenerated_of_separable H

/-- The genuine Hilbert-module sum, with its coefficient-induced sum norm. -/
abbrev Pair := HilbertModuleSum ℂ H H

/-- The ordinary complex Hilbert inner product on the scalar sum agrees
with its existing Hilbert-module norm. -/
scoped instance instPairInnerProductSpace : InnerProductSpace ℂ Pair where
  __ := (inferInstance : NormedSpace ℂ Pair)
  inner x y := ⟪x.fst, y.fst⟫_ℂ + ⟪x.snd, y.snd⟫_ℂ
  norm_sq_eq_re_inner x := by
    rw [CStarModule.norm_sq_eq ℂᵐᵒᵖ]
    change ‖MulOpposite.op (⟪x.fst, x.fst⟫_ℂ + ⟪x.snd, x.snd⟫_ℂ)‖ =
      Complex.re (⟪x.fst, x.fst⟫_ℂ + ⟪x.snd, x.snd⟫_ℂ)
    rw [MulOpposite.norm_op]
    have hp (v : H) : (0 : ℂ) ≤ ⟪v, v⟫_ℂ := by
      rw [← inner_self_ofReal_re, RCLike.ofReal_nonneg]
      exact inner_self_nonneg
    have hn := RCLike.norm_of_nonneg' (add_nonneg (hp x.fst) (hp x.snd))
    have hRe := congrArg (RCLike.re : ℂ → ℝ) hn
    simp only [RCLike.ofReal_re] at hRe
    rw [RCLike.re_eq_complex_re] at hRe
    exact hRe
  conj_inner_symm x y := by
    simp only [map_add, inner_conj_symm]
  add_left x y z := by
    change ⟪x.fst + y.fst, z.fst⟫_ℂ + ⟪x.snd + y.snd, z.snd⟫_ℂ =
      (⟪x.fst, z.fst⟫_ℂ + ⟪x.snd, z.snd⟫_ℂ) +
        (⟪y.fst, z.fst⟫_ℂ + ⟪y.snd, z.snd⟫_ℂ)
    simp only [inner_add_left]
    abel
  smul_left x y a := by
    change ⟪a • x.fst, y.fst⟫_ℂ + ⟪a • x.snd, y.snd⟫_ℂ =
      (starRingEnd ℂ) a * (⟪x.fst, y.fst⟫_ℂ + ⟪x.snd, y.snd⟫_ℂ)
    simp only [inner_smul_left, mul_add]

open scoped ScalarCreationCycleCounterexample

theorem pair_countablyGenerated : IsCountablyGeneratedModule ℂ Pair :=
  hilbertSpace_countablyGenerated.sum hilbertSpace_countablyGenerated

/-- Scalar multiplication gives the actual nonunital star representation. -/
def scalarRepresentation (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M]
    [SMul ℂᵐᵒᵖ M] [CStarModule ℂᵐᵒᵖ M] :
    ℂ →⋆ₙₐ[ℂ] AdjointableMap ℂ M M :=
  (StarAlgHom.ofId ℂ (AdjointableMap ℂ M M)).toNonUnitalStarAlgHom

@[simp] theorem scalarRepresentation_apply (M : Type*) [NormedAddCommGroup M]
    [NormedSpace ℂ M] [SMul ℂᵐᵒᵖ M] [CStarModule ℂᵐᵒᵖ M] (a : ℂ) (x : M) :
    scalarRepresentation M a x = a • x := by
  change (algebraMap ℂ (AdjointableMap ℂ M M) a) x = a • x
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-- The actual trivial algebra action, specialized to the trivial group. -/
abbrev scalarAction : CStarAlgebraAction Unit ℂ := CStarAlgebraAction.trivial

theorem trivial_conjugate (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M]
    [SMul ℂᵐᵒᵖ M] [CStarModule ℂᵐᵒᵖ M] (g : Unit)
    (T : AdjointableMap ℂ M M) :
    (EquivariantHilbertModule.trivial (Γ := Unit)).conjugateOperator g T = T := by
  ext x
  rfl

theorem scalarRepresentation_compact (a : ℂ) :
    IsModuleCompact (scalarRepresentation ℂ a) := by
  have h : scalarRepresentation ℂ a = moduleRankOne (B := ℂ) a 1 := by
    ext z
    simp only [scalarRepresentation_apply, moduleRankOne_apply,
      ScalarHilbertModule.inner_eq_op, ScalarHilbertModule.op_smul]
    simp [RCLike.inner_apply, smul_eq_mul, mul_comm]
  rw [h]
  exact moduleRankOne_mem_moduleCompact a 1

/-- The first full cycle: all-even ℂ, scalar representation, and F = 0. -/
def firstCycle : KasparovCycle scalarAction scalarAction ℂ where
  countablyGenerated := countablyGenerated_of_separable ℂ
  grading := GradedHilbertModule.trivial
  groupAction := EquivariantHilbertModule.trivial
  grading_preserved := fun _ _ => rfl
  representation := scalarRepresentation ℂ
  representation_even := fun _ _ => rfl
  representation_equivariant g a := trivial_conjugate ℂ g _
  operator := 0
  operator_odd := by intro x; simp
  selfadjoint_mod_compact := by
    intro a
    simpa using (IsModuleCompact.zero (B := ℂ) (E := ℂ) (F := ℂ))
  square_mod_compact := by
    intro a
    simpa using (scalarRepresentation_compact a).neg
  commutator_compact := by
    intro a
    simpa using (IsModuleCompact.zero (B := ℂ) (E := ℂ) (F := ℂ))
  equivariance_mod_compact := by
    intro g a
    rw [trivial_conjugate]
    simpa using (IsModuleCompact.zero (B := ℂ) (E := ℂ) (F := ℂ))

/-- The diagonal grading involution on the genuine sum. -/
def diagonalInvolution : AdjointableMap ℂ Pair Pair :=
  sumMap (1 : AdjointableMap ℂ H H) (-1 : AdjointableMap ℂ H H)

theorem diagonalInvolution_selfadjoint : diagonalInvolution.adjoint = diagonalInvolution := by
  change star diagonalInvolution = diagonalInvolution
  rw [diagonalInvolution, ← sumMap_star]
  simp only [star_one, star_neg]

theorem diagonalInvolution_square :
    diagonalInvolution.comp diagonalInvolution = AdjointableMap.id := by
  change diagonalInvolution * diagonalInvolution = 1
  rw [diagonalInvolution, ← sumMap_mul]
  simp

/-- The honest Z/2 grading `diag(1,-1)`. -/
def pairGrading : GradedHilbertModule (CStarGrading.trivial : CStarGrading ℂ) Pair :=
  GradedHilbertModule.ofSelfadjointInvolution diagonalInvolution
    diagonalInvolution_selfadjoint diagonalInvolution_square

@[simp] theorem pairGrading_apply (x : Pair) :
    pairGrading.grading x = sumMk x.fst (-x.snd) := by
  simp [pairGrading, diagonalInvolution, sumMap_apply]

/-- The bounded flip, with itself as the explicit module adjoint. -/
def flipOperator : AdjointableMap ℂ Pair Pair where
  toCLM := (sumSwap (B := ℂ) (E := H) (F := H)).toContinuousLinearEquiv.toContinuousLinearMap
  adjointCLM := (sumSwap (B := ℂ) (E := H) (F := H)).toContinuousLinearEquiv.toContinuousLinearMap
  adjoint_identity x y := by
    change ⟪x.snd, y.fst⟫_(ℂᵐᵒᵖ) + ⟪x.fst, y.snd⟫_(ℂᵐᵒᵖ) =
      ⟪x.fst, y.snd⟫_(ℂᵐᵒᵖ) + ⟪x.snd, y.fst⟫_(ℂᵐᵒᵖ)
    exact add_comm _ _

@[simp] theorem flipOperator_apply (x : Pair) :
    flipOperator x = sumMk x.snd x.fst := rfl

@[simp] theorem flipOperator_selfadjoint : star flipOperator = flipOperator := rfl

@[simp] theorem flipOperator_adjoint : flipOperator.adjoint = flipOperator := rfl

@[simp] theorem flipOperator_square : flipOperator * flipOperator = 1 := by
  ext x
  exact sumMk_eta x

theorem flipOperator_odd : pairGrading.IsOdd pairGrading flipOperator := by
  intro x
  simp only [pairGrading_apply, flipOperator_apply, sumMk_fst, sumMk_snd]
  apply Prod.ext <;> simp

theorem flipOperator_commutes (a : ℂ) :
    flipOperator * scalarRepresentation Pair a = scalarRepresentation Pair a * flipOperator := by
  ext x
  change flipOperator (a • x) = a • flipOperator x
  exact flipOperator.toCLM.map_smul a x

/-- The second full cycle: countably generated, genuine graded sum, scalar
representation, and the odd selfadjoint unitary flip. -/
def secondCycle : KasparovCycle scalarAction scalarAction Pair where
  countablyGenerated := pair_countablyGenerated
  grading := pairGrading
  groupAction := EquivariantHilbertModule.trivial
  grading_preserved := fun _ _ => rfl
  representation := scalarRepresentation Pair
  representation_even a x := by
    change pairGrading.grading (a • x) = a • pairGrading.grading x
    exact pairGrading.grading.map_smul a x
  representation_equivariant g a := trivial_conjugate Pair g _
  operator := flipOperator
  operator_odd := flipOperator_odd
  selfadjoint_mod_compact := by
    intro a
    simpa using (IsModuleCompact.zero (B := ℂ) (E := Pair) (F := Pair))
  square_mod_compact := by
    intro a
    simpa using (IsModuleCompact.zero (B := ℂ) (E := Pair) (F := Pair))
  commutator_compact := by
    intro a
    rw [flipOperator_commutes, sub_self]
    exact IsModuleCompact.zero
  equivariance_mod_compact := by
    intro g a
    rw [trivial_conjugate, sub_self, zero_mul]
    exact IsModuleCompact.zero

/-- Every one of the second cycle's four defects vanishes exactly. -/
theorem secondCycle_isDegenerate : secondCycle.IsDegenerate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a; simp [secondCycle]
  · intro a; simp [secondCycle]
  · intro a; simp [secondCycle, flipOperator_commutes]
  · intro g a; simp [secondCycle, trivial_conjugate]

/-- The scalar tensor creation map attached to the second full cycle. -/
def creationAtOne : AdjointableMap ℂ Pair (ℂ ⊗[ℂ] Pair) :=
  scalarCreationModuleMap 1

@[simp] theorem creationAtOne_apply (x : Pair) : creationAtOne x = 1 ⊗ₜ[ℂ] x := rfl

/-- The actual tensor creation map at 1 fails module compactness despite
all the complete, countably generated, graded cycle hypotheses above. -/
theorem creationAtOne_not_moduleCompact : ¬ IsModuleCompact creationAtOne := by
  intro h
  have hC := ScalarHilbertModule.isCompactOperator_of_isModuleCompact h
  have hI : IsCompactOperator (ContinuousLinearMap.id ℂ Pair) := by
    have hL : IsCompactOperator
        ((TensorProduct.lidIsometry ℂ Pair).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (scalarCreationMap (H := Pair) 1)) :=
      hC.clm_comp (TensorProduct.lidIsometry ℂ Pair).toContinuousLinearEquiv.toContinuousLinearMap
    simpa only [
      scalarCreationMap_lid_comp, one_smul] using hL
  have hH := (hI.comp_clm (sumInl (B := ℂ) (E := H) (F := H)).toCLM).clm_comp
    (sumFst (B := ℂ) (E := H) (F := H)).toCLM
  exact l2Nat_identity_not_compact hH

/-- Both full cycles and the noncompact creation map occur in one concrete
scalar example; the second cycle even has exactly vanishing defects. -/
theorem fullCycleCounterexample :
    ∃ (c : KasparovCycle scalarAction scalarAction ℂ)
      (d : KasparovCycle scalarAction scalarAction Pair),
      c.operator = 0 ∧ c.representation = scalarRepresentation ℂ ∧
      d.representation = scalarRepresentation Pair ∧ d.IsDegenerate ∧
      ¬ IsModuleCompact creationAtOne :=
  ⟨firstCycle, secondCycle, rfl, rfl, rfl,
    secondCycle_isDegenerate, creationAtOne_not_moduleCompact⟩

end ScalarCreationCycleCounterexample
end BC4lean.KKTheory
