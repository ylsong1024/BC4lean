import BC4lean.HilbertModuleSum
import BC4lean.KasparovCycle

/-! # Direct sums of equivariant Kasparov cycles

The direct sum uses the coefficient-valued Hilbert-module norm. Gradings,
compatible coefficient-twisted actions, representations, and Fredholm operators
are combined diagonally. The compact defect conditions are proved from the
summand defects through the actual adjointable coordinate maps.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ A B E F G H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- Two compatible coefficient-twisted isometries induce an isometry of Hilbert sums. -/
def sumLinearIsometryEquiv (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] H)
    (σ : Bᵐᵒᵖ ≃⋆ₐ[ℂ] Bᵐᵒᵖ)
    (he : ∀ x y, ⟪e x, e y⟫_(Bᵐᵒᵖ) = σ ⟪x, y⟫_(Bᵐᵒᵖ))
    (hf : ∀ x y, ⟪f x, f y⟫_(Bᵐᵒᵖ) = σ ⟪x, y⟫_(Bᵐᵒᵖ)) :
    HilbertModuleSum B E F ≃ₗᵢ[ℂ] HilbertModuleSum B G H where
  toLinearEquiv := (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (E × F)).trans
    ((e.toLinearEquiv.prodCongr f.toLinearEquiv).trans
      (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (G × H)).symm)
  norm_map' x := by
    change Real.sqrt ‖⟪e x.fst, e x.fst⟫_(Bᵐᵒᵖ) + ⟪f x.snd, f x.snd⟫_(Bᵐᵒᵖ)‖ =
      Real.sqrt ‖⟪x.fst, x.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd, x.snd⟫_(Bᵐᵒᵖ)‖
    rw [he, hf, ← map_add, StarAlgEquiv.norm_map]

@[simp] theorem sumLinearIsometryEquiv_apply (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] H)
    (σ : Bᵐᵒᵖ ≃⋆ₐ[ℂ] Bᵐᵒᵖ)
    (he : ∀ x y, ⟪e x, e y⟫_(Bᵐᵒᵖ) = σ ⟪x, y⟫_(Bᵐᵒᵖ))
    (hf : ∀ x y, ⟪f x, f y⟫_(Bᵐᵒᵖ) = σ ⟪x, y⟫_(Bᵐᵒᵖ))
    (x : HilbertModuleSum B E F) :
    sumLinearIsometryEquiv e f σ he hf x = sumMk (e x.fst) (f x.snd) := rfl

namespace GradedHilbertModule

variable {δ : CStarGrading B}

/-- The direct-sum grading, also for nontrivially graded coefficients. -/
def sum (γE : GradedHilbertModule δ E) (γF : GradedHilbertModule δ F) :
    GradedHilbertModule δ (HilbertModuleSum B E F) where
  grading := sumLinearIsometryEquiv γE.grading γF.grading (opStarAlgEquiv δ.automorphism)
    γE.inner_grading γF.inner_grading
  involutive x := by
    apply Prod.ext <;> simp
  inner_grading x y := by
    simp only [inner_sum, sumLinearIsometryEquiv_apply, sumMk_fst, sumMk_snd,
      γE.inner_grading, γF.inner_grading, map_add]

@[simp] theorem sum_grading_apply (γE : GradedHilbertModule δ E) (γF : GradedHilbertModule δ F)
    (x : HilbertModuleSum B E F) :
    (γE.sum γF).grading x = sumMk (γE.grading x.fst) (γF.grading x.snd) := rfl

theorem IsEven.sumMap {γE : GradedHilbertModule δ E} {γF : GradedHilbertModule δ F}
    {γG : GradedHilbertModule δ G} {γH : GradedHilbertModule δ H}
    {S : AdjointableMap B E G} {T : AdjointableMap B F H}
    (hS : IsEven γE γG S) (hT : IsEven γF γH T) :
    IsEven (γE.sum γF) (γG.sum γH) (sumMap S T) := by
  intro x
  simp only [sum_grading_apply, sumMap_apply, sumMk_fst, sumMk_snd]
  exact Prod.ext (hS x.fst) (hT x.snd)

theorem IsOdd.sumMap {γE : GradedHilbertModule δ E} {γF : GradedHilbertModule δ F}
    {γG : GradedHilbertModule δ G} {γH : GradedHilbertModule δ H}
    {S : AdjointableMap B E G} {T : AdjointableMap B F H}
    (hS : IsOdd γE γG S) (hT : IsOdd γF γH T) :
    IsOdd (γE.sum γF) (γG.sum γH) (sumMap S T) := by
  intro x
  simp only [sum_grading_apply, sumMap_apply, sumMk_fst, sumMk_snd]
  exact Prod.ext (hS x.fst) (hT x.snd)

end GradedHilbertModule

variable [Group Γ]

namespace EquivariantHilbertModule

variable {β : CStarAlgebraAction Γ B}

/-- Compatible group actions combine on the genuine Hilbert-module direct sum. -/
def sum (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F) :
    EquivariantHilbertModule β (HilbertModuleSum B E F) where
  action :=
    { toFun := fun g => sumLinearIsometryEquiv (U.action g) (V.action g)
        (opStarAlgEquiv (β.automorphism g)) (U.inner_action g) (V.inner_action g)
      map_one' := by
        ext x
        apply Prod.ext <;> simp
      map_mul' := by
        intro g h
        ext x
        apply Prod.ext <;> simp }
  inner_action g x y := by
    change ⟪U.action g x.fst, U.action g y.fst⟫_(Bᵐᵒᵖ) +
      ⟪V.action g x.snd, V.action g y.snd⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv (β.automorphism g)
        (⟪x.fst, y.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd, y.snd⟫_(Bᵐᵒᵖ))
    rw [U.inner_action, V.inner_action, map_add]

@[simp] theorem sum_action_apply (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule β F) (g : Γ) (x : HilbertModuleSum B E F) :
    (U.sum V).action g x = sumMk (U.action g x.fst) (V.action g x.snd) := rfl

theorem PreservesGrading.sum {δ : CStarGrading B}
    {U : EquivariantHilbertModule β E} {V : EquivariantHilbertModule β F}
    {γE : GradedHilbertModule δ E} {γF : GradedHilbertModule δ F}
    (hU : U.PreservesGrading γE) (hV : V.PreservesGrading γF) :
    (U.sum V).PreservesGrading (γE.sum γF) := by
  intro g x
  simp only [sum_action_apply, GradedHilbertModule.sum_grading_apply, sumMk_fst, sumMk_snd]
  exact Prod.ext (hU g x.fst) (hV g x.snd)

@[simp] theorem sum_conjugateOperator (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule β F) (g : Γ)
    (S : AdjointableMap B E E) (T : AdjointableMap B F F) :
    (U.sum V).conjugateOperator g (sumMap S T) =
      sumMap (U.conjugateOperator g S) (V.conjugateOperator g T) := by
  ext x
  simp only [conjugateMap_apply, sum_action_apply, sumMap_apply, sumMk_fst, sumMk_snd]

end EquivariantHilbertModule

variable [NonUnitalCStarAlgebra A]

/-- The diagonal direct sum of two nonunital star representations. -/
def sumRepresentation (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (ψ : A →⋆ₙₐ[ℂ] AdjointableMap B F F) :
    A →⋆ₙₐ[ℂ] AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) where
  toFun a := sumMap (φ a) (ψ a)
  map_zero' := by simp
  map_add' a b := by simp only [map_add, sumMap_add]
  map_mul' a b := by simp only [map_mul, sumMap_mul]
  map_smul' c a := by simp only [map_smul, sumMap_smul, MonoidHom.id_apply]
  map_star' a := by simp only [map_star, sumMap_star]

@[simp] theorem sumRepresentation_apply (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (ψ : A →⋆ₙₐ[ℂ] AdjointableMap B F F) (a : A) :
    sumRepresentation φ ψ a = sumMap (φ a) (ψ a) := rfl

variable [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- The genuine direct sum of two even equivariant Kasparov cycles. -/
def directSum (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycle α β (HilbertModuleSum B E F) where
  countablyGenerated := c.countablyGenerated.sum d.countablyGenerated
  grading := c.grading.sum d.grading
  groupAction := c.groupAction.sum d.groupAction
  grading_preserved := c.grading_preserved.sum d.grading_preserved
  representation := sumRepresentation c.representation d.representation
  representation_even a := (c.representation_even a).sumMap (d.representation_even a)
  representation_equivariant g a := by
    change (c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap (c.representation a) (d.representation a)) =
        sumMap (c.representation (α.automorphism g a)) (d.representation (α.automorphism g a))
    rw [EquivariantHilbertModule.sum_conjugateOperator,
      c.representation_equivariant, d.representation_equivariant]
  operator := sumMap c.operator d.operator
  operator_odd := c.operator_odd.sumMap d.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((sumMap c.operator d.operator - star (sumMap c.operator d.operator)) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_mul]
    exact (c.selfadjoint_mod_compact a).sumMap (d.selfadjoint_mod_compact a)
  square_mod_compact a := by
    change IsModuleCompact ((sumMap c.operator d.operator * sumMap c.operator d.operator - 1) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_mul, ← (sumMap_one (B := B) (E := E) (F := F)), ← sumMap_sub, ← sumMap_mul]
    exact (c.square_mod_compact a).sumMap (d.square_mod_compact a)
  commutator_compact a := by
    change IsModuleCompact (sumMap c.operator d.operator * sumMap (c.representation a) (d.representation a) -
      sumMap (c.representation a) (d.representation a) * sumMap c.operator d.operator)
    rw [← sumMap_mul, ← sumMap_mul, ← sumMap_sub]
    exact (c.commutator_compact a).sumMap (d.commutator_compact a)
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap c.operator d.operator) - sumMap c.operator d.operator) *
        sumMap (c.representation a) (d.representation a))
    rw [EquivariantHilbertModule.sum_conjugateOperator, ← sumMap_sub, ← sumMap_mul]
    exact (c.equivariance_mod_compact g a).sumMap (d.equivariance_mod_compact g a)

@[simp] theorem directSum_operator (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    (c.directSum d).operator = sumMap c.operator d.operator := rfl

@[simp] theorem directSum_representation (c : KasparovCycle α β E) (d : KasparovCycle α β F) (a : A) :
    (c.directSum d).representation a = sumMap (c.representation a) (d.representation a) := rfl

/-- Direct sums preserve exact degeneracy, as required before taking a KK quotient. -/
theorem directSum_isDegenerate (c : KasparovCycle α β E) (d : KasparovCycle α β F)
    (hc : c.IsDegenerate) (hd : d.IsDegenerate) : (c.directSum d).IsDegenerate := by
  rcases hc with ⟨hc₁, hc₂, hc₃, hc₄⟩
  rcases hd with ⟨hd₁, hd₂, hd₃, hd₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (sumMap c.operator d.operator - star (sumMap c.operator d.operator)) *
      sumMap (c.representation a) (d.representation a) = 0
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_mul, hc₁, hd₁, sumMap_zero]
  · intro a
    change (sumMap c.operator d.operator * sumMap c.operator d.operator - 1) *
      sumMap (c.representation a) (d.representation a) = 0
    rw [← sumMap_mul, ← (sumMap_one (B := B) (E := E) (F := F)),
      ← sumMap_sub, ← sumMap_mul, hc₂, hd₂, sumMap_zero]
  · intro a
    change sumMap c.operator d.operator * sumMap (c.representation a) (d.representation a) -
      sumMap (c.representation a) (d.representation a) * sumMap c.operator d.operator = 0
    rw [← sumMap_mul, ← sumMap_mul, ← sumMap_sub, hc₃, hd₃, sumMap_zero]
  · intro g a
    change ((c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap c.operator d.operator) - sumMap c.operator d.operator) *
      sumMap (c.representation a) (d.representation a) = 0
    rw [EquivariantHilbertModule.sum_conjugateOperator, ← sumMap_sub, ← sumMap_mul,
      hc₄, hd₄, sumMap_zero]

end KasparovCycle

namespace OddKasparovCycle

/-- The genuine direct sum in the odd Fredholm-cycle picture. -/
def directSum (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) :
    OddKasparovCycle α β (HilbertModuleSum B E F) where
  countablyGenerated := c.countablyGenerated.sum d.countablyGenerated
  groupAction := c.groupAction.sum d.groupAction
  representation := sumRepresentation c.representation d.representation
  representation_equivariant g a := by
    change (c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap (c.representation a) (d.representation a)) =
        sumMap (c.representation (α.automorphism g a)) (d.representation (α.automorphism g a))
    rw [EquivariantHilbertModule.sum_conjugateOperator,
      c.representation_equivariant, d.representation_equivariant]
  operator := sumMap c.operator d.operator
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((sumMap c.operator d.operator - star (sumMap c.operator d.operator)) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_mul]
    exact (c.selfadjoint_mod_compact a).sumMap (d.selfadjoint_mod_compact a)
  square_mod_compact a := by
    change IsModuleCompact ((sumMap c.operator d.operator * sumMap c.operator d.operator - 1) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_mul, ← (sumMap_one (B := B) (E := E) (F := F)), ← sumMap_sub, ← sumMap_mul]
    exact (c.square_mod_compact a).sumMap (d.square_mod_compact a)
  commutator_compact a := by
    change IsModuleCompact (sumMap c.operator d.operator * sumMap (c.representation a) (d.representation a) -
      sumMap (c.representation a) (d.representation a) * sumMap c.operator d.operator)
    rw [← sumMap_mul, ← sumMap_mul, ← sumMap_sub]
    exact (c.commutator_compact a).sumMap (d.commutator_compact a)
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap c.operator d.operator) - sumMap c.operator d.operator) *
        sumMap (c.representation a) (d.representation a))
    rw [EquivariantHilbertModule.sum_conjugateOperator, ← sumMap_sub, ← sumMap_mul]
    exact (c.equivariance_mod_compact g a).sumMap (d.equivariance_mod_compact g a)

@[simp] theorem directSum_operator (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) :
    (c.directSum d).operator = sumMap c.operator d.operator := rfl

/-- Direct sums also preserve exact degeneracy in the odd Fredholm picture. -/
theorem directSum_isDegenerate (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F)
    (hc : c.IsDegenerate) (hd : d.IsDegenerate) : (c.directSum d).IsDegenerate := by
  rcases hc with ⟨hc₁, hc₂, hc₃, hc₄⟩
  rcases hd with ⟨hd₁, hd₂, hd₃, hd₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (sumMap c.operator d.operator - star (sumMap c.operator d.operator)) *
      sumMap (c.representation a) (d.representation a) = 0
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_mul, hc₁, hd₁, sumMap_zero]
  · intro a
    change (sumMap c.operator d.operator * sumMap c.operator d.operator - 1) *
      sumMap (c.representation a) (d.representation a) = 0
    rw [← sumMap_mul, ← (sumMap_one (B := B) (E := E) (F := F)),
      ← sumMap_sub, ← sumMap_mul, hc₂, hd₂, sumMap_zero]
  · intro a
    change sumMap c.operator d.operator * sumMap (c.representation a) (d.representation a) -
      sumMap (c.representation a) (d.representation a) * sumMap c.operator d.operator = 0
    rw [← sumMap_mul, ← sumMap_mul, ← sumMap_sub, hc₃, hd₃, sumMap_zero]
  · intro g a
    change ((c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap c.operator d.operator) - sumMap c.operator d.operator) *
      sumMap (c.representation a) (d.representation a) = 0
    rw [EquivariantHilbertModule.sum_conjugateOperator, ← sumMap_sub, ← sumMap_mul,
      hc₄, hd₄, sumMap_zero]

end OddKasparovCycle
end BC4lean.KKTheory
