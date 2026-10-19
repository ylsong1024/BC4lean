import BC4lean.KasparovDescentAlgebraicRepresentation
import BC4lean.KasparovDescentRegularEmbedding
import BC4lean.ReducedSourceRegularOperator
import BC4lean.ReducedCrossedRepresentationExtension

/-! # The actual reduced source representation for Kasparov descent



The genuine regular amplification embeds in the actual indexed E-module.
Original source equivariance proves the generator intertwining formula,
first on finite regular vectors and then by completion density. The finite
regular norm estimate therefore bounds the actual descended algebraic
operator. Faithful coefficient amplification detects its norm. Finally the
actual dense closure extension gives the completed reduced representation.

The original representation may be degenerate. No norm bridge,
factorization, surjectivity of the regular embedding, or completed source
representation is supplied as a hypothesis.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped InnerProductSpace KasparovDescent CStarAlgebra

variable {Γ A B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (α : CStarAlgebraAction Γ A) (U : EquivariantHilbertModule β E)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
  (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))

/-- The completed coefficient extension is determined by its actual elementary tensors. -/
private theorem descentModule_clm_ext {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    {S T : Module β E →L[ℂ] P}
    (h : ∀ (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ),
      S (mk β E x c) = T (mk β E x c)) : S = T := by
  apply ContinuousLinearMap.ext_on
    (interiorModuleTensor_span_dense
      (B := B) (C := ReducedCrossedProduct β) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (coefficientRepresentation β))
  rintro v ⟨⟨x, c⟩, rfl⟩
  exact h x c

/-- Continuous linear maps on the amplified module are determined by its actual elementary tensors. -/
private theorem regularAmplification_outer_clm_ext {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    {S T : InteriorModuleTensor
      (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
      (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) →L[ℂ] P}
    (h : ∀ (u : Module β E) (z : ReducedCrossedHilbertModule B Γ),
      S (interiorModuleTensorMk
        (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
        (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) u z) =
      T (interiorModuleTensorMk
        (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
        (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) u z)) :
    S = T := by
  apply ContinuousLinearMap.ext_on
    (interiorModuleTensor_span_dense
      (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
      (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β))
  rintro v ⟨⟨u, z⟩, rfl⟩
  exact h u z

/-- Fixing the completed regular vector gives an actual bounded linear elementary-tensor map. -/
private def regularAmplification_leftPureCLM (z : ReducedCrossedHilbertModule B Γ) :
    Module β E →L[ℂ] InteriorModuleTensor
      (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
      (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) :=
  ((interiorModuleTensorMk
    (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
    (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)).flip z).mkContinuous
      ‖z‖ (fun u => by
        change ‖interiorModuleTensorMk
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) u z‖ ≤
            ‖z‖ * ‖u‖
        simpa only [mul_comm] using interiorModuleTensorMk_norm_le
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) u z)

/-- Continuous linear maps on the concrete regular amplification are determined
by the actual triple elementary tensors. -/
private theorem regularAmplification_clm_ext {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    {S T : InteriorModuleTensor
      (B := ReducedCrossedProduct β) (C := B)
      (E := Module β E)
      (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) →L[ℂ] P}
    (h : ∀ (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ)
      (z : ReducedCrossedHilbertModule B Γ),
      S (interiorModuleTensorMk (B := ReducedCrossedProduct β) (C := B)
        (E := Module β E)
        (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
        (mk β E x c) z) =
      T (interiorModuleTensorMk (B := ReducedCrossedProduct β) (C := B)
        (E := Module β E)
        (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
        (mk β E x c) z)) :
    S = T := by
  apply regularAmplification_outer_clm_ext β E (P := P)
  intro u z
  have hh : S.comp (regularAmplification_leftPureCLM β E z) =
      T.comp (regularAmplification_leftPureCLM β E z) := by
    apply descentModule_clm_ext β E (P := P)
    intro x c
    exact h x c z
  exact DFunLike.congr_fun hh u

/-- The regular coefficient representation acts by actual left translation. -/
private theorem regularCoefficientRepresentation_leftRegular (g : Γ)
    (c : ReducedCrossedProduct β) (z : ReducedCrossedHilbertModule B Γ) :
    regularCoefficientRepresentation β (leftRegular β g c) z =
      reducedCrossedRegular g (regularCoefficientRepresentation β c z) := rfl

include hπ

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
/-- The original equivariance equation, evaluated before tensoring. -/
private theorem originalRepresentation_action (g : Γ) (a : A) (x : E) :
    U.action g (π a x) = π (α.automorphism g a) (U.action g x) := by
  have h := congrArg (fun T : AdjointableMap B E E => T (U.action g x)) (hπ g a)
  simpa only [EquivariantHilbertModule.conjugateMap_apply, U.inv_apply_apply] using h

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] [CompleteSpace E] in
/-- The exact finite-coordinate intertwining equation. Its proof uses only
the given action, given representation equivariance, and coefficient linearity. -/
private theorem regularFactor_finite_generator (a : A) (g : Γ) (x : E)
    (f : ReducedCrossedVectors B Γ) :
    ReducedRegularTensorEmbedding.finite U (π a (U.action g x))
        (reducedCrossedEmbeddingLinear (Equiv.mulLeft g).toEmbedding f) =
      ReducedSourceRegular.finiteGenerator α π a g
        (ReducedRegularTensorEmbedding.finite U x f) := by
  ext t
  simp only [ReducedRegularTensorEmbedding.finite_apply,
    reducedCrossedRegular_finite_apply, ReducedSourceRegular.finiteGenerator_apply]
  rw [originalRepresentation_action β E α U π hπ]
  simp only [← U.mul_apply, mul_inv_rev, inv_inv, (π (α.automorphism t⁻¹ a)).map_op_smul]

/-- The actual regular tensor formula intertwines the source generator on
all completed regular vectors, by its proved finite-vector density. -/
private theorem regularFactor_generator (a : A) (g : Γ) (x : E)
    (z : ReducedCrossedHilbertModule B Γ) :
    ReducedRegularTensorEmbedding.factor U (π a (U.action g x))
        (reducedCrossedRegular g z) =
      ReducedSourceRegular.operatorCLM α π (AlgebraicCrossedProduct.single α g a)
        (ReducedRegularTensorEmbedding.factor U x z) := by
  refine reducedCrossedMk_denseRange.induction_on z
    (isClosed_eq
      ((ReducedRegularTensorEmbedding.factor U (π a (U.action g x))).continuous.comp
        (reducedCrossedRegular g).toCLM.continuous)
      ((ReducedSourceRegular.operatorCLM α π
        (AlgebraicCrossedProduct.single α g a)).continuous.comp
          (ReducedRegularTensorEmbedding.factor U x).continuous)) ?_
  intro f
  rw [reducedCrossedRegular_mk, ReducedRegularTensorEmbedding.factor_mk,
    ReducedRegularTensorEmbedding.factor_mk, ReducedSourceRegular.operatorCLM_mk,
    ReducedSourceRegular.finiteAction_single, regularFactor_finite_generator β E α U π hπ]

/-- The source generator intertwining equation on the actual triple pure tensors. -/
private theorem regularEmbedding_sourceGenerator_triple (a : A) (g : Γ)
    (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : ReducedCrossedHilbertModule B Γ) :
    regularEmbedding β E U
      (interiorModuleTensorOperator
        (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
        (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
        (sourceGenerator β E U π a g)
        (interiorModuleTensorMk (E := Module β E) (regularCoefficientRepresentation β)
          (mk β E x c) z)) =
      ReducedSourceRegular.operatorCLM α π (AlgebraicCrossedProduct.single α g a)
        (regularEmbedding β E U
          (interiorModuleTensorMk (E := Module β E) (regularCoefficientRepresentation β)
            (mk β E x c) z)) := by
  have hAmp := interiorModuleTensorOperator_mk
    (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
    (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
    (sourceGenerator β E U π a g) (mk β E x c) z
  have hSource := sourceGenerator_mk β E U π a g x c
  have hLeft := (regularEmbedding_triple β E U (π a (U.action g x))
    (MulOpposite.op (leftRegular β g (MulOpposite.unop c))) z).trans
      (ReducedRegularTensorEmbedding.isometry_mk U (π a (U.action g x))
        (regularCoefficientRepresentation β (leftRegular β g (MulOpposite.unop c)) z))
  have hRight := (regularEmbedding_triple β E U x c z).trans
    (ReducedRegularTensorEmbedding.isometry_mk U x
      (regularCoefficientRepresentation β (MulOpposite.unop c) z))
  calc
    _ = regularEmbedding β E U
        (interiorModuleTensorMk (B := ReducedCrossedProduct β) (C := B)
          (E := Module β E) (F := ReducedCrossedHilbertModule B Γ)
          (regularCoefficientRepresentation β) (sourceGenerator β E U π a g (mk β E x c)) z) :=
      congrArg (regularEmbedding β E U) hAmp
    _ = regularEmbedding β E U
        (interiorModuleTensorMk (B := ReducedCrossedProduct β) (C := B)
          (E := Module β E) (F := ReducedCrossedHilbertModule B Γ)
          (regularCoefficientRepresentation β)
          (mk β E (π a (U.action g x))
            (MulOpposite.op (leftRegular β g (MulOpposite.unop c)))) z) :=
      congrArg (fun v : Module β E => regularEmbedding β E U
        (interiorModuleTensorMk (B := ReducedCrossedProduct β) (C := B)
          (E := Module β E) (F := ReducedCrossedHilbertModule B Γ)
          (regularCoefficientRepresentation β) v z)) hSource
    _ = ReducedRegularTensorEmbedding.factor U (π a (U.action g x))
        (regularCoefficientRepresentation β (leftRegular β g (MulOpposite.unop c)) z) := hLeft
    _ = ReducedRegularTensorEmbedding.factor U (π a (U.action g x))
        (reducedCrossedRegular g (regularCoefficientRepresentation β (MulOpposite.unop c) z)) :=
      congrArg (ReducedRegularTensorEmbedding.factor U (π a (U.action g x)))
        (regularCoefficientRepresentation_leftRegular β g (MulOpposite.unop c) z)
    _ = ReducedSourceRegular.operatorCLM α π (AlgebraicCrossedProduct.single α g a)
        (ReducedRegularTensorEmbedding.factor U x
          (regularCoefficientRepresentation β (MulOpposite.unop c) z)) :=
      regularFactor_generator β E α U π hπ a g x _
    _ = _ := congrArg
      (ReducedSourceRegular.operatorCLM α π (AlgebraicCrossedProduct.single α g a)) hRight.symm

/-- The actual regular embedding intertwines the faithfully amplified
descended generator with the genuine source regular operator. -/
private theorem regularEmbedding_sourceGenerator (a : A) (g : Γ)
    (u : InteriorModuleTensor (E := Module β E) (regularCoefficientRepresentation β)) :
    regularEmbedding β E U
        (interiorModuleTensorOperator
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
          (sourceGenerator β E U π a g) u) =
      ReducedSourceRegular.operatorCLM α π (AlgebraicCrossedProduct.single α g a)
        (regularEmbedding β E U u) := by
  let W : InteriorModuleTensor
      (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
      (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
      →L[ℂ] IndexedHilbertModule.Module B E Γ :=
    (regularEmbedding β E U).toContinuousLinearMap
  have h : W.comp (interiorModuleTensorOperator
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
      (sourceGenerator β E U π a g)).toCLM =
      (ReducedSourceRegular.operatorCLM α π
        (AlgebraicCrossedProduct.single α g a)).comp W := by
    with_reducible_and_instances
      apply regularAmplification_clm_ext β E (P := IndexedHilbertModule.Module B E Γ)
    intro x c z
    change regularEmbedding β E U
      (interiorModuleTensorOperator
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
        (sourceGenerator β E U π a g)
        (interiorModuleTensorMk (E := Module β E) (regularCoefficientRepresentation β) (mk β E x c) z)) = _
    exact regularEmbedding_sourceGenerator_triple β E α U π hπ a g x c z
  exact DFunLike.congr_fun h u

/-- Finite integration preserves the actual regular intertwining equation. -/
private theorem regularEmbedding_algebraicSourceOperator (f : AlgebraicCrossedProduct α)
    (u : InteriorModuleTensor (E := Module β E) (regularCoefficientRepresentation β)) :
    regularEmbedding β E U
        (interiorModuleTensorOperator
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
          (algebraicSourceOperatorHom β E α U π hπ f) u) =
      ReducedSourceRegular.operatorCLM α π f (regularEmbedding β E U u) := by
  change regularEmbedding β E U
    (interiorModuleTensorOperatorHom
      (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
      (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
      (algebraicSourceOperatorHom β E α U π hπ f) u) = _
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero =>
    simp only [map_zero, AdjointableMap.coe_zero_apply,
      ReducedSourceRegular.operatorCLM_zero, zero_apply]
  | single g a =>
    simpa only [algebraicSourceOperatorHom_single, interiorModuleTensorOperatorHom_apply]
      using regularEmbedding_sourceGenerator β E α U π hπ a g u
  | add f h hf hh =>
    simp only [map_add, AdjointableMap.coe_add_apply,
      ReducedSourceRegular.operatorCLM_add, add_apply, hf, hh]

/-- The genuine norm bridge: the actual descended algebraic operator is
bounded by the concrete regular reduced norm. Faithfulness is the proved
subtype inclusion of the crossed coefficient algebra, and not an assumption
on the original source representation π. -/
theorem algebraicSourceOperator_norm_le (f : AlgebraicCrossedProduct α) :
    ‖algebraicSourceOperatorHom β E α U π hπ f‖ ≤
      ‖algebraicCrossedOperatorHom α f‖ := by
  rw [← norm_regularAmplification β E (algebraicSourceOperatorHom β E α U π hπ f)]
  change ‖(interiorModuleTensorOperator
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
    (algebraicSourceOperatorHom β E α U π hπ f)).toCLM‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  calc
    _ = ‖regularEmbedding β E U
        (interiorModuleTensorOperator
          (B := ReducedCrossedProduct β) (C := B) (E := Module β E)
          (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β)
          (algebraicSourceOperatorHom β E α U π hπ f) u)‖ :=
      ((regularEmbedding β E U).norm_map _).symm
    _ = ‖ReducedSourceRegular.operatorCLM α π f (regularEmbedding β E U u)‖ :=
      congrArg (fun v : IndexedHilbertModule.Module B E Γ => ‖v‖)
        (regularEmbedding_algebraicSourceOperator β E α U π hπ f u)
    _ ≤ ‖algebraicCrossedOperatorHom α f‖ * ‖regularEmbedding β E U u‖ :=
      ReducedSourceRegular.operatorCLM_norm_apply_le α π f _
    _ = _ := by rw [(regularEmbedding β E U).norm_map]

/-- The actual completed source crossed-product representation. It is
constructed from the finite covariant sum and the proved norm bridge. -/
def reducedSourceRepresentation : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
    AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
  extendReducedRepresentation α (algebraicSourceOperatorHom β E α U π hπ)
    (algebraicSourceOperator_norm_le β E α U π hπ)

/-- The completed representation agrees with the actual finite integration
on the actual dense algebraic embedding. -/
@[simp] theorem reducedSourceRepresentation_algebraic (f : AlgebraicCrossedProduct α) :
    reducedSourceRepresentation β E α U π hπ (algebraicToReducedCrossed α f) =
      algebraicSourceOperatorHom β E α U π hπ f :=
  extendReducedRepresentation_algebraic α (algebraicSourceOperatorHom β E α U π hπ)
    (algebraicSourceOperator_norm_le β E α U π hπ) f

/-- The generator formula expected by the actual raw-cycle construction. -/
@[simp] theorem reducedSourceRepresentation_single (g : Γ) (a : A) :
    reducedSourceRepresentation β E α U π hπ
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) =
      sourceGenerator β E U π a g := by
  rw [reducedSourceRepresentation_algebraic, algebraicSourceOperatorHom_single]

/-- The same formula directly on a concrete regular generator of the closed algebra. -/
theorem reducedSourceRepresentation_generator (a : A) (g : Γ) :
    reducedSourceRepresentation β E α U π hπ
        (⟨reducedCrossedGenerator α a g, reducedCrossedGenerator_mem α a g⟩ :
          ReducedCrossedProduct α) = sourceGenerator β E U π a g := by
  have hgen : (⟨reducedCrossedGenerator α a g,
      reducedCrossedGenerator_mem α a g⟩ : ReducedCrossedProduct α) =
      algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a) := by
    apply Subtype.ext
    exact (algebraicToReducedCrossed_single α g a).symm
  rw [hgen]
  exact reducedSourceRepresentation_single β E α U π hπ g a

/-- Restriction to the actual coefficient inclusion is the actual tensor
of the original source representation. -/
@[simp] theorem reducedSourceRepresentation_coefficient (a : A) :
    reducedSourceRepresentation β E α U π hπ (coefficientToReducedCrossed α a) =
      sourceRepresentation β E π a := by
  have hcoefficient : coefficientToReducedCrossed α a =
      algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α (1 : Γ) a) := by
    apply Subtype.ext
    rw [coefficientToReducedCrossed_coe, algebraicToReducedCrossed_single,
      reducedCrossedGenerator, reducedCrossedRegular_one, mul_one]
  calc
    _ = reducedSourceRepresentation β E α U π hπ
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α (1 : Γ) a)) :=
      congrArg (reducedSourceRepresentation β E α U π hπ) hcoefficient
    _ = sourceGenerator β E U π a 1 :=
      reducedSourceRepresentation_single β E α U π hπ 1 a
    _ = _ := by
      change sourceRepresentation β E π a * groupOperator β E U 1 = _
      exact (congrArg
        (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
          sourceRepresentation β E π a * T)
        (groupOperator_one β E U)).trans (mul_one (sourceRepresentation β E π a))

theorem reducedSourceRepresentation_comp_algebraic :
    (reducedSourceRepresentation β E α U π hπ).comp (algebraicToReducedCrossed α) =
      algebraicSourceOperatorHom β E α U π hπ := by
  apply DFunLike.ext
  intro f
  exact reducedSourceRepresentation_algebraic β E α U π hπ f

theorem continuous_reducedSourceRepresentation :
    Continuous (reducedSourceRepresentation β E α U π hπ) := by
  change Continuous (extendReducedRepresentationCLM α (algebraicSourceOperatorHom β E α U π hπ))
  exact (extendReducedRepresentationCLM α (algebraicSourceOperatorHom β E α U π hπ)).continuous

theorem norm_reducedSourceRepresentation_le (z : ReducedCrossedProduct α) :
    ‖reducedSourceRepresentation β E α U π hπ z‖ ≤ ‖z‖ :=
  NonUnitalStarAlgHom.norm_apply_le (reducedSourceRepresentation β E α U π hπ) z

/-- Equality on the actual dense finite integration determines the completed
source representation. No density of its image in the whole adjointable
algebra is asserted. -/
theorem reducedSourceRepresentation_unique
    (ψ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hψ : ∀ f : AlgebraicCrossedProduct α,
      ψ (algebraicToReducedCrossed α f) = algebraicSourceOperatorHom β E α U π hπ f) :
    ψ = reducedSourceRepresentation β E α U π hπ := by
  apply DFunLike.ext
  intro z
  refine (algebraicToReducedCrossed_denseRange α).induction_on z
    (isClosed_eq (map_continuous ψ) (continuous_reducedSourceRepresentation β E α U π hπ)) ?_
  intro f
  rw [hψ, reducedSourceRepresentation_algebraic]

/-- The finite integrated image is dense in exactly the closure of the
completed representation's image. -/
theorem reducedSourceRepresentation_range_closure :
    closure (Set.range (reducedSourceRepresentation β E α U π hπ)) =
      closure (Set.range (algebraicSourceOperatorHom β E α U π hπ)) := by
  apply le_antisymm
  · apply closure_minimal ?_ isClosed_closure
    rintro _ ⟨z, rfl⟩
    refine (algebraicToReducedCrossed_denseRange α).induction_on z
      (isClosed_closure.preimage (continuous_reducedSourceRepresentation β E α U π hπ)) ?_
    intro f
    rw [reducedSourceRepresentation_algebraic]
    exact subset_closure ⟨f, rfl⟩
  · apply closure_minimal ?_ isClosed_closure
    rintro _ ⟨f, rfl⟩
    exact subset_closure ⟨algebraicToReducedCrossed α f,
      reducedSourceRepresentation_algebraic β E α U π hπ f⟩

end BC4lean.KKTheory.KasparovDescent
