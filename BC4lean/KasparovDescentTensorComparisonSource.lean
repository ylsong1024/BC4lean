import BC4lean.KasparovDescentTensorComparison
import BC4lean.ModuleTensorCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual integrated source compatibility of the crossed tensor comparison

The construction uses the concrete reduced representations and
comparison helpers. The proof
constructs the original tensor covariant pair, proves compatibility with its
actual group operators, then extends the exact crossed-generator law by
finite induction and actual reduced-norm density. No source-intertwining
conclusion, nondegeneracy premise, or product property is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

private theorem reduced_intertwining_of_single_aux
    {G A₀ D M N : Type*} [Group G]
    [NonUnitalCStarAlgebra A₀] [PartialOrder A₀] [StarOrderedRing A₀]
    [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Dᵐᵒᵖ M]
    [CStarModule Dᵐᵒᵖ M] [CompleteSpace M]
    [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Dᵐᵒᵖ N]
    [CStarModule Dᵐᵒᵖ N] [CompleteSpace N]
    (α₀ : CStarAlgebraAction G A₀)
    (L : ReducedCrossedProduct α₀ →⋆ₙₐ[ℂ] AdjointableMap D M M)
    (R : ReducedCrossedProduct α₀ →⋆ₙₐ[ℂ] AdjointableMap D N N)
    (Q : HilbertModuleEquiv D M N)
    (hL : Continuous L) (hR : Continuous R)
    (hsingle : ∀ g a v,
      Q (L (algebraicToReducedCrossed α₀ (AlgebraicCrossedProduct.single α₀ g a)) v) =
        R (algebraicToReducedCrossed α₀ (AlgebraicCrossedProduct.single α₀ g a)) (Q v))
    (z : ReducedCrossedProduct α₀) (u : M) :
    Q (L z u) = R z (Q u) := by
  have hcL : Continuous (fun w : ReducedCrossedProduct α₀ => L w u) :=
    (AdjointableMap.toCLM_isometry.continuous.comp hL).clm_apply continuous_const
  have hcR : Continuous (fun w : ReducedCrossedProduct α₀ => R w (Q u)) :=
    (AdjointableMap.toCLM_isometry.continuous.comp hR).clm_apply continuous_const
  refine (algebraicToReducedCrossed_denseRange α₀).induction_on z
    (isClosed_eq (Q.linearIsometryEquiv.continuous.comp hcL) hcR) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on α₀ with
  | zero =>
    simp only [map_zero, AdjointableMap.coe_zero_apply]
  | single g a => exact hsingle g a u
  | add f h ihf ihh =>
    simp only [map_add, AdjointableMap.coe_add_apply, ihf, ihh]

private theorem tensorComparison_associator_action_mk_aux
    {Γ B C D E F G : Type*} [Group Γ]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
    [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G]
    [CStarModule Dᵐᵒᵖ G] [CompleteSpace G]
    {α : CStarAlgebraAction Γ B} {β : CStarAlgebraAction Γ C}
    {δ : CStarAlgebraAction Γ D}
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)
    (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule β F)
    (Z : EquivariantHilbertModule δ G)
    (hφ : ModuleTensorRepresentationEquivariant φ α V)
    (hψ : ModuleTensorRepresentationEquivariant ψ β Z)
    (g : Γ) (x : E) (y : InteriorModuleTensor (E := F) ψ) :
    (InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) φ ψ).symm
      (interiorModuleTensorMk
        (InteriorModuleTensorAssociator.rightRepresentation φ ψ)
        (U.action g x) ((V.interiorTensor Z hψ).action g y)) =
    (((U.interiorTensor V hφ).interiorTensor Z hψ).action g)
      ((InteriorModuleTensorAssociator.hilbertEquiv
        (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) φ ψ).symm
          (interiorModuleTensorMk
            (InteriorModuleTensorAssociator.rightRepresentation φ ψ) x y)) := by
  let A : HilbertModuleEquiv D
      (InteriorModuleTensorAssociator.LeftTensor (E := E) φ ψ)
      (InteriorModuleTensorAssociator.RightTensor (E := E) φ ψ) :=
    InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) φ ψ
  let JL : InteriorModuleTensorAssociator.LeftTensor (E := E) φ ψ ≃ₗᵢ[ℂ]
      InteriorModuleTensorAssociator.LeftTensor (E := E) φ ψ :=
    ((U.interiorTensor V hφ).interiorTensor Z hψ).action g
  let JR : InteriorModuleTensorAssociator.RightTensor (E := E) φ ψ ≃ₗᵢ[ℂ]
      InteriorModuleTensorAssociator.RightTensor (E := E) φ ψ :=
    (U.interiorTensor (V.interiorTensor Z hψ)
      (InteriorModuleTensorAssociator.rightRepresentation_equivariant
        (B := B) (C := C) (D := D) (F := F) (G := G)
        (Γ := Γ) (α := α) (β := β) (χ := δ) φ ψ V Z hφ hψ)).action g
  let v : InteriorModuleTensorAssociator.RightTensor (E := E) φ ψ :=
    interiorModuleTensorMk
      (InteriorModuleTensorAssociator.rightRepresentation φ ψ) x y
  have h₀ := InteriorModuleTensorAssociator.hilbertEquiv_action_intertwine
    (B := B) (C := C) (D := D) (E := E) (F := F) (G := G)
    (Γ := Γ) (α := α) (β := β) (χ := δ) φ ψ U V Z hφ hψ g (A.symm v)
  have h₁ : A (JL (A.symm v)) = JR v :=
    h₀.trans (congrArg
      (fun w : InteriorModuleTensorAssociator.RightTensor (E := E) φ ψ => JR w)
      (A.apply_symm_apply v))
  have hInv : A.symm (JR v) = JL (A.symm v) :=
    (congrArg
      (fun w : InteriorModuleTensorAssociator.RightTensor (E := E) φ ψ => A.symm w)
      h₁).symm.trans (A.symm_apply_apply (JL (A.symm v)))
  have hMk := EquivariantHilbertModule.interiorTensor_action_mk
    (B := B) (C := D) (E := E)
    (F := InteriorModuleTensor (E := F) ψ)
    (Γ := Γ) (α := α) (β := δ)
    (φ := InteriorModuleTensorAssociator.rightRepresentation φ ψ)
    U (V.interiorTensor Z hψ)
    (InteriorModuleTensorAssociator.rightRepresentation_equivariant
      (B := B) (C := C) (D := D) (F := F) (G := G)
      (Γ := Γ) (α := α) (β := β) (χ := δ) φ ψ V Z hφ hψ) g x y
  exact (congrArg
    (fun w : InteriorModuleTensorAssociator.RightTensor (E := E) φ ψ => A.symm w)
    hMk).symm.trans hInv

variable {Γ B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (V : EquivariantHilbertModule γ F)
  (π : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (hπ : ∀ g b, V.conjugateOperator g (π b) = π (β.automorphism g b))

/-- Actual left regular multiplication changes the coefficient and group index
of the concrete algebraic generator. -/
theorem tensorComparison_leftRegular_single (g h : Γ) (b : B) :
    leftRegular β g (algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β h b)) =
      algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β (g * h) (β.automorphism g b)) := by
  apply Subtype.ext
  simp only [leftRegular_coe, algebraicToReducedCrossed_single]
  exact regular_mul_generator β g h b

/-- A genuine reduced representation intertwines the actual left multiplier
with its constructed group unitary. The identity holds for every whole
crossed coefficient, obtained from finite generators by continuity. -/
theorem tensorComparison_source_leftRegular (g : Γ) (d : ReducedCrossedProduct β) :
    reducedSourceRepresentation γ F β V π hπ (leftRegular β g d) =
      groupOperator γ F V g * reducedSourceRepresentation γ F β V π hπ d := by
  let ρ : ReducedCrossedProduct β →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) :=
    reducedSourceRepresentation γ F β V π hπ
  let K : B →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) :=
    sourceRepresentation γ F π
  let G : Γ → AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) :=
    groupOperator γ F V
  have hs (h : Γ) (b : B) :
      ρ (algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β h b)) = K b * G h :=
    reducedSourceRepresentation_single γ F β V π hπ h b
  have hρ : Continuous ρ :=
    continuous_reducedSourceRepresentation γ F β V π hπ
  have hL : Continuous (leftRegular β g) :=
    MulOpposite.continuous_unop.comp
      ((leftRegularIsometry β g).continuous.comp MulOpposite.continuous_op)
  have hzero : leftRegular β g 0 = 0 := by
    apply Subtype.ext
    simp only [leftRegular_coe, ZeroMemClass.coe_zero, mul_zero]
  have hadd (d e : ReducedCrossedProduct β) :
      leftRegular β g (d + e) = leftRegular β g d + leftRegular β g e := by
    apply Subtype.ext
    exact mul_add _ _ _
  refine (algebraicToReducedCrossed_denseRange β).induction_on d
    (isClosed_eq (hρ.comp hL)
      (continuous_const.mul hρ)) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on β with
  | zero => simp only [map_zero, hzero, mul_zero]
  | single h b =>
    calc
      ρ (leftRegular β g
          (algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β h b))) =
          ρ (algebraicToReducedCrossed β
            (AlgebraicCrossedProduct.single β (g * h) (β.automorphism g b))) :=
        congrArg (fun c : ReducedCrossedProduct β => ρ c)
          (tensorComparison_leftRegular_single β g h b)
      _ = K (β.automorphism g b) * G (g * h) := hs (g * h) _
      _ = K (β.automorphism g b) * (G g * G h) :=
        congrArg
          (fun T : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) =>
            K (β.automorphism g b) * T)
          (groupOperator_mul γ F V g h)
      _ = (K (β.automorphism g b) * G g) * G h := (mul_assoc _ _ _).symm
      _ = (G g * K b) * G h :=
        congrArg
          (fun T : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) =>
            T * G h)
          (sourceRepresentation_covariance γ F β V π hπ g b)
      _ = G g * (K b * G h) := mul_assoc _ _ _
      _ = G g * ρ
          (algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β h b)) :=
        congrArg
          (fun T : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) =>
            G g * T) (hs h b).symm
  | add f h ihf ihh => simp only [map_add, hadd, ihf, ihh, mul_add]

private theorem tensorComparison_groupOperator_mk_aux
    (U : EquivariantHilbertModule β E) (g : Γ) (x : E)
    (d : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : Module γ F) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorOperator (reducedSourceRepresentation γ F β V π hπ)
        (groupOperator β E U g)
        (interiorModuleTensorMk (reducedSourceRepresentation γ F β V π hπ)
          (mk β E x d) z)) =
      groupOperator γ (InteriorModuleTensor (E := E) π)
        (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)) g
        (tensorComparison β γ V π hπ
          (interiorModuleTensorMk (reducedSourceRepresentation γ F β V π hπ)
            (mk β E x d) z)) := by
  let ρ := reducedSourceRepresentation γ F β V π hπ
  let ψ := InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ)
  let A := InteriorModuleTensorAssociator.hilbertEquiv
    (B := B) (C := C) (D := ReducedCrossedProduct γ)
    (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ) π (coefficientRepresentation γ)
  let Q := tensorComparison (E := E) β γ V π hπ
  let K := groupOperator γ (InteriorModuleTensor (E := E) π)
    (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)) g
  have hop := interiorModuleTensorOperator_mk ρ (groupOperator β E U g) (mk β E x d) z
  have hgroup := groupOperator_mk β E U g x d
  have hOp := hop.trans
    (congrArg (fun v : Module β E => interiorModuleTensorMk ρ v z) hgroup)
  have hc := congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) => T z)
    (tensorComparison_source_leftRegular β γ V π hπ g (MulOpposite.unop d))
  have h₁ := congrArg
    (fun v : InteriorModuleTensor (E := Module β E) ρ => Q v) hOp
  have h₂ := tensorComparison_mk β γ V π hπ (U.action g x)
    (MulOpposite.op (leftRegular β g (MulOpposite.unop d))) z
  have h₃ := congrArg (fun v : Module γ F =>
    A.symm (interiorModuleTensorMk ψ (U.action g x) v)) hc
  have h₄ := tensorComparison_associator_action_mk_aux
    (B := B) (C := C) (D := ReducedCrossedProduct γ)
    (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
    π (coefficientRepresentation γ) U V (leftRegularAction γ)
    (V.representationEquivariant_of_conjugate hπ)
    (coefficientRepresentation_equivariant γ) g x (ρ (MulOpposite.unop d) z)
  have h₅ := congrArg
    (fun v : Module γ (InteriorModuleTensor (E := E) π) => K v)
    (tensorComparison_mk β γ V π hπ x d z).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- The comparison intertwines the actual amplified first-module group
operator with the actual diagonal group operator on the descended original
tensor. The proof uses the left multiplier identity, not an element λ_g in
an incorrectly unitized crossed algebra. -/
theorem tensorComparison_groupOperator (U : EquivariantHilbertModule β E) (g : Γ)
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β V π hπ)) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorOperator (reducedSourceRepresentation γ F β V π hπ)
        (groupOperator β E U g) u) =
      groupOperator γ (InteriorModuleTensor (E := E) π)
        (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)) g
          (tensorComparison β γ V π hπ u) := by
  let ρ := reducedSourceRepresentation γ F β V π hπ
  let W : EquivariantHilbertModule γ (InteriorModuleTensor (E := E) π) :=
    U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)
  let Q : HilbertModuleEquiv (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E) ρ)
      (Module γ (InteriorModuleTensor (E := E) π)) :=
    tensorComparison (E := E) β γ V π hπ
  let H : AdjointableMap (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E) ρ)
      (InteriorModuleTensor (E := Module β E) ρ) :=
    interiorModuleTensorOperator ρ (groupOperator β E U g)
  let K : AdjointableMap (ReducedCrossedProduct γ)
      (Module γ (InteriorModuleTensor (E := E) π))
      (Module γ (InteriorModuleTensor (E := E) π)) :=
    groupOperator γ (InteriorModuleTensor (E := E) π) W g
  let L : InteriorModuleTensor (E := Module β E) ρ →L[ℂ]
      Module γ (InteriorModuleTensor (E := E) π) :=
    Q.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp H.toCLM = K.toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
      (E := Module β E) (F := Module γ F) (φ := ρ)
    intro ξ z
    let P : Module β E →L[ℂ] InteriorModuleTensor (E := Module β E) ρ :=
      InteriorModuleTensorScalarExtension.pureCLM
        (B := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
        (E := Module β E) (H := Module γ F) ρ z
    have hinner : (L.comp H.toCLM).comp P = (K.toCLM.comp L).comp P := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
        (B := B) (C := ReducedCrossedProduct β)
        (E := E) (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
        (φ := coefficientRepresentation β)
      intro x d
      exact tensorComparison_groupOperator_mk_aux β γ V π hπ U g x d z
    exact DFunLike.congr_fun hinner ξ
  exact DFunLike.congr_fun h u

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAlgebraAction Γ A) (U : EquivariantHilbertModule β E)
  (κ : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
  (hκ : ∀ g a, U.conjugateOperator g (κ a) = κ (α.automorphism g a))

omit [PartialOrder A] [StarOrderedRing A] in
include hκ in
/-- Original tensor covariance follows from the actual completed tensor action. -/
theorem tensorComparison_tensorRepresentation_equivariant (g : Γ) (a : A) :
    (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)).conjugateOperator g
      (InteriorModuleTensorAssociator.rightRepresentation κ π a) =
        InteriorModuleTensorAssociator.rightRepresentation κ π (α.automorphism g a) := by
  change (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)).conjugateOperator g
    (interiorModuleTensorOperator π (κ a)) = _
  rw [EquivariantHilbertModule.interiorTensor_conjugateOperator, hκ]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The concrete crossed generators of the original source are intertwined. -/
theorem tensorComparison_sourceGenerator (a : A) (g : Γ)
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β V π hπ)) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorOperator (reducedSourceRepresentation γ F β V π hπ)
        (sourceGenerator β E U κ a g) u) =
      sourceGenerator γ (InteriorModuleTensor (E := E) π)
        (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ))
        (InteriorModuleTensorAssociator.rightRepresentation κ π) a g
          (tensorComparison β γ V π hπ u) := by
  let ρ : ReducedCrossedProduct β →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) :=
    reducedSourceRepresentation γ F β V π hπ
  let W : EquivariantHilbertModule γ (InteriorModuleTensor (E := E) π) :=
    U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)
  let Q : HilbertModuleEquiv (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E) ρ)
      (Module γ (InteriorModuleTensor (E := E) π)) :=
    tensorComparison (E := E) β γ V π hπ
  let H : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) →⋆ₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ)
        (InteriorModuleTensor (E := Module β E) ρ)
        (InteriorModuleTensor (E := Module β E) ρ) :=
    interiorModuleTensorOperatorHom ρ
  let P : AdjointableMap (ReducedCrossedProduct γ)
      (Module γ (InteriorModuleTensor (E := E) π))
      (Module γ (InteriorModuleTensor (E := E) π)) :=
    operatorHom γ (InteriorModuleTensor (E := E) π) (interiorModuleTensorOperator π (κ a))
  let K : AdjointableMap (ReducedCrossedProduct γ)
      (Module γ (InteriorModuleTensor (E := E) π))
      (Module γ (InteriorModuleTensor (E := E) π)) :=
    groupOperator γ (InteriorModuleTensor (E := E) π) W g
  have hsource : sourceGenerator β E U κ a g =
      operatorHom β E (κ a) * groupOperator β E U g := rfl
  have hmap : H (sourceGenerator β E U κ a g) =
      H (operatorHom β E (κ a)) * H (groupOperator β E U g) :=
    (congrArg H hsource).trans
      (map_mul H (operatorHom β E (κ a)) (groupOperator β E U g))
  calc
    Q (H (sourceGenerator β E U κ a g) u) =
        Q ((H (operatorHom β E (κ a)) * H (groupOperator β E U g)) u) :=
      congrArg (fun T : AdjointableMap (ReducedCrossedProduct γ)
        (InteriorModuleTensor (E := Module β E) ρ)
        (InteriorModuleTensor (E := Module β E) ρ) => Q (T u)) hmap
    _ = Q (H (operatorHom β E (κ a)) (H (groupOperator β E U g) u)) := rfl
    _ = P (Q (H (groupOperator β E U g) u)) :=
      tensorComparison_operator β γ V π hπ (κ a) (H (groupOperator β E U g) u)
    _ = P (K (Q u)) :=
      congrArg (fun v : Module γ (InteriorModuleTensor (E := E) π) => P v)
        (tensorComparison_groupOperator β γ V π hπ U g u)
    _ = sourceGenerator γ (InteriorModuleTensor (E := E) π) W
        (InteriorModuleTensorAssociator.rightRepresentation κ π) a g (Q u) := rfl

private theorem tensorComparison_reducedSource_single_aux (g : Γ) (a : A)
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β V π hπ)) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorOperator (reducedSourceRepresentation γ F β V π hπ)
        (reducedSourceRepresentation β E α U κ hκ
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))) u) =
      reducedSourceRepresentation γ (InteriorModuleTensor (E := E) π) α
        (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ))
        (InteriorModuleTensorAssociator.rightRepresentation κ π)
        (tensorComparison_tensorRepresentation_equivariant β γ V π hπ α U κ hκ)
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))
          (tensorComparison β γ V π hπ u) := by
  let ρ := reducedSourceRepresentation γ F β V π hπ
  let Q := tensorComparison (E := E) β γ V π hπ
  let W := U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)
  have hleft : Q
      (interiorModuleTensorOperator ρ
        (reducedSourceRepresentation β E α U κ hκ
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))) u) =
      Q (interiorModuleTensorOperator ρ (sourceGenerator β E U κ a g) u) :=
    congrArg (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
      Q (interiorModuleTensorOperator ρ T u))
      (reducedSourceRepresentation_single β E α U κ hκ g a)
  have hmiddle : Q (interiorModuleTensorOperator ρ (sourceGenerator β E U κ a g) u) =
      sourceGenerator γ (InteriorModuleTensor (E := E) π) W
        (InteriorModuleTensorAssociator.rightRepresentation κ π) a g (Q u) :=
    tensorComparison_sourceGenerator β γ V π hπ U κ a g u
  have hright :
      reducedSourceRepresentation γ (InteriorModuleTensor (E := E) π) α W
        (InteriorModuleTensorAssociator.rightRepresentation κ π)
        (tensorComparison_tensorRepresentation_equivariant β γ V π hπ α U κ hκ)
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) (Q u) =
      sourceGenerator γ (InteriorModuleTensor (E := E) π) W
        (InteriorModuleTensorAssociator.rightRepresentation κ π) a g (Q u) :=
    congrArg (fun T : AdjointableMap (ReducedCrossedProduct γ)
      (Module γ (InteriorModuleTensor (E := E) π))
      (Module γ (InteriorModuleTensor (E := E) π)) => T (Q u))
      (reducedSourceRepresentation_single γ (InteriorModuleTensor (E := E) π) α W
        (InteriorModuleTensorAssociator.rightRepresentation κ π)
        (tensorComparison_tensorRepresentation_equivariant β γ V π hπ α U κ hκ) g a)
  exact hleft.trans (hmiddle.trans hright.symm)

/-- The exact integrated-source intertwining on every completed source
crossed element follows from finite induction and genuine reduced density. -/
theorem tensorComparison_reducedSourceRepresentation
    (z : ReducedCrossedProduct α)
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β V π hπ)) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorOperator (reducedSourceRepresentation γ F β V π hπ)
        (reducedSourceRepresentation β E α U κ hκ z) u) =
      reducedSourceRepresentation γ (InteriorModuleTensor (E := E) π) α
        (U.interiorTensor V (V.representationEquivariant_of_conjugate hπ))
        (InteriorModuleTensorAssociator.rightRepresentation κ π)
        (tensorComparison_tensorRepresentation_equivariant β γ V π hπ α U κ hκ) z
          (tensorComparison β γ V π hπ u) := by
  let ρ : ReducedCrossedProduct β →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) :=
    reducedSourceRepresentation γ F β V π hπ
  let W : EquivariantHilbertModule γ (InteriorModuleTensor (E := E) π) :=
    U.interiorTensor V (V.representationEquivariant_of_conjugate hπ)
  let Q : HilbertModuleEquiv (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E) ρ)
      (Module γ (InteriorModuleTensor (E := E) π)) :=
    tensorComparison (E := E) β γ V π hπ
  let ρA : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    reducedSourceRepresentation β E α U κ hκ
  let H : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) →⋆ₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ)
        (InteriorModuleTensor (E := Module β E) ρ)
        (InteriorModuleTensor (E := Module β E) ρ) :=
    interiorModuleTensorOperatorHom ρ
  let ρL : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ)
        (InteriorModuleTensor (E := Module β E) ρ)
        (InteriorModuleTensor (E := Module β E) ρ) :=
    H.toNonUnitalStarAlgHom.comp ρA
  let ρT : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ)
        (Module γ (InteriorModuleTensor (E := E) π))
        (Module γ (InteriorModuleTensor (E := E) π)) :=
    reducedSourceRepresentation γ (InteriorModuleTensor (E := E) π) α W
      (InteriorModuleTensorAssociator.rightRepresentation κ π)
      (tensorComparison_tensorRepresentation_equivariant β γ V π hπ α U κ hκ)
  have hρA : Continuous ρA :=
    continuous_reducedSourceRepresentation β E α U κ hκ
  have hρL : Continuous ρL :=
    (interiorModuleTensorOperatorCLM (E := Module β E) ρ).continuous.comp hρA
  have hρT : Continuous ρT :=
    continuous_reducedSourceRepresentation γ (InteriorModuleTensor (E := E) π) α W
      (InteriorModuleTensorAssociator.rightRepresentation κ π)
      (tensorComparison_tensorRepresentation_equivariant β γ V π hπ α U κ hκ)
  exact reduced_intertwining_of_single_aux α ρL ρT Q hρL hρT
    (fun g a v => tensorComparison_reducedSource_single_aux β γ V π hπ α U κ hκ g a v) z u

end BC4lean.KKTheory.KasparovDescent
