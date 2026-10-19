import BC4lean.KasparovDescentTensorComparison
import BC4lean.KasparovDescentGradedCycle
import BC4lean.RectangularInteriorModuleTensorCompact
import BC4lean.GradedConnectionDefectAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual signed compact connections under reduced descent

The construction uses the comparison, actual
graded raw descent and compact rectangular tensor helper.
 No product conclusion is assumed here.

The proof uses the original connection defect on every x, obtained from its
four homogeneous laws, and the actual graded crossed commutator at every d.
On x tensor d, the exact defect is the sum of the compact amplified original
connection defect times ρ(d), and the amplified creation map times the genuine
graded commutator at d. The entire defect is a continuous complex-linear map
of the first descended vector. The closed compact preimage and genuine pure
vector density extend the result to every completed first vector, before any
homogeneous specializations. No density of unprojected homogeneous generators
or generatorwise additive positivity argument is used.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

private theorem gradedConnection_of_two_signed_creation_defects
    {G A₀ B₀ C₀ E₀ F₀ : Type*} [Group G]
    [NonUnitalCStarAlgebra A₀] [NonUnitalCStarAlgebra B₀] [NonUnitalCStarAlgebra C₀]
    [PartialOrder B₀] [StarOrderedRing B₀] [PartialOrder C₀] [StarOrderedRing C₀]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [SMul B₀ᵐᵒᵖ E₀]
    [CStarModule B₀ᵐᵒᵖ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [NormedSpace ℂ F₀] [SMul C₀ᵐᵒᵖ F₀]
    [CStarModule C₀ᵐᵒᵖ F₀] [CompleteSpace F₀]
    {α₀ : CStarAlgebraAction G A₀} {β₀ : CStarAlgebraAction G B₀}
    {γ₀ : CStarAlgebraAction G C₀}
    {δA₀ : CStarGrading A₀} {δB₀ : CStarGrading B₀} {δC₀ : CStarGrading C₀}
    (c₀ : GradedKasparovCycle α₀ β₀ δA₀ δB₀ E₀)
    (d₀ : GradedKasparovCycle β₀ γ₀ δB₀ δC₀ F₀)
    (Q : AdjointableMap C₀ (InteriorModuleTensor (E := E₀) d₀.representation)
      (InteriorModuleTensor (E := E₀) d₀.representation))
    (hQ : ∀ x, IsModuleCompact (Q.comp (moduleCreationMap d₀.representation x) -
      (moduleCreationMap d₀.representation (c₀.grading.grading x)).comp d₀.operator))
    (hQstar : ∀ x, IsModuleCompact ((star Q).comp (moduleCreationMap d₀.representation x) -
      (moduleCreationMap d₀.representation (c₀.grading.grading x)).comp (star d₀.operator))) :
    GradedKasparovConnection c₀ d₀ Q := by
  have heven (S : AdjointableMap C₀ F₀ F₀)
      (R : AdjointableMap C₀ (InteriorModuleTensor (E := E₀) d₀.representation)
        (InteriorModuleTensor (E := E₀) d₀.representation))
      (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap d₀.representation x) -
        (moduleCreationMap d₀.representation (c₀.grading.grading x)).comp S))
      (x : E₀) (hx : c₀.grading.grading x = x) :
      IsModuleCompact ((moduleCreationMap d₀.representation x).comp S -
        R.comp (moduleCreationMap d₀.representation x)) := by
    simpa only [hx, neg_sub] using (hR x).neg
  have hodd (S : AdjointableMap C₀ F₀ F₀)
      (R : AdjointableMap C₀ (InteriorModuleTensor (E := E₀) d₀.representation)
        (InteriorModuleTensor (E := E₀) d₀.representation))
      (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap d₀.representation x) -
        (moduleCreationMap d₀.representation (c₀.grading.grading x)).comp S))
      (x : E₀) (hx : c₀.grading.grading x = -x) :
      IsModuleCompact ((moduleCreationMap d₀.representation x).comp S +
        R.comp (moduleCreationMap d₀.representation x)) := by
    have h := hR x
    rw [hx, moduleCreationMap_neg] at h
    have heq : R.comp (moduleCreationMap d₀.representation x) -
        (-moduleCreationMap d₀.representation x).comp S =
        (moduleCreationMap d₀.representation x).comp S +
          R.comp (moduleCreationMap d₀.representation x) := by
      apply AdjointableMap.ext
      intro y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
      abel
    exact Eq.mp
      (congrArg
        (fun T : AdjointableMap C₀ F₀ (InteriorModuleTensor (E := E₀) d₀.representation) =>
          IsModuleCompact T) heq) h
  exact ⟨heven d₀.operator Q hQ, heven (star d₀.operator) (star Q) hQstar,
    hodd d₀.operator Q hQ, hodd (star d₀.operator) (star Q) hQstar⟩

variable {Γ B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]

variable (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (V : EquivariantHilbertModule γ F)
  (π : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (hπ : ∀ g b, V.conjugateOperator g (π b) = π (β.automorphism g b))

/-- Creation followed by the actual whole comparison unitary. -/
def comparisonCreation (ξ : Module β E) :
    AdjointableMap (ReducedCrossedProduct γ) (Module γ F)
      (Module γ (InteriorModuleTensor (E := E) π)) :=
  (tensorComparison (E := E) β γ V π hπ).toAdjointable.comp
    (moduleCreationMap (reducedSourceRepresentation γ F β V π hπ) ξ)

@[simp] theorem comparisonCreation_mk (x : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    comparisonCreation β γ V π hπ (mk β E x d) =
      (RectangularInteriorModuleTensorOperator.tensor (coefficientRepresentation γ)
        (moduleCreationMap π x)).comp
          (reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d)) :=
  tensorComparison_creation β γ V π hπ x d

/-- The original tensor operator is transported by the actual comparison,
with no product or connection conditions built into its definition. -/
def descendedConnectionOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) π)
      (InteriorModuleTensor (E := E) π)) :
    AdjointableMap (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E) (reducedSourceRepresentation γ F β V π hπ))
      (InteriorModuleTensor (E := Module β E) (reducedSourceRepresentation γ F β V π hπ)) :=
  (tensorComparison (E := E) β γ V π hπ).symm.transport
    (operatorHom γ (InteriorModuleTensor (E := E) π) R)

@[simp] theorem descendedConnectionOperator_star
    (R : AdjointableMap C (InteriorModuleTensor (E := E) π)
      (InteriorModuleTensor (E := E) π)) :
    descendedConnectionOperator β γ V π hπ (star R) =
      star (descendedConnectionOperator β γ V π hπ R) := by
  simp only [descendedConnectionOperator, map_star, HilbertModuleEquiv.transport_star]

variable {δB : CStarGrading B} (hβ : β.PreservesGrading δB)
  (J : GradedHilbertModule δB E)
  (S : AdjointableMap C F F)
  (R : AdjointableMap C (InteriorModuleTensor (E := E) π)
    (InteriorModuleTensor (E := E) π))

private theorem comparisonCreation_rectangle_algebra
    {D X Y : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul Dᵐᵒᵖ X] [CStarModule Dᵐᵒᵖ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul Dᵐᵒᵖ Y] [CStarModule Dᵐᵒᵖ Y]
    (R : AdjointableMap D Y Y) (T Tj : AdjointableMap D X Y)
    (S p q : AdjointableMap D X X) :
    R.comp (T.comp p) - (Tj.comp q).comp S =
      (R.comp T - Tj.comp S).comp p + Tj.comp (S * p - q * S) := by
  apply AdjointableMap.ext
  intro y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.mul_apply, map_sub]
  abel

private theorem comparisonCreation_tensor_algebra
    {A D X Y G : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul Aᵐᵒᵖ X] [CStarModule Aᵐᵒᵖ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul Aᵐᵒᵖ Y] [CStarModule Aᵐᵒᵖ Y]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace G]
    (φ : A →⋆ₙₐ[ℂ] AdjointableMap D G G)
    (R : AdjointableMap A Y Y) (T Tj : AdjointableMap A X Y)
    (S : AdjointableMap A X X)
    (p q : AdjointableMap D (InteriorModuleTensor (E := X) φ)
      (InteriorModuleTensor (E := X) φ)) :
    (interiorModuleTensorOperator φ R).comp
        ((RectangularInteriorModuleTensorOperator.tensor φ T).comp p) -
      ((RectangularInteriorModuleTensorOperator.tensor φ Tj).comp q).comp
        (interiorModuleTensorOperator φ S) =
    (RectangularInteriorModuleTensorOperator.tensor φ (R.comp T - Tj.comp S)).comp p +
      (RectangularInteriorModuleTensorOperator.tensor φ Tj).comp
        (interiorModuleTensorOperator φ S * p - q * interiorModuleTensorOperator φ S) := by
  let U : AdjointableMap D (InteriorModuleTensor (E := X) φ)
      (InteriorModuleTensor (E := Y) φ) :=
    RectangularInteriorModuleTensorOperator.tensor φ T
  let Uj : AdjointableMap D (InteriorModuleTensor (E := X) φ)
      (InteriorModuleTensor (E := Y) φ) :=
    RectangularInteriorModuleTensorOperator.tensor φ Tj
  have hR : RectangularInteriorModuleTensorOperator.tensor φ R =
      interiorModuleTensorOperator φ R :=
    RectangularInteriorModuleTensorOperator.tensor_endo
      (B := A) (C := D) (E := Y) (F := G) φ R
  have hS : RectangularInteriorModuleTensorOperator.tensor φ S =
      interiorModuleTensorOperator φ S :=
    RectangularInteriorModuleTensorOperator.tensor_endo
      (B := A) (C := D) (E := X) (F := G) φ S
  have hRT : RectangularInteriorModuleTensorOperator.tensor φ (R.comp T) =
      (interiorModuleTensorOperator φ R).comp U :=
    (RectangularInteriorModuleTensorOperator.tensor_comp
      (B := A) (C := D) (E := X) (E' := Y) (E'' := Y) (F := G) φ T R).trans
        (congrArg (fun K : AdjointableMap D (InteriorModuleTensor (E := Y) φ)
          (InteriorModuleTensor (E := Y) φ) => K.comp U) hR)
  have hTjS : RectangularInteriorModuleTensorOperator.tensor φ (Tj.comp S) =
      Uj.comp (interiorModuleTensorOperator φ S) :=
    (RectangularInteriorModuleTensorOperator.tensor_comp
      (B := A) (C := D) (E := X) (E' := X) (E'' := Y) (F := G) φ S Tj).trans
        (congrArg (fun K : AdjointableMap D (InteriorModuleTensor (E := X) φ)
          (InteriorModuleTensor (E := X) φ) => Uj.comp K) hS)
  have hdefect : RectangularInteriorModuleTensorOperator.tensor φ
      (R.comp T - Tj.comp S) =
      (interiorModuleTensorOperator φ R).comp U -
        Uj.comp (interiorModuleTensorOperator φ S) :=
    (RectangularInteriorModuleTensorOperator.tensor_sub
      (B := A) (C := D) (E := X) (E' := Y) (F := G) φ (R.comp T) (Tj.comp S)).trans
        (congrArg₂ (fun K L : AdjointableMap D (InteriorModuleTensor (E := X) φ)
          (InteriorModuleTensor (E := Y) φ) => K - L) hRT hTjS)
  exact (comparisonCreation_rectangle_algebra
    (D := D) (X := InteriorModuleTensor (E := X) φ)
    (Y := InteriorModuleTensor (E := Y) φ)
    (interiorModuleTensorOperator φ R) U Uj (interiorModuleTensorOperator φ S) p q).trans
      (congrArg (fun K : AdjointableMap D (InteriorModuleTensor (E := X) φ)
        (InteriorModuleTensor (E := Y) φ) =>
          K.comp p + Uj.comp
            (interiorModuleTensorOperator φ S * p - q * interiorModuleTensorOperator φ S))
        hdefect.symm)

/-- The exact elementary signed defect decomposition retains the actual crossed
coefficient grading σ(d). This proves a relation of real operators, not a
formal expression in unspecified cycle fields. -/
theorem comparisonCreation_signed_defect_mk (x : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    (operatorHom γ (InteriorModuleTensor (E := E) π) R).comp
        (comparisonCreation β γ V π hπ (mk β E x d)) -
      (comparisonCreation β γ V π hπ
        ((moduleGrading β δB hβ J).grading (mk β E x d))).comp (operatorHom γ F S) =
    (RectangularInteriorModuleTensorOperator.tensor (coefficientRepresentation γ)
      (R.comp (moduleCreationMap π x) -
        (moduleCreationMap π (J.grading x)).comp S)).comp
          (reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d)) +
      (RectangularInteriorModuleTensorOperator.tensor (coefficientRepresentation γ)
        (moduleCreationMap π (J.grading x))).comp
          (operatorHom γ F S * reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d) -
            reducedSourceRepresentation γ F β V π hπ
              ((reducedCrossedProductGrading β δB hβ).automorphism (MulOpposite.unop d)) *
                operatorHom γ F S) := by
  have hj : comparisonCreation β γ V π hπ
      ((moduleGrading β δB hβ J).grading (mk β E x d)) =
      (RectangularInteriorModuleTensorOperator.tensor (coefficientRepresentation γ)
        (moduleCreationMap π (J.grading x))).comp
          (reducedSourceRepresentation γ F β V π hπ
            ((reducedCrossedProductGrading β δB hβ).automorphism (MulOpposite.unop d))) :=
    (congrArg (fun ξ : Module β E => comparisonCreation β γ V π hπ ξ)
      (moduleGrading_mk (Γ := Γ) (B := B) (E := E) β δB hβ J x d)).trans
        (comparisonCreation_mk (Γ := Γ) (B := B) (C := C) (E := E) (F := F)
          β γ V π hπ (J.grading x)
          (MulOpposite.op
            ((reducedCrossedProductGrading β δB hβ).automorphism (MulOpposite.unop d))))
  exact (congrArg₂
    (fun K L : AdjointableMap (ReducedCrossedProduct γ) (Module γ F)
      (Module γ (InteriorModuleTensor (E := E) π)) =>
        (operatorHom γ (InteriorModuleTensor (E := E) π) R).comp K -
          L.comp (operatorHom γ F S))
    (comparisonCreation_mk (Γ := Γ) (B := B) (C := C) (E := E) (F := F)
      β γ V π hπ x d) hj).trans
      (comparisonCreation_tensor_algebra
        (A := C) (D := ReducedCrossedProduct γ) (X := F)
        (Y := InteriorModuleTensor (E := E) π) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
        (coefficientRepresentation γ) R (moduleCreationMap π x)
        (moduleCreationMap π (J.grading x)) S
        (reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d))
        (reducedSourceRepresentation γ F β V π hπ
          ((reducedCrossedProductGrading β δB hβ).automorphism (MulOpposite.unop d))))

/-- Compactness of the original whole-vector signed connection defects and
actual crossed graded commutators proves compactness on each elementary
first descended vector, with no homogeneity assumptions on x or d. -/
theorem comparisonCreation_signed_defect_mk_compact
    (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap π x) -
      (moduleCreationMap π (J.grading x)).comp S))
    (hS : ∀ z : ReducedCrossedProduct β,
      IsModuleCompact (operatorHom γ F S * reducedSourceRepresentation γ F β V π hπ z -
        reducedSourceRepresentation γ F β V π hπ
          ((reducedCrossedProductGrading β δB hβ).automorphism z) * operatorHom γ F S))
    (x : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    IsModuleCompact ((operatorHom γ (InteriorModuleTensor (E := E) π) R).comp
        (comparisonCreation β γ V π hπ (mk β E x d)) -
      (comparisonCreation β γ V π hπ
        ((moduleGrading β δB hβ J).grading (mk β E x d))).comp (operatorHom γ F S)) := by
  rw [comparisonCreation_signed_defect_mk]
  exact (((hR x).rectangularInteriorModuleTensor (coefficientRepresentation γ)
    (coefficientRepresentation_compact γ)).comp_right _).add
      ((hS (MulOpposite.unop d)).comp_left _)

/-- Genuine closed-preimage density extends the signed compact defect to
all completed first vectors. Thus homogeneous vectors need no separate,
unjustified elementary-density claim. -/
theorem comparisonCreation_signed_defect_compact
    (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap π x) -
      (moduleCreationMap π (J.grading x)).comp S))
    (hS : ∀ z : ReducedCrossedProduct β,
      IsModuleCompact (operatorHom γ F S * reducedSourceRepresentation γ F β V π hπ z -
        reducedSourceRepresentation γ F β V π hπ
          ((reducedCrossedProductGrading β δB hβ).automorphism z) * operatorHom γ F S))
    (ξ : Module β E) :
    IsModuleCompact ((operatorHom γ (InteriorModuleTensor (E := E) π) R).comp
        (comparisonCreation β γ V π hπ ξ) -
      (comparisonCreation β γ V π hπ ((moduleGrading β δB hβ J).grading ξ)).comp
        (operatorHom γ F S)) := by
  let K := (AdjointableMap.compLeftContinuousLinearMap
    (tensorComparison (E := E) β γ V π hπ).toAdjointable).comp
      (moduleCreationContinuousLinearMap (E := Module β E)
        (reducedSourceRepresentation γ F β V π hπ))
  let L := (AdjointableMap.compLeftContinuousLinearMap
      (operatorHom γ (InteriorModuleTensor (E := E) π) R)).comp K -
    (AdjointableMap.compRightContinuousLinearMap (operatorHom γ F S)).comp
      (K.comp (moduleGrading β δB hβ J).grading.toContinuousLinearEquiv.toContinuousLinearMap)
  let P := (moduleCompact (ReducedCrossedProduct γ) (Module γ F)
    (Module γ (InteriorModuleTensor (E := E) π))).comap L.toLinearMap
  have hP : IsClosed (P : Set (Module β E)) := moduleCompact_isClosed.preimage L.continuous
  have hspan : Submodule.span ℂ
      (Set.range fun p : E × (ReducedCrossedProduct β)ᵐᵒᵖ => mk β E p.1 p.2) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,d⟩,rfl⟩
    exact comparisonCreation_signed_defect_mk_compact β γ V π hπ hβ J S R hR hS x d
  exact closure_minimal hspan hP (interiorModuleTensor_span_dense (coefficientRepresentation β) ξ)

/-- Transporting the compact signed defect back by the actual unitary proves
the full signed connection law on the actual crossed interior tensor. -/
theorem descended_signed_connection_compact
    (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap π x) -
      (moduleCreationMap π (J.grading x)).comp S))
    (hS : ∀ z : ReducedCrossedProduct β,
      IsModuleCompact (operatorHom γ F S * reducedSourceRepresentation γ F β V π hπ z -
        reducedSourceRepresentation γ F β V π hπ
          ((reducedCrossedProductGrading β δB hβ).automorphism z) * operatorHom γ F S))
    (ξ : Module β E) :
    IsModuleCompact ((descendedConnectionOperator β γ V π hπ R).comp
        (moduleCreationMap (reducedSourceRepresentation γ F β V π hπ) ξ) -
      (moduleCreationMap (reducedSourceRepresentation γ F β V π hπ)
        ((moduleGrading β δB hβ J).grading ξ)).comp (operatorHom γ F S)) := by
  have h := (comparisonCreation_signed_defect_compact β γ V π hπ hβ J S R hR hS ξ).comp_left
    (tensorComparison (E := E) β γ V π hπ).symm.toAdjointable
  convert h using 1
  apply AdjointableMap.ext
  intro y
  simp only [descendedConnectionOperator, comparisonCreation,
    HilbertModuleEquiv.transport_apply, AdjointableMap.comp_apply,
    AdjointableMap.coe_sub_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.map_sub, HilbertModuleEquiv.symm_symm,
    HilbertModuleEquiv.symm_apply_apply]

section WholeCycles

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Countable Γ] [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  {δA : CStarGrading A} {δC : CStarGrading C}
  (α : CStarAlgebraAction Γ A)
  (c : GradedKasparovCycle α β δA δB E)
  (d : GradedKasparovCycle β γ δB δC F)
  (R₀ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))

/-- All four genuine homogeneous connection laws descend. The proof first
establishes both all-vector signed laws, using the actual descended second
cycle commutator, and only then specializes to even and odd vectors.
No product, positivity, selfadjointness or nondegeneracy is assumed. -/
theorem descended_gradedConnection (hR₀ : GradedKasparovConnection c d R₀) :
    GradedKasparovConnection (gradedCycle β α c) (gradedCycle γ β d)
      (descendedConnectionOperator β γ d.groupAction d.representation
        d.representation_equivariant R₀) := by
  let ρ : ReducedCrossedProduct β →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) :=
    reducedSourceRepresentation γ F β d.groupAction d.representation d.representation_equivariant
  let J₁ : GradedHilbertModule
      (reducedCrossedProductGrading β δB c.coefficientAction_preservesGrading) (Module β E) :=
    moduleGrading β δB c.coefficientAction_preservesGrading c.grading
  let S₁ : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) :=
    operatorHom γ F d.operator
  let R₁ : AdjointableMap (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E) ρ)
      (InteriorModuleTensor (E := Module β E) ρ) :=
    descendedConnectionOperator β γ d.groupAction d.representation
      d.representation_equivariant R₀
  have hcomm (z : ReducedCrossedProduct β) :
      IsModuleCompact (operatorHom γ F d.operator * ρ z -
        ρ ((reducedCrossedProductGrading β δB c.coefficientAction_preservesGrading).automorphism z) *
          operatorHom γ F d.operator) :=
    graded_reduced_commutator_compact γ β d z
  have hdef (ξ : Module β E) :
      IsModuleCompact (R₁.comp (moduleCreationMap ρ ξ) -
        (moduleCreationMap ρ (J₁.grading ξ)).comp S₁) :=
    descended_signed_connection_compact β γ d.groupAction d.representation
      d.representation_equivariant c.coefficientAction_preservesGrading c.grading
      d.operator R₀ hR₀.creation_defect hcomm ξ
  have hcommAdj (z : ReducedCrossedProduct β) :
      IsModuleCompact (operatorHom γ F (star d.operator) * ρ z -
        ρ ((reducedCrossedProductGrading β δB c.coefficientAction_preservesGrading).automorphism z) *
          operatorHom γ F (star d.operator)) := by
    have hadj : (operatorHom γ F d.operator).adjoint =
        operatorHom γ F (star d.operator) :=
      (operatorHom_adjoint γ F d.operator).trans
        (congrArg (fun T : AdjointableMap C F F => operatorHom γ F T)
          (AdjointableMap.star_eq_adjoint d.operator).symm)
    have hnative := graded_coefficient_commutator_adjoint_compact
      (B := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ) (F := Module γ F)
      (δB := reducedCrossedProductGrading β δB c.coefficientAction_preservesGrading)
      ρ (operatorHom γ F d.operator) hcomm z
    exact Eq.mp
      (congrArg
        (fun Q : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) =>
          IsModuleCompact (Q * ρ z -
            ρ ((reducedCrossedProductGrading β δB c.coefficientAction_preservesGrading).automorphism z) * Q))
        hadj) hnative
  have hdefAdj (ξ : Module β E) :
      IsModuleCompact ((star R₁).comp (moduleCreationMap ρ ξ) -
        (moduleCreationMap ρ (J₁.grading ξ)).comp (star S₁)) := by
    have hnative : IsModuleCompact
        ((descendedConnectionOperator β γ d.groupAction d.representation
            d.representation_equivariant (star R₀)).comp (moduleCreationMap ρ ξ) -
          (moduleCreationMap ρ (J₁.grading ξ)).comp (operatorHom γ F (star d.operator))) :=
      descended_signed_connection_compact β γ d.groupAction d.representation
        d.representation_equivariant c.coefficientAction_preservesGrading c.grading
        (star d.operator) (star R₀) hR₀.creation_adjoint_defect hcommAdj ξ
    have hRstar : descendedConnectionOperator β γ d.groupAction d.representation
        d.representation_equivariant (star R₀) = star R₁ :=
      descendedConnectionOperator_star β γ d.groupAction d.representation
        d.representation_equivariant R₀
    have hSstar : operatorHom γ F (star d.operator) = star S₁ :=
      map_star (operatorHom γ F) d.operator
    have heq := congrArg₂
      (fun (Q : AdjointableMap (ReducedCrossedProduct γ)
          (InteriorModuleTensor (E := Module β E) ρ)
          (InteriorModuleTensor (E := Module β E) ρ))
        (P : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F)) =>
        Q.comp (moduleCreationMap ρ ξ) - (moduleCreationMap ρ (J₁.grading ξ)).comp P)
      hRstar hSstar
    exact Eq.mp
      (congrArg
        (fun T : AdjointableMap (ReducedCrossedProduct γ) (Module γ F)
          (InteriorModuleTensor (E := Module β E) ρ) => IsModuleCompact T) heq) hnative
  exact gradedConnection_of_two_signed_creation_defects
    (gradedCycle β α c) (gradedCycle γ β d) R₁ hdef hdefAdj

end WholeCycles

end BC4lean.KKTheory.KasparovDescent
