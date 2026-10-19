import BC4lean.KasparovDescentReducedRepresentation
import BC4lean.InteriorModuleTensorScalarExtension
import BC4lean.RectangularInteriorModuleTensorOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual crossed interior-tensor comparison unitary

The construction uses the concrete
`KasparovDescentReducedRepresentation` and generic scalar-extension helper.


For an arbitrary equivariant, possibly degenerate π : B → L_C(F), this
constructs the entire coefficient-form unitary
  D(E) tensor_(B crossed Γ) D(F) ≃ D(E tensor_B F).
It is the generic composition of coefficient extension followed by the inverse
of the genuine completed associator. In the generic step the standard pairing
map is only an embedding; onto-ness of the outer comparison uses the intrinsic
coefficient approximate unit on E, never nondegeneracy of π.

Its generator formula is the genuine one, with λ_g a left regular multiplier:
  ((x tensor (b δ_g)) tensor (y tensor c))
      ↦ (x tensor π(b) U_g(y)) tensor λ_g(c).
This is a Hilbert-module comparison, not a claimed Kasparov product theorem.
Connection conditions, grading compatibility and quadratic Calkin positivity
must each be checked separately before such a theorem can be stated.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent InnerProductSpace

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

/-- The original coefficient inclusion is exactly the actual algebraic
single at the group identity, as elements of the concrete reduced algebra. -/
theorem tensorComparison_coefficient_eq_single (b : B) :
    coefficientToReducedCrossed β b =
      algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β 1 b) := by
  apply Subtype.ext
  simp only [coefficientToReducedCrossed_coe, algebraicToReducedCrossed_single,
    reducedCrossedGenerator, reducedCrossedRegular_one, mul_one]

/-- Actual finite integration at the identity gives the precise coefficient
compatibility required by scalar-extension composition. -/
theorem tensorComparison_source_coefficient (b : B) :
    reducedSourceRepresentation γ F β V π hπ (coefficientToReducedCrossed β b) =
      InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ) b := by
  have hsource :
      reducedSourceRepresentation γ F β V π hπ (coefficientToReducedCrossed β b) =
        sourceRepresentation γ F π b :=
    reducedSourceRepresentation_coefficient γ F β V π hπ b
  have hright : sourceRepresentation γ F π b =
      InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ) b :=
    rfl
  exact hsource.trans hright

@[instance_reducible] private def tensorCanonicalFirstNormedAddCommGroup
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    NormedAddCommGroup (InteriorModuleTensor (E := E) r) :=
  inferInstance

@[instance_reducible] private def tensorCanonicalFirstNormedSpace
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    NormedSpace ℂ (InteriorModuleTensor (E := E) r) :=
  inferInstance

@[instance_reducible] private def tensorCanonicalFirstSMul
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    SMul Dᵐᵒᵖ (InteriorModuleTensor (E := E) r) :=
  inferInstance

@[instance_reducible] private def tensorCanonicalFirstCStarModule
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    CStarModule Dᵐᵒᵖ (InteriorModuleTensor (E := E) r) :=
  inferInstance

private theorem tensorCanonicalFirstCompleteSpace
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    CompleteSpace (InteriorModuleTensor (E := E) r) :=
  inferInstance

private def tensorCoefficientExtensionEquiv_of_representation_eq
    {D H : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
    [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (i : B →⋆ₙₐ[ℂ] D)
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ)
    (hr : r = InteriorModuleTensorScalarExtension.standardRepresentation i)
    (M : Type _) (hM : M = InteriorModuleTensor (E := E) r)
    (nM : NormedAddCommGroup M)
    (hnM : HEq nM (tensorCanonicalFirstNormedAddCommGroup (E := E) r))
    (vM : letI : NormedAddCommGroup M := nM; NormedSpace ℂ M)
    (hvM : HEq vM (tensorCanonicalFirstNormedSpace (E := E) r))
    (sM : SMul Dᵐᵒᵖ M)
    (hsM : HEq sM (tensorCanonicalFirstSMul (E := E) r))
    (mM : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      CStarModule Dᵐᵒᵖ M)
    (hmM : HEq mM (tensorCanonicalFirstCStarModule (E := E) r))
    (qM : letI : NormedAddCommGroup M := nM; CompleteSpace M)
    (hqM : HEq qM (tensorCanonicalFirstCompleteSpace (E := E) r))
    (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (hρ : ∀ b, ρ (i b) = ψ b) :
    letI : NormedAddCommGroup M := nM;
    letI : NormedSpace ℂ M := vM;
    letI : SMul Dᵐᵒᵖ M := sM;
    letI : CStarModule Dᵐᵒᵖ M := mM;
    letI : CompleteSpace M := qM;
    HilbertModuleEquiv C
      (InteriorModuleTensor (E := M) ρ)
      (InteriorModuleTensor (E := E) ψ) := by
  subst M
  have hnM' : nM = tensorCanonicalFirstNormedAddCommGroup (E := E) r := eq_of_heq hnM
  subst nM
  have hvM' : vM = tensorCanonicalFirstNormedSpace (E := E) r := eq_of_heq hvM
  subst vM
  have hsM' : sM = tensorCanonicalFirstSMul (E := E) r := eq_of_heq hsM
  subst sM
  have hmM' : mM = tensorCanonicalFirstCStarModule (E := E) r := eq_of_heq hmM
  subst mM
  have hqM' : qM = tensorCanonicalFirstCompleteSpace (E := E) r := eq_of_heq hqM
  subst qM
  subst r
  exact InteriorModuleTensorScalarExtension.hilbertEquiv
    (B := B) (D := D) (C := C) (E := E) (H := H) i ρ ψ hρ

private theorem tensorCoefficientExtensionEquiv_of_representation_eq_triple
    {D H : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
    [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (i : B →⋆ₙₐ[ℂ] D)
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ)
    (hr : r = InteriorModuleTensorScalarExtension.standardRepresentation i)
    (M : Type _) (hM : M = InteriorModuleTensor (E := E) r)
    (nM : NormedAddCommGroup M)
    (hnM : HEq nM (tensorCanonicalFirstNormedAddCommGroup (E := E) r))
    (vM : letI : NormedAddCommGroup M := nM; NormedSpace ℂ M)
    (hvM : HEq vM (tensorCanonicalFirstNormedSpace (E := E) r))
    (sM : SMul Dᵐᵒᵖ M)
    (hsM : HEq sM (tensorCanonicalFirstSMul (E := E) r))
    (mM : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      CStarModule Dᵐᵒᵖ M)
    (hmM : HEq mM (tensorCanonicalFirstCStarModule (E := E) r))
    (qM : letI : NormedAddCommGroup M := nM; CompleteSpace M)
    (hqM : HEq qM (tensorCanonicalFirstCompleteSpace (E := E) r))
    (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (hρ : ∀ b, ρ (i b) = ψ b)
    (x : E) (d : Dᵐᵒᵖ) (y : H) (u : M)
    (hu : HEq u (interiorModuleTensorMk (E := E) r x d)) :
    letI : NormedAddCommGroup M := nM;
    letI : NormedSpace ℂ M := vM;
    letI : SMul Dᵐᵒᵖ M := sM;
    letI : CStarModule Dᵐᵒᵖ M := mM;
    letI : CompleteSpace M := qM;
    tensorCoefficientExtensionEquiv_of_representation_eq
        (B := B) (D := D) (C := C) (E := E) (H := H)
        i r hr M hM nM hnM vM hvM sM hsM mM hmM qM hqM ρ ψ hρ
        (interiorModuleTensorMk (E := M) ρ u y) =
      interiorModuleTensorMk (E := E) ψ x (ρ (MulOpposite.unop d) y) := by
  subst M
  have hnM' : nM = tensorCanonicalFirstNormedAddCommGroup (E := E) r := eq_of_heq hnM
  subst nM
  have hvM' : vM = tensorCanonicalFirstNormedSpace (E := E) r := eq_of_heq hvM
  subst vM
  have hsM' : sM = tensorCanonicalFirstSMul (E := E) r := eq_of_heq hsM
  subst sM
  have hmM' : mM = tensorCanonicalFirstCStarModule (E := E) r := eq_of_heq hmM
  subst mM
  have hqM' : qM = tensorCanonicalFirstCompleteSpace (E := E) r := eq_of_heq hqM
  subst qM
  subst r
  have hu' : u = interiorModuleTensorMk (E := E)
      (InteriorModuleTensorScalarExtension.standardRepresentation i) x d := eq_of_heq hu
  subst u
  exact InteriorModuleTensorScalarExtension.hilbertEquiv_triple
    (B := B) (D := D) (C := C) (E := E) (H := H) i ρ ψ hρ x d y

private theorem tensorCoefficientExtensionEquiv_of_representation_eq_operator
    {D H : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
    [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (i : B →⋆ₙₐ[ℂ] D)
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ)
    (hr : r = InteriorModuleTensorScalarExtension.standardRepresentation i)
    (M : Type _) (hM : M = InteriorModuleTensor (E := E) r)
    (nM : NormedAddCommGroup M)
    (hnM : HEq nM (tensorCanonicalFirstNormedAddCommGroup (E := E) r))
    (vM : letI : NormedAddCommGroup M := nM; NormedSpace ℂ M)
    (hvM : HEq vM (tensorCanonicalFirstNormedSpace (E := E) r))
    (sM : SMul Dᵐᵒᵖ M)
    (hsM : HEq sM (tensorCanonicalFirstSMul (E := E) r))
    (mM : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      CStarModule Dᵐᵒᵖ M)
    (hmM : HEq mM (tensorCanonicalFirstCStarModule (E := E) r))
    (qM : letI : NormedAddCommGroup M := nM; CompleteSpace M)
    (hqM : HEq qM (tensorCanonicalFirstCompleteSpace (E := E) r))
    (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (hρ : ∀ b, ρ (i b) = ψ b)
    (T : AdjointableMap B E E)
    (S : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      letI : CStarModule Dᵐᵒᵖ M := mM;
      letI : CompleteSpace M := qM;
      AdjointableMap D M M)
    (hS : HEq S (interiorModuleTensorOperator (E := E) r T))
    (u : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      letI : CStarModule Dᵐᵒᵖ M := mM;
      letI : CompleteSpace M := qM;
      InteriorModuleTensor (E := M) ρ) :
    letI : NormedAddCommGroup M := nM;
    letI : NormedSpace ℂ M := vM;
    letI : SMul Dᵐᵒᵖ M := sM;
    letI : CStarModule Dᵐᵒᵖ M := mM;
    letI : CompleteSpace M := qM;
    tensorCoefficientExtensionEquiv_of_representation_eq
        (B := B) (D := D) (C := C) (E := E) (H := H)
        i r hr M hM nM hnM vM hvM sM hsM mM hmM qM hqM ρ ψ hρ
        (interiorModuleTensorOperator (E := M) ρ S u) =
      interiorModuleTensorOperator (E := E) ψ T
        (tensorCoefficientExtensionEquiv_of_representation_eq
        (B := B) (D := D) (C := C) (E := E) (H := H)
        i r hr M hM nM hnM vM hvM sM hsM mM hmM qM hqM ρ ψ hρ u) := by
  subst M
  have hnM' : nM = tensorCanonicalFirstNormedAddCommGroup (E := E) r := eq_of_heq hnM
  subst nM
  have hvM' : vM = tensorCanonicalFirstNormedSpace (E := E) r := eq_of_heq hvM
  subst vM
  have hsM' : sM = tensorCanonicalFirstSMul (E := E) r := eq_of_heq hsM
  subst sM
  have hmM' : mM = tensorCanonicalFirstCStarModule (E := E) r := eq_of_heq hmM
  subst mM
  have hqM' : qM = tensorCanonicalFirstCompleteSpace (E := E) r := eq_of_heq hqM
  subst qM
  subst r
  have hS' : S = interiorModuleTensorOperator (E := E)
      (InteriorModuleTensorScalarExtension.standardRepresentation i) T := eq_of_heq hS
  subst S
  exact InteriorModuleTensorScalarExtension.hilbertEquiv_operator
    (B := B) (D := D) (C := C) (E := E) (H := H) i ρ ψ hρ T u

/-- First compose the two actual coefficient extensions. The target already
uses the actual amplified B-representation on D(F). -/
def tensorCoefficientExtensionEquiv :
    HilbertModuleEquiv (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E)
        (reducedSourceRepresentation γ F β V π hπ))
      (InteriorModuleTensor (E := E)
        (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ))) :=
  tensorCoefficientExtensionEquiv_of_representation_eq
    (B := B) (D := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
    (E := E) (H := InteriorModuleTensor (E := F) (coefficientRepresentation γ))
    (coefficientToReducedCrossed β) (coefficientRepresentation β) rfl
    (Module β E) rfl
    (inferInstance : NormedAddCommGroup (Module β E)) HEq.rfl
    (inferInstance : NormedSpace ℂ (Module β E)) HEq.rfl
    (inferInstance : SMul (ReducedCrossedProduct β)ᵐᵒᵖ (Module β E)) HEq.rfl
    (inferInstance : CStarModule (ReducedCrossedProduct β)ᵐᵒᵖ (Module β E)) HEq.rfl
    (inferInstance : CompleteSpace (Module β E)) HEq.rfl
    (reducedSourceRepresentation γ F β V π hπ)
    (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ))
    (tensorComparison_source_coefficient β γ V π hπ)

/-- The genuine whole-module crossed tensor comparison, including the
possibly degenerate second representation. -/
def tensorComparison : HilbertModuleEquiv (ReducedCrossedProduct γ)
    (InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β V π hπ))
    (Module γ (InteriorModuleTensor (E := E) π)) :=
  (tensorCoefficientExtensionEquiv (E := E) β γ V π hπ).trans
    (InteriorModuleTensorAssociator.hilbertEquiv (E := E) π (coefficientRepresentation γ)).symm

/-- A formula valid for every crossed coefficient, not only finite sums. -/
theorem tensorComparison_mk (x : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ)
    (z : Module γ F) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorMk (reducedSourceRepresentation γ F β V π hπ)
        (mk β E x d) z) =
      (InteriorModuleTensorAssociator.hilbertEquiv (E := E) π
        (coefficientRepresentation γ)).symm
          (interiorModuleTensorMk
            (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ)) x
              (reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d) z)) := by
  have hpure :
      tensorCoefficientExtensionEquiv (E := E) β γ V π hπ
          (interiorModuleTensorMk (reducedSourceRepresentation γ F β V π hπ)
            (mk β E x d) z) =
        interiorModuleTensorMk
          (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ)) x
          (reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d) z) :=
    tensorCoefficientExtensionEquiv_of_representation_eq_triple
      (B := B) (D := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
      (E := E) (H := InteriorModuleTensor (E := F) (coefficientRepresentation γ))
      (coefficientToReducedCrossed β) (coefficientRepresentation β) rfl
      (Module β E) rfl
      (inferInstance : NormedAddCommGroup (Module β E)) HEq.rfl
      (inferInstance : NormedSpace ℂ (Module β E)) HEq.rfl
      (inferInstance : SMul (ReducedCrossedProduct β)ᵐᵒᵖ (Module β E)) HEq.rfl
      (inferInstance : CStarModule (ReducedCrossedProduct β)ᵐᵒᵖ (Module β E)) HEq.rfl
      (inferInstance : CompleteSpace (Module β E)) HEq.rfl
      (reducedSourceRepresentation γ F β V π hπ)
      (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ))
      (tensorComparison_source_coefficient β γ V π hπ) x d z
      (mk β E x d) HEq.rfl
  exact congrArg
    (fun w : InteriorModuleTensor (E := E)
      (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ)) =>
      (InteriorModuleTensorAssociator.hilbertEquiv
        (B := B) (C := C) (D := ReducedCrossedProduct γ)
        (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
        π (coefficientRepresentation γ)).symm w) hpure

/-- The precise crossed-generator formula, with the actual multiplier acting
on c. No group unitary is falsely treated as an element of a nonunital algebra. -/
@[simp] theorem tensorComparison_single (x : E) (b : B) (g : Γ) (y : F)
    (c : (ReducedCrossedProduct γ)ᵐᵒᵖ) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorMk (reducedSourceRepresentation γ F β V π hπ)
        (mk β E x (MulOpposite.op
          (algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β g b))))
        (mk γ F y c)) =
      mk γ (InteriorModuleTensor (E := E) π)
        (interiorModuleTensorMk π x (π b (V.action g y)))
        (MulOpposite.op (leftRegular γ g (MulOpposite.unop c))) := by
  have hsingle := congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct γ) (Module γ F) (Module γ F) =>
      T (mk γ F y c))
    (reducedSourceRepresentation_single γ F β V π hπ g b)
  have haction := hsingle.trans (sourceGenerator_mk γ F V π b g y c)
  have hmiddle := congrArg
    (fun w : Module γ F =>
      (InteriorModuleTensorAssociator.hilbertEquiv
        (B := B) (C := C) (D := ReducedCrossedProduct γ)
        (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
        π (coefficientRepresentation γ)).symm
          (interiorModuleTensorMk
            (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ))
            x w)) haction
  have hfirst := tensorComparison_mk (Γ := Γ) (B := B) (C := C) (E := E) (F := F)
    β γ V π hπ x
    (MulOpposite.op (algebraicToReducedCrossed β (AlgebraicCrossedProduct.single β g b)))
    (mk γ F y c)
  have hlast := InteriorModuleTensorAssociator.hilbertEquiv_symm_triple
    (B := B) (C := C) (D := ReducedCrossedProduct γ)
    (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
    π (coefficientRepresentation γ) x (π b (V.action g y))
      (MulOpposite.op (leftRegular γ g (MulOpposite.unop c)))
  exact hfirst.trans (hmiddle.trans hlast)

/-- The full coefficient pairing is preserved on arbitrary whole vectors. -/
theorem tensorComparison_inner
    (u v : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β V π hπ)) :
    ⟪tensorComparison β γ V π hπ u, tensorComparison β γ V π hπ v⟫_((ReducedCrossedProduct γ)ᵐᵒᵖ) =
      ⟪u, v⟫_((ReducedCrossedProduct γ)ᵐᵒᵖ) :=
  (tensorComparison β γ V π hπ).inner_map u v

private theorem tensorComparison_associator_operator_aux
    {D G : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G]
    [CStarModule Dᵐᵒᵖ G] [CompleteSpace G]
    (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)
    (T : AdjointableMap B E E)
    (v : InteriorModuleTensorAssociator.RightTensor (E := E) π ψ) :
    (InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) π ψ).symm
      (interiorModuleTensorOperator (InteriorModuleTensorAssociator.rightRepresentation π ψ) T v) =
      interiorModuleTensorOperator ψ (interiorModuleTensorOperator π T)
        ((InteriorModuleTensorAssociator.hilbertEquiv
          (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) π ψ).symm v) := by
  let W : HilbertModuleEquiv D
      (InteriorModuleTensorAssociator.LeftTensor (E := E) π ψ)
      (InteriorModuleTensorAssociator.RightTensor (E := E) π ψ) :=
    InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) π ψ
  let L : AdjointableMap D
      (InteriorModuleTensorAssociator.LeftTensor (E := E) π ψ)
      (InteriorModuleTensorAssociator.LeftTensor (E := E) π ψ) :=
    interiorModuleTensorOperator ψ (interiorModuleTensorOperator π T)
  let R : AdjointableMap D
      (InteriorModuleTensorAssociator.RightTensor (E := E) π ψ)
      (InteriorModuleTensorAssociator.RightTensor (E := E) π ψ) :=
    interiorModuleTensorOperator (InteriorModuleTensorAssociator.rightRepresentation π ψ) T
  have h₀ := InteriorModuleTensorAssociator.hilbertEquiv_operator_intertwine
    (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) π ψ T (W.symm v)
  have h₁ : W (L (W.symm v)) = R v :=
    h₀.trans (congrArg
      (fun w : InteriorModuleTensorAssociator.RightTensor (E := E) π ψ => R w)
      (W.apply_symm_apply v))
  exact (congrArg
    (fun w : InteriorModuleTensorAssociator.RightTensor (E := E) π ψ => W.symm w)
    h₁).symm.trans (W.symm_apply_apply (L (W.symm v)))

private theorem tensorCoefficientExtensionEquiv_operator_aux
    (T : AdjointableMap B E E) :
    ∀ u : InteriorModuleTensor (E := Module β E)
        (reducedSourceRepresentation γ F β V π hπ),
      tensorCoefficientExtensionEquiv (E := E) β γ V π hπ
          (interiorModuleTensorOperator (reducedSourceRepresentation γ F β V π hπ)
            (operatorHom β E T) u) =
        interiorModuleTensorOperator
          (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ)) T
          (tensorCoefficientExtensionEquiv (E := E) β γ V π hπ u) := by
  intro u
  exact tensorCoefficientExtensionEquiv_of_representation_eq_operator
      (B := B) (D := ReducedCrossedProduct β) (C := ReducedCrossedProduct γ)
      (E := E) (H := InteriorModuleTensor (E := F) (coefficientRepresentation γ))
      (coefficientToReducedCrossed β) (coefficientRepresentation β) rfl
      (Module β E) rfl
      (inferInstance : NormedAddCommGroup (Module β E)) HEq.rfl
      (inferInstance : NormedSpace ℂ (Module β E)) HEq.rfl
      (inferInstance : SMul (ReducedCrossedProduct β)ᵐᵒᵖ (Module β E)) HEq.rfl
      (inferInstance : CStarModule (ReducedCrossedProduct β)ᵐᵒᵖ (Module β E)) HEq.rfl
      (inferInstance : CompleteSpace (Module β E)) HEq.rfl
      (reducedSourceRepresentation γ F β V π hπ)
      (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ))
      (tensorComparison_source_coefficient β γ V π hπ) T
      (operatorHom β E T) HEq.rfl u

/-- The comparison intertwines actual first-factor operator amplification,
the operator input needed separately in product positivity. -/
theorem tensorComparison_operator (T : AdjointableMap B E E)
    (u : InteriorModuleTensor (E := Module β E)
      (reducedSourceRepresentation γ F β V π hπ)) :
    tensorComparison β γ V π hπ
      (interiorModuleTensorOperator (reducedSourceRepresentation γ F β V π hπ)
        (operatorHom β E T) u) =
      operatorHom γ (InteriorModuleTensor (E := E) π)
        (interiorModuleTensorOperator π T) (tensorComparison β γ V π hπ u) := by
  let W : HilbertModuleEquiv (ReducedCrossedProduct γ)
      (Module γ (InteriorModuleTensor (E := E) π))
      (InteriorModuleTensorAssociator.RightTensor (E := E) π (coefficientRepresentation γ)) :=
    InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := ReducedCrossedProduct γ)
      (E := E) (F := F) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ) π (coefficientRepresentation γ)
  let X : HilbertModuleEquiv (ReducedCrossedProduct γ)
      (InteriorModuleTensor (E := Module β E) (reducedSourceRepresentation γ F β V π hπ))
      (InteriorModuleTensorAssociator.RightTensor (E := E) π (coefficientRepresentation γ)) :=
    tensorCoefficientExtensionEquiv (E := E) β γ V π hπ
  have hScalar := tensorCoefficientExtensionEquiv_operator_aux
    (E := E) β γ V π hπ T u
  exact (congrArg
    (fun w : InteriorModuleTensorAssociator.RightTensor
      (E := E) π (coefficientRepresentation γ) => W.symm w) hScalar).trans
      (tensorComparison_associator_operator_aux
        (B := B) (C := C) (E := E) (F := F)
        (D := ReducedCrossedProduct γ) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
        π (coefficientRepresentation γ) T (X u))

private theorem tensorComparison_associator_creation_clm_aux
    {D G : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G]
    [CStarModule Dᵐᵒᵖ G] [CompleteSpace G]
    (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)
    (x : E) :
    (((InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) π ψ).symm.toAdjointable).toCLM).comp
      (moduleCreationMap (B := B) (C := D) (E := E)
        (F := InteriorModuleTensor (E := F) ψ)
        (InteriorModuleTensorAssociator.rightRepresentation π ψ) x).toCLM =
      (RectangularInteriorModuleTensorOperator.tensor
        (B := C) (C := D) (E := F) (E' := InteriorModuleTensor (E := E) π) (F := G) ψ
        (moduleCreationMap (B := B) (C := C) (E := E) (F := F) π x)).toCLM := by
  let W : HilbertModuleEquiv D
      (InteriorModuleTensorAssociator.LeftTensor (E := E) π ψ)
      (InteriorModuleTensorAssociator.RightTensor (E := E) π ψ) :=
    InteriorModuleTensorAssociator.hilbertEquiv
      (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) π ψ
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    (B := C) (C := D) (E := F) (F := G)
    (P := InteriorModuleTensorAssociator.LeftTensor (E := E) π ψ) (φ := ψ)
  intro y c
  have hOuter := congrArg
    (fun v : InteriorModuleTensorAssociator.RightTensor (E := E) π ψ => W.symm v)
    (moduleCreationMap_apply (B := B) (C := D) (E := E)
      (F := InteriorModuleTensor (E := F) ψ)
      (InteriorModuleTensorAssociator.rightRepresentation π ψ) x
      (interiorModuleTensorMk (B := C) (C := D) (E := F) (F := G) ψ y c))
  have hTriple := InteriorModuleTensorAssociator.hilbertEquiv_symm_triple
    (B := B) (C := C) (D := D) (E := E) (F := F) (G := G) π ψ x y c
  have hCreation := congrArg
    (fun v : InteriorModuleTensor (E := E) π =>
      interiorModuleTensorMk (B := C) (C := D)
        (E := InteriorModuleTensor (E := E) π) (F := G) ψ v c)
    (moduleCreationMap_apply (B := B) (C := C) (E := E) (F := F) π x y)
  have hTensor := RectangularInteriorModuleTensorOperator.tensor_mk
    (B := C) (C := D) (E := F) (E' := InteriorModuleTensor (E := E) π) (F := G) ψ
    (moduleCreationMap (B := B) (C := C) (E := E) (F := F) π x) y c
  exact hOuter.trans (hTriple.trans (hCreation.symm.trans hTensor.symm))

/-- The inverse associator applied after pure creation is exactly the actual
rectangular coefficient amplification of the original creation operator. -/
theorem tensorComparison_associator_creation (x : E) :
    ((InteriorModuleTensorAssociator.hilbertEquiv (E := E) π
      (coefficientRepresentation γ)).symm.toAdjointable).comp
        (moduleCreationMap
          (InteriorModuleTensorAssociator.rightRepresentation π (coefficientRepresentation γ)) x) =
      RectangularInteriorModuleTensorOperator.tensor (coefficientRepresentation γ)
        (moduleCreationMap π x) := by
  exact (AdjointableMap.toCLM_injective
    (B := ReducedCrossedProduct γ) (E := Module γ F)
    (F := Module γ (InteriorModuleTensor (E := E) π)))
    (tensorComparison_associator_creation_clm_aux
      (B := B) (C := C) (E := E) (F := F)
      (D := ReducedCrossedProduct γ) (G := (ReducedCrossedProduct γ)ᵐᵒᵖ)
      π (coefficientRepresentation γ) x)

/-- Whole-vector creation intertwining on an elementary first descended vector.
This identity is an input to later connection-defect proofs; it does not assert
that those defects are compact. -/
theorem tensorComparison_creation (x : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    (tensorComparison (E := E) β γ V π hπ).toAdjointable.comp
      (moduleCreationMap (reducedSourceRepresentation γ F β V π hπ) (mk β E x d)) =
    (RectangularInteriorModuleTensorOperator.tensor (coefficientRepresentation γ)
      (moduleCreationMap π x)).comp
        (reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d)) := by
  apply AdjointableMap.ext
  intro z
  exact (tensorComparison_mk
    (Γ := Γ) (B := B) (C := C) (E := E) (F := F) β γ V π hπ x d z).trans
      (congrArg
        (fun T : AdjointableMap (ReducedCrossedProduct γ)
          (Module γ F) (Module γ (InteriorModuleTensor (E := E) π)) =>
            T (reducedSourceRepresentation γ F β V π hπ (MulOpposite.unop d) z))
        (tensorComparison_associator_creation
          (Γ := Γ) (B := B) (C := C) (E := E) (F := F) γ π x))

end BC4lean.KKTheory.KasparovDescent
