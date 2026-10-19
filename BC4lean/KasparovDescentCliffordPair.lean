import BC4lean.ReducedCrossedProductPair
import BC4lean.StandardCoefficientExtensionEquiv
import BC4lean.CliffordPairStandardTensorCompatibility
import BC4lean.KasparovDescentGrading
import BC4lean.KasparovDescentAction
import BC4lean.KasparovDescentReducedRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual completed Clifford coordinate descent unitary



The right-hand coefficient is changed by the constructed actual star
equivalence `(B × B) crossed Γ ≃ (B crossed Γ) × (B crossed Γ)`.
The first constructed unitary changes this standard extension coefficient;
the second is the existing, genuinely onto completed pair tensor unitary.
Their composite has the full actual product-valued inner product.
The original module and all its source representations may be degenerate.
No desired descent isomorphism is among the construction inputs.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped InnerProductSpace KasparovDescent CStarAlgebra

variable {Γ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (β : CStarAlgebraAction Γ B)

theorem pairCoefficientHom_eq :
    StandardCoefficientExtensionEquiv.targetHom
      (coefficientToReducedCrossed (cliffordCoefficientAction β))
      (ReducedCrossedProductPair.equiv β) =
      cliffordCoordinateHom (coefficientToReducedCrossed β) := by
  apply NonUnitalStarAlgHom.ext
  intro b
  exact ReducedCrossedProductPair.equiv_coefficient β b

abbrev PairChangedModule := CoefficientChangedModule (ReducedCrossedProductPair.equiv β)
  (Module (cliffordCoefficientAction β) (CliffordPairModule B E))

/-- The actual change of standard extension coefficient; it has an exact
elementary formula and no nondegeneracy condition. -/
def pairCoefficientExtension : HilbertModuleEquiv
    (ReducedCrossedProduct β × ReducedCrossedProduct β)
    (PairChangedModule (E := E) β)
    (CliffordPairStandardTensor.Source (H := E) (coefficientToReducedCrossed β)) :=
  StandardCoefficientExtensionEquiv.hilbertEquivTo
    (coefficientToReducedCrossed (cliffordCoefficientAction β))
    (ReducedCrossedProductPair.equiv β)
    (cliffordCoordinateHom (coefficientToReducedCrossed β)) (pairCoefficientHom_eq β)

/-- The entire descended Clifford pair is the Clifford pair of the actual
descended original module, after the genuine crossed coefficient change. -/
def pairModuleEquiv : HilbertModuleEquiv
    (ReducedCrossedProduct β × ReducedCrossedProduct β)
    (PairChangedModule (E := E) β)
    (CliffordPairModule (ReducedCrossedProduct β) (Module β E)) :=
  (pairCoefficientExtension (E := E) β).trans
    (CliffordPairStandardTensor.hilbertEquiv (coefficientToReducedCrossed β))

/-- The same actual whole-vector map with its original coefficient carrier. -/
def pairModuleMap : Module (cliffordCoefficientAction β) (CliffordPairModule B E) →ₗᵢ[ℂ]
    CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
  (pairModuleEquiv (E := E) β).linearIsometryEquiv.toLinearIsometry.comp
    (coefficientChangedLinearIsometry (ReducedCrossedProductPair.equiv β)).toLinearIsometry

@[simp] theorem pairModuleMap_mk (x : CliffordPairModule B E)
    (c : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :
    pairModuleMap β (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c) =
      cliffordPairMk
        (mk β E x.1 (MulOpposite.op ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c)).1))
        (mk β E x.2 (MulOpposite.op ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c)).2)) := by
  let f : B →⋆ₙₐ[ℂ] ReducedCrossedProduct β := coefficientToReducedCrossed β
  let e := ReducedCrossedProductPair.equiv β
  let q : PairChangedModule (E := E) β :=
    coefficientChangedLinearIsometry e
      (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c)
  let y : (ReducedCrossedProduct β × ReducedCrossedProduct β)ᵐᵒᵖ :=
    opStarAlgEquivBetween e c
  let V := pairCoefficientExtension (E := E) β
  let W := CliffordPairStandardTensor.hilbertEquiv (H := E) f
  have hV : V q =
      interiorModuleTensorMk (CliffordPairStandardTensor.representation f) x y :=
    StandardCoefficientExtensionEquiv.hilbertEquivTo_mk
      (B := B × B) (D := ReducedCrossedProduct (cliffordCoefficientAction β))
      (C := ReducedCrossedProduct β × ReducedCrossedProduct β)
      (E := CliffordPairModule B E)
      (coefficientToReducedCrossed (cliffordCoefficientAction β)) e
      (cliffordCoordinateHom f) (pairCoefficientHom_eq β) x c
  have hW : W (interiorModuleTensorMk
      (CliffordPairStandardTensor.representation f) x y) =
      CliffordPairStandardTensor.bilinear f x y :=
    CliffordPairStandardTensor.hilbertEquiv_mk (H := E) f x y
  have hmap : pairModuleMap β
      (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c) = W (V q) := rfl
  have hcoords : CliffordPairStandardTensor.bilinear f x y =
      cliffordPairMk
        (mk β E x.1 (MulOpposite.op ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c)).1))
        (mk β E x.2 (MulOpposite.op ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c)).2)) := rfl
  exact hmap.trans ((congrArg
    (fun v : CliffordPairStandardTensor.Source (H := E) f => W v) hV).trans
      (hW.trans hcoords))

/-- The full inner product is carried by the actual crossed algebra equivalence. -/
theorem pairModuleMap_inner
    (z w : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    ⟪pairModuleMap β z, pairModuleMap β w⟫_
        ((ReducedCrossedProduct β × ReducedCrossedProduct β)ᵐᵒᵖ) =
      opStarAlgEquivBetween (ReducedCrossedProductPair.equiv β)
        ⟪z, w⟫_((ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :=
  (pairModuleEquiv (E := E) β).inner_map _ _

/-- The construction is onto the whole pair, without any source-action assumption. -/
theorem pairModuleMap_surjective : Function.Surjective (pairModuleMap (E := E) β) :=
  (pairModuleEquiv (E := E) β).surjective.comp
    (coefficientChangedLinearIsometry (ReducedCrossedProductPair.equiv β)).surjective

theorem pairModuleMap_operator (S T : AdjointableMap B E E)
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      (operatorHom (cliffordCoefficientAction β) (CliffordPairModule B E)
        (cliffordPairMap S T) z) =
      cliffordPairMap (operatorHom β E S) (operatorHom β E T) (pairModuleMap β z) := by
  have h₁ := StandardCoefficientExtensionEquiv.hilbertEquivTo_operator
    (E := CliffordPairModule B E)
    (coefficientToReducedCrossed (cliffordCoefficientAction β))
    (ReducedCrossedProductPair.equiv β)
    (cliffordCoordinateHom (coefficientToReducedCrossed β)) (pairCoefficientHom_eq β)
    (cliffordPairMap S T)
    (coefficientChangedLinearIsometry (ReducedCrossedProductPair.equiv β) z)
  have h₂ := CliffordPairStandardTensor.hilbertEquiv_operator
    (coefficientToReducedCrossed β) S T
    (pairCoefficientExtension (E := E) β
      (coefficientChangedLinearIsometry (ReducedCrossedProductPair.equiv β) z))
  exact (congrArg
    (fun v : CliffordPairStandardTensor.Source (H := E) (coefficientToReducedCrossed β) =>
      CliffordPairStandardTensor.hilbertEquiv (coefficientToReducedCrossed β) v) h₁).trans h₂

/-- The actual induced crossed grading becomes the genuine coordinate swap. -/
theorem pairModuleMap_grading
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      ((moduleGrading (cliffordCoefficientAction β) cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading β) cliffordPairGrading).grading z) =
      cliffordPairGrading.grading (pairModuleMap β z) := by
  let W : Module (cliffordCoefficientAction β) (CliffordPairModule B E) →L[ℂ]
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
    (pairModuleMap (E := E) β).toContinuousLinearMap
  let J : Module (cliffordCoefficientAction β) (CliffordPairModule B E) →L[ℂ]
      Module (cliffordCoefficientAction β) (CliffordPairModule B E) :=
    (moduleGrading (cliffordCoefficientAction β) cliffordCoefficientGrading
      (cliffordCoefficientAction_preservesGrading β)
      (cliffordPairGrading (B := B) (H := E))).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K : CliffordPairModule (ReducedCrossedProduct β) (Module β E) →L[ℂ]
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
    (cliffordPairGrading (B := ReducedCrossedProduct β)
      (H := Module β E)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let G : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ →
      (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ := fun d =>
    MulOpposite.op
      ((reducedCrossedProductGrading (cliffordCoefficientAction β)
        cliffordCoefficientGrading (cliffordCoefficientAction_preservesGrading β)).automorphism
          (MulOpposite.unop d))
  let P : CliffordPairModule B E →
      (ReducedCrossedProduct β × ReducedCrossedProduct β) →
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) := fun y q =>
    cliffordPairMk (mk β E y.1 (MulOpposite.op q.1))
      (mk β E y.2 (MulOpposite.op q.2))
  have hW (y : CliffordPairModule B E)
      (d : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :
      W (mk (cliffordCoefficientAction β) (CliffordPairModule B E) y d) =
        P y ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop d)) :=
    pairModuleMap_mk (Γ := Γ) (B := B) (E := E) β y d
  have hJ (y : CliffordPairModule B E)
      (d : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :
      J (mk (cliffordCoefficientAction β) (CliffordPairModule B E) y d) =
        mk (cliffordCoefficientAction β) (CliffordPairModule B E)
          ((cliffordPairGrading (B := B) (H := E)).grading y) (G d) :=
    moduleGrading_mk (Γ := Γ) (B := B × B) (E := CliffordPairModule B E)
      (cliffordCoefficientAction β) cliffordCoefficientGrading
      (cliffordCoefficientAction_preservesGrading β) cliffordPairGrading y d
  have hP (y : CliffordPairModule B E)
      (q : ReducedCrossedProduct β × ReducedCrossedProduct β) :
      P ((cliffordPairGrading (B := B) (H := E)).grading y)
          ((cliffordCoefficientGrading :
            CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism q) =
        K (P y q) := rfl
  have h : W.comp J = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B × B) (C := ReducedCrossedProduct (cliffordCoefficientAction β))
      (E := CliffordPairModule B E)
      (F := (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ)
      (φ := coefficientRepresentation (cliffordCoefficientAction β))
      (P := CliffordPairModule (ReducedCrossedProduct β) (Module β E))
      (f := W.comp J) (g := K.comp W)
    intro x c
    have hc : (ReducedCrossedProductPair.equiv β) (MulOpposite.unop (G c)) =
        (cliffordCoefficientGrading :
          CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism
            ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c)) :=
      ReducedCrossedProductPair.equiv_grading β (MulOpposite.unop c)
    change W (J (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c)) =
      K (W (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c))
    calc
      W (J (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c)) =
          W (mk (cliffordCoefficientAction β) (CliffordPairModule B E)
            ((cliffordPairGrading (B := B) (H := E)).grading x) (G c)) :=
        congrArg (fun v : Module (cliffordCoefficientAction β) (CliffordPairModule B E) => W v)
          (hJ x c)
      _ = P ((cliffordPairGrading (B := B) (H := E)).grading x)
          ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop (G c))) :=
        hW ((cliffordPairGrading (B := B) (H := E)).grading x) (G c)
      _ = P ((cliffordPairGrading (B := B) (H := E)).grading x)
          ((cliffordCoefficientGrading :
            CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism
              ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c))) :=
        congrArg (P ((cliffordPairGrading (B := B) (H := E)).grading x)) hc
      _ = K (P x ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c))) :=
        hP x ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c))
      _ = K (W (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c)) :=
        congrArg (fun v : CliffordPairModule (ReducedCrossedProduct β) (Module β E) => K v)
          (hW x c).symm
  exact DFunLike.congr_fun h z

/-- The actual diagonal group multiplier action is coordinatewise under the
same completed pair map. -/
theorem pairModuleMap_groupOperator (U : EquivariantHilbertModule β E) (g : Γ)
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      (groupOperator (cliffordCoefficientAction β) (CliffordPairModule B E)
        (cliffordPairAction U) g z) =
      cliffordPairMap (groupOperator β E U g) (groupOperator β E U g) (pairModuleMap β z) := by
  let W : Module (cliffordCoefficientAction β) (CliffordPairModule B E) →L[ℂ]
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
    (pairModuleMap (E := E) β).toContinuousLinearMap
  let L : Module (cliffordCoefficientAction β) (CliffordPairModule B E) →L[ℂ]
      Module (cliffordCoefficientAction β) (CliffordPairModule B E) :=
    (groupOperator (cliffordCoefficientAction β) (CliffordPairModule B E)
      (cliffordPairAction U) g).toCLM
  let R : CliffordPairModule (ReducedCrossedProduct β) (Module β E) →L[ℂ]
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
    (cliffordPairMap (groupOperator β E U g) (groupOperator β E U g)).toCLM
  let P (x : CliffordPairModule B E)
      (d : ReducedCrossedProduct β × ReducedCrossedProduct β) :
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
    cliffordPairMk
      (mk β E x.1 (MulOpposite.op d.1))
      (mk β E x.2 (MulOpposite.op d.2))
  have hW (x : CliffordPairModule B E)
      (c : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :
      W (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c) =
        P x ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop c)) :=
    pairModuleMap_mk (E := E) β x c
  have hL (x : CliffordPairModule B E)
      (c : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :
      L (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c) =
        mk (cliffordCoefficientAction β) (CliffordPairModule B E)
          ((cliffordPairAction U).action g x)
          (MulOpposite.op (leftRegular (cliffordCoefficientAction β) g
            (MulOpposite.unop c))) :=
    groupOperator_mk (cliffordCoefficientAction β) (CliffordPairModule B E)
      (cliffordPairAction U) g x c
  have hAct (x : CliffordPairModule B E) :
      (cliffordPairAction U).action g x =
        cliffordPairMk (B := B) (U.action g x.1) (U.action g x.2) := rfl
  have hR (y : CliffordPairModule (ReducedCrossedProduct β) (Module β E)) :
      R y = cliffordPairMk
        (groupOperator β E U g y.1) (groupOperator β E U g y.2) :=
    cliffordPairMap_apply (groupOperator β E U g) (groupOperator β E U g) y
  have hP (x : CliffordPairModule B E)
      (d : ReducedCrossedProduct β × ReducedCrossedProduct β) :
      P (cliffordPairMk (B := B) (U.action g x.1) (U.action g x.2))
          (leftRegular β g d.1, leftRegular β g d.2) = R (P x d) := by
    calc
      _ = cliffordPairMk
          (groupOperator β E U g (mk β E x.1 (MulOpposite.op d.1)))
          (groupOperator β E U g (mk β E x.2 (MulOpposite.op d.2))) :=
        congrArg₂
          (fun p q : Module β E =>
            cliffordPairMk (B := ReducedCrossedProduct β) p q)
          (groupOperator_mk β E U g x.1 (MulOpposite.op d.1)).symm
          (groupOperator_mk β E U g x.2 (MulOpposite.op d.2)).symm
      _ = R (P x d) := (hR (P x d)).symm
  have h : W.comp L = R.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B × B) (C := ReducedCrossedProduct (cliffordCoefficientAction β))
      (E := CliffordPairModule B E)
      (F := (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ)
      (φ := coefficientRepresentation (cliffordCoefficientAction β))
      (P := CliffordPairModule (ReducedCrossedProduct β) (Module β E))
      (f := W.comp L) (g := R.comp W)
    intro x c
    let d : ReducedCrossedProduct β × ReducedCrossedProduct β :=
      (ReducedCrossedProductPair.equiv β) (MulOpposite.unop c)
    let q : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ :=
      MulOpposite.op (leftRegular (cliffordCoefficientAction β) g (MulOpposite.unop c))
    have hC : (ReducedCrossedProductPair.equiv β) (MulOpposite.unop q) =
        (leftRegular β g d.1, leftRegular β g d.2) :=
      ReducedCrossedProductPair.equiv_leftRegular β g (MulOpposite.unop c)
    calc
      (W.comp L) (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c) =
          W (mk (cliffordCoefficientAction β) (CliffordPairModule B E)
            ((cliffordPairAction U).action g x) q) :=
        congrArg
          (fun v : Module (cliffordCoefficientAction β) (CliffordPairModule B E) => W v)
          (hL x c)
      _ = P ((cliffordPairAction U).action g x)
          ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop q)) :=
        hW ((cliffordPairAction U).action g x) q
      _ = P ((cliffordPairAction U).action g x)
          (leftRegular β g d.1, leftRegular β g d.2) :=
        congrArg (P ((cliffordPairAction U).action g x)) hC
      _ = P (cliffordPairMk (B := B) (U.action g x.1) (U.action g x.2))
          (leftRegular β g d.1, leftRegular β g d.2) :=
        congrArg
          (fun y : CliffordPairModule B E =>
            P y (leftRegular β g d.1, leftRegular β g d.2)) (hAct x)
      _ = R (P x d) := hP x d
      _ = (R.comp W)
          (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x c) :=
        congrArg
          (fun v : CliffordPairModule (ReducedCrossedProduct β) (Module β E) => R v)
          (hW x c).symm
  exact DFunLike.congr_fun h z

section Source
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAlgebraAction Γ A) (U : EquivariantHilbertModule β E)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
  (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))

def pairDiagonalRepresentation : A →⋆ₙₐ[ℂ]
    AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B E) :=
  cliffordPairDiagonalHom.toNonUnitalStarAlgHom.comp π

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] in
include hπ in
theorem pairDiagonalRepresentation_equivariant (g : Γ) (a : A) :
    (cliffordPairAction U).conjugateOperator g (pairDiagonalRepresentation π a) =
      pairDiagonalRepresentation π (α.automorphism g a) := by
  change (cliffordPairAction U).conjugateOperator g (cliffordPairMap (π a) (π a)) = _
  rw [cliffordPairAction_conjugate, hπ]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem pairModuleMap_sourceGenerator (a : A) (g : Γ)
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      (sourceGenerator (cliffordCoefficientAction β) (CliffordPairModule B E)
        (cliffordPairAction U) (pairDiagonalRepresentation π) a g z) =
      cliffordPairMap (sourceGenerator β E U π a g) (sourceGenerator β E U π a g)
        (pairModuleMap β z) := by
  let P := operatorHom β E (π a)
  let V := groupOperator β E U g
  have h₁ := pairModuleMap_operator β (π a) (π a)
    (groupOperator (cliffordCoefficientAction β) (CliffordPairModule B E)
      (cliffordPairAction U) g z)
  have h₂ := congrArg (fun v : CliffordPairModule (ReducedCrossedProduct β) (Module β E) =>
      cliffordPairMap P P v) (pairModuleMap_groupOperator β U g z)
  have h₃ := congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct β × ReducedCrossedProduct β)
      (CliffordPairModule (ReducedCrossedProduct β) (Module β E))
      (CliffordPairModule (ReducedCrossedProduct β) (Module β E)) => T (pairModuleMap β z))
    (cliffordPairMap_mul P P V V).symm
  exact h₁.trans (h₂.trans h₃)

/-- The same module map intertwines the genuine completed source action. -/
theorem pairModuleMap_reducedSourceRepresentation (a : ReducedCrossedProduct α)
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      (reducedSourceRepresentation (cliffordCoefficientAction β) (CliffordPairModule B E)
        α (cliffordPairAction U) (pairDiagonalRepresentation π)
        (pairDiagonalRepresentation_equivariant β α U π hπ) a z) =
      cliffordPairMap
        (reducedSourceRepresentation β E α U π hπ a)
        (reducedSourceRepresentation β E α U π hπ a) (pairModuleMap β z) := by
  let ρS := reducedSourceRepresentation (cliffordCoefficientAction β) (CliffordPairModule B E)
    α (cliffordPairAction U) (pairDiagonalRepresentation π)
      (pairDiagonalRepresentation_equivariant β α U π hπ)
  let ρT := cliffordPairDiagonalHom.toNonUnitalStarAlgHom.comp
    (reducedSourceRepresentation β E α U π hπ)
  let W := (pairModuleMap (E := E) β).toContinuousLinearMap
  have hS : Continuous (fun a => W (ρS a z)) :=
    W.continuous.comp
      ((AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρS)).clm_apply continuous_const)
  have hT : Continuous (fun a => ρT a (W z)) :=
    (AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρT)).clm_apply continuous_const
  refine (algebraicToReducedCrossed_denseRange α).induction_on a (isClosed_eq hS hT) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp only [map_zero, cliffordPairMap_zero, AdjointableMap.coe_zero_apply]
  | single g b =>
    change pairModuleMap β
      (ρS (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g b)) z) = _
    simp only [ρS, reducedSourceRepresentation_single]
    exact pairModuleMap_sourceGenerator β U π b g z
  | add f h ihf ihh =>
    simpa only [map_add, cliffordPairMap_add, AdjointableMap.coe_add_apply] using
      congrArg₂ (· + ·) ihf ihh
end Source

end BC4lean.KKTheory.KasparovDescent
