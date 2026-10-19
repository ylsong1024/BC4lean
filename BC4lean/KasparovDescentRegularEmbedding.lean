import BC4lean.KasparovDescentAction
import BC4lean.ReducedRegularTensorEmbedding
import BC4lean.StandardModuleTensorEmbedding
import BC4lean.InteriorModuleTensorSecondFactorIsometry
import BC4lean.InteriorModuleTensorAssociator
import BC4lean.InteriorModuleTensorFaithful

/-! # The genuine regular amplification embedding for reduced descent

The representation used for amplification is the
actual inclusion of the reduced crossed algebra into its defining regular
adjointable operators.  It is faithful by subtype injectivity.  The actual
amplified module embeds isometrically into ℓ²(Γ,E), using the proved tensor
associator, the proved standard-module pairing embedding, the actual
second-factor tensor embedding, and the proved twisted regular tensor map.
No nondegeneracy, surjectivity, or reduced-norm bound is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped InnerProductSpace KasparovDescent

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- The actual defining representation of the crossed coefficient algebra. -/
def regularCoefficientRepresentation (β : CStarAlgebraAction Γ B) :
    ReducedCrossedProduct β →⋆ₙₐ[ℂ]
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  NonUnitalStarSubalgebraClass.subtype (reducedCrossedAlgebra β)

@[simp] theorem regularCoefficientRepresentation_apply (β : CStarAlgebraAction Γ B)
    (c : ReducedCrossedProduct β) :
    regularCoefficientRepresentation β c =
      (c : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (ReducedCrossedHilbertModule B Γ)) := rfl

theorem regularCoefficientRepresentation_injective (β : CStarAlgebraAction Γ B) :
    Function.Injective (regularCoefficientRepresentation β) := Subtype.val_injective

@[simp] theorem regularCoefficientRepresentation_coefficient
    (β : CStarAlgebraAction Γ B) (b : B) :
    regularCoefficientRepresentation β (coefficientToReducedCrossed β b) =
      reducedCrossedCoefficientHom β b := rfl

/-- The standard crossed module tensored with its actual regular module
embeds in that regular module with its original B-valued pairing. -/
def standardRegularEmbedding (β : CStarAlgebraAction Γ B) :
    ModuleTensorSecondFactorIsometry
      (InteriorModuleTensorAssociator.rightRepresentation
        (coefficientRepresentation β) (regularCoefficientRepresentation β))
      (reducedCrossedCoefficientHom β) where
  second := StandardModuleTensorEmbedding.isometry (regularCoefficientRepresentation β)
  map_op_smul := StandardModuleTensorEmbedding.isometry_map_op_smul
    (regularCoefficientRepresentation β)
  inner_map := StandardModuleTensorEmbedding.isometry_inner
    (regularCoefficientRepresentation β)
  intertwines b u := by
    change StandardModuleTensorEmbedding.isometry (regularCoefficientRepresentation β)
        (interiorModuleTensorOperator (regularCoefficientRepresentation β)
          (standardLeftMul (coefficientToReducedCrossed β b)) u) =
      regularCoefficientRepresentation β (coefficientToReducedCrossed β b)
        (StandardModuleTensorEmbedding.isometry (regularCoefficientRepresentation β) u)
    exact StandardModuleTensorEmbedding.isometry_intertwines
      (regularCoefficientRepresentation β) (coefficientToReducedCrossed β b) u

variable (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The existing actual associator, specialized to the descended coefficient module. -/
def regularAssociatorEmbedding :
    InteriorModuleTensor (E := Module β E) (regularCoefficientRepresentation β)
      →ₗᵢ[ℂ] InteriorModuleTensorAssociator.RightTensor (E := E)
        (coefficientRepresentation β) (regularCoefficientRepresentation β) := by
  with_reducible_and_instances
    exact InteriorModuleTensorAssociator.completionIsometry
      (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
      (coefficientRepresentation β) (regularCoefficientRepresentation β)

/-- Collapse of the standard crossed-product factor after the actual associator. -/
def regularCollapseEmbedding :
    InteriorModuleTensorAssociator.RightTensor (E := E)
      (coefficientRepresentation β) (regularCoefficientRepresentation β)
      →ₗᵢ[ℂ] InteriorModuleTensor (E := E) (reducedCrossedCoefficientHom β) :=
  (standardRegularEmbedding β).interiorIsometry (E := E)

/-- The second-factor embedding is the actual standard-module collapse. -/
private theorem standardRegularEmbedding_second_apply
    (q : InteriorModuleTensor (E := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (regularCoefficientRepresentation β)) :
    (standardRegularEmbedding β).second q =
      StandardModuleTensorEmbedding.isometry (regularCoefficientRepresentation β) q := rfl

/-- The specialized associator has exactly the existing completed associator formula. -/
private theorem regularAssociatorEmbedding_apply
    (u : InteriorModuleTensor (E := Module β E) (regularCoefficientRepresentation β)) :
    regularAssociatorEmbedding β E u =
      InteriorModuleTensorAssociator.completionMap (E := E)
        (coefficientRepresentation β) (regularCoefficientRepresentation β) u := rfl

/-- The completed associator on one concrete outer elementary tensor. -/
private theorem regularCompletedAssociator_mk (u : InteriorModuleTensor (E := E) (coefficientRepresentation β))
    (z : ReducedCrossedHilbertModule B Γ) :
    InteriorModuleTensorAssociator.completionMap
      (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
    (coefficientRepresentation β) (regularCoefficientRepresentation β)
      (interiorModuleTensorMk (B := ReducedCrossedProduct β) (C := B)
        (E := InteriorModuleTensor (E := E) (coefficientRepresentation β))
        (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) u z) =
      InteriorModuleTensorAssociator.creation
        (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
        (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
        (coefficientRepresentation β) (regularCoefficientRepresentation β) u z := by
  have h := InteriorModuleTensorAssociator.completionMap_mk
    (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
    (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
    (coefficientRepresentation β) (regularCoefficientRepresentation β) u z
  exact h

/-- Evaluation of creation on one concrete inner elementary tensor. -/
private theorem regularCreation_mk_apply (x : E)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : ReducedCrossedHilbertModule B Γ) :
    InteriorModuleTensorAssociator.creation
      (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
      (coefficientRepresentation β) (regularCoefficientRepresentation β) (mk β E x c) z =
      InteriorModuleTensorAssociator.pureCreation
      (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
        (coefficientRepresentation β) (regularCoefficientRepresentation β) x c z := by
  dsimp only [mk]
  with_reducible_and_instances
    exact congrArg
      (fun T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (InteriorModuleTensorAssociator.RightTensor (E := E)
          (coefficientRepresentation β) (regularCoefficientRepresentation β)) => T z)
      (InteriorModuleTensorAssociator.creation_mk
        (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
        (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
        (coefficientRepresentation β) (regularCoefficientRepresentation β) x c)

/-- Concrete pure creation is the actual nested elementary tensor. -/
private theorem regularPureCreation_apply (x : E)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : ReducedCrossedHilbertModule B Γ) :
    InteriorModuleTensorAssociator.pureCreation
      (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
      (coefficientRepresentation β) (regularCoefficientRepresentation β) x c z =
      interiorModuleTensorMk (E := E)
        (InteriorModuleTensorAssociator.rightRepresentation
          (coefficientRepresentation β) (regularCoefficientRepresentation β)) x
        (interiorModuleTensorMk (E := (ReducedCrossedProduct β)ᵐᵒᵖ)
          (regularCoefficientRepresentation β) c z) := rfl

/-- The existing completed associator formula with the concrete coefficients fixed. -/
private theorem regularCompletedAssociator_triple (x : E)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : ReducedCrossedHilbertModule B Γ) :
    InteriorModuleTensorAssociator.completionMap
      (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
      (coefficientRepresentation β) (regularCoefficientRepresentation β)
      (interiorModuleTensorMk (B := ReducedCrossedProduct β) (C := B)
        (E := InteriorModuleTensor (E := E) (coefficientRepresentation β))
        (F := ReducedCrossedHilbertModule B Γ) (regularCoefficientRepresentation β) (mk β E x c) z) =
      interiorModuleTensorMk (E := E)
        (InteriorModuleTensorAssociator.rightRepresentation
          (coefficientRepresentation β) (regularCoefficientRepresentation β)) x
        (interiorModuleTensorMk (E := (ReducedCrossedProduct β)ᵐᵒᵖ) (regularCoefficientRepresentation β) c z) := by
  have h := (regularCompletedAssociator_mk β E (mk β E x c) z).trans
    ((regularCreation_mk_apply β E x c z).trans (regularPureCreation_apply β E x c z))
  exact h

/-- The specialized associator on actual triple elementary tensors. -/
private theorem regularAssociatorEmbedding_triple (x : E)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) (z : ReducedCrossedHilbertModule B Γ) :
    regularAssociatorEmbedding β E
      (interiorModuleTensorMk (E := Module β E) (regularCoefficientRepresentation β) (mk β E x c) z) =
      interiorModuleTensorMk (E := E)
        (InteriorModuleTensorAssociator.rightRepresentation
          (coefficientRepresentation β) (regularCoefficientRepresentation β)) x
        (interiorModuleTensorMk (E := (ReducedCrossedProduct β)ᵐᵒᵖ) (regularCoefficientRepresentation β) c z) := by
  exact (regularAssociatorEmbedding_apply β E _).trans
    (regularCompletedAssociator_triple β E x c z)

/-- The standard-factor collapse on actual elementary tensors. -/
private theorem regularCollapseEmbedding_mk (x : E)
    (q : InteriorModuleTensor (E := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (regularCoefficientRepresentation β)) :
    regularCollapseEmbedding β E
      (interiorModuleTensorMk (E := E)
        (InteriorModuleTensorAssociator.rightRepresentation
          (coefficientRepresentation β) (regularCoefficientRepresentation β)) x q) =
      interiorModuleTensorMk (reducedCrossedCoefficientHom β) x
        (StandardModuleTensorEmbedding.isometry (regularCoefficientRepresentation β) q) := by
  change (standardRegularEmbedding β).interiorIsometry
    (interiorModuleTensorMk _ x q) = _
  with_reducible_and_instances
    exact ((standardRegularEmbedding β).interiorIsometry_mk (E := E) x q).trans
      (congrArg (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x)
        (standardRegularEmbedding_second_apply β q))

/-- The specialized associator preserves its actual coefficient pairing. -/
private theorem regularAssociatorEmbedding_inner
    (u v : InteriorModuleTensor (E := Module β E) (regularCoefficientRepresentation β)) :
    ⟪regularAssociatorEmbedding β E u, regularAssociatorEmbedding β E v⟫_(Bᵐᵒᵖ) =
      ⟪u, v⟫_(Bᵐᵒᵖ) := by
  with_reducible_and_instances
    have h := congrArg₂ (fun x y : InteriorModuleTensorAssociator.RightTensor (E := E)
        (coefficientRepresentation β) (regularCoefficientRepresentation β) =>
      ⟪x, y⟫_(Bᵐᵒᵖ)) (regularAssociatorEmbedding_apply β E u)
        (regularAssociatorEmbedding_apply β E v)
    exact h.trans (InteriorModuleTensorAssociator.completionMap_inner
      (B := B) (C := ReducedCrossedProduct β) (D := B) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (G := ReducedCrossedHilbertModule B Γ)
      (coefficientRepresentation β) (regularCoefficientRepresentation β) u v)

/-- The standard-factor collapse preserves its actual coefficient pairing. -/
private theorem regularCollapseEmbedding_inner
    (u v : InteriorModuleTensorAssociator.RightTensor (E := E)
      (coefficientRepresentation β) (regularCoefficientRepresentation β)) :
    ⟪regularCollapseEmbedding β E u, regularCollapseEmbedding β E v⟫_(Bᵐᵒᵖ) =
      ⟪u, v⟫_(Bᵐᵒᵖ) := by
  change ⟪(standardRegularEmbedding β).interiorIsometry u,
    (standardRegularEmbedding β).interiorIsometry v⟫_(Bᵐᵒᵖ) = _
  exact (standardRegularEmbedding β).interiorIsometry_inner (E := E) u v

/-- Amplifying the actual descended module by its faithful coefficient
representation gives an actual isometric embedding into the indexed module. -/
def regularEmbedding (U : EquivariantHilbertModule β E) :
    InteriorModuleTensor (E := Module β E) (regularCoefficientRepresentation β)
      →ₗᵢ[ℂ] IndexedHilbertModule.Module B E Γ := by
  let a := regularAssociatorEmbedding β E
  let c := regularCollapseEmbedding β E
  let r := ReducedRegularTensorEmbedding.isometry U
  refine
    { toLinearMap :=
        { toFun := fun u => r (c (a u))
          map_add' := ?_
          map_smul' := ?_ }
      norm_map' := ?_ }
  · intro u v
    simp only [map_add]
  · intro z u
    simp only [map_smul, RingHom.id_apply]
  · intro u
    change ‖r (c (a u))‖ = ‖u‖
    rw [r.norm_map, c.norm_map, a.norm_map]

/-- The genuine formula on three elementary factors. -/
@[simp] theorem regularEmbedding_triple (U : EquivariantHilbertModule β E)
    (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ)
    (z : ReducedCrossedHilbertModule B Γ) :
    regularEmbedding β E U
        (interiorModuleTensorMk (E := Module β E) (regularCoefficientRepresentation β) (mk β E x c) z) =
      ReducedRegularTensorEmbedding.isometry U
        (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x
          (regularCoefficientRepresentation β (MulOpposite.unop c) z)) := by
  let R := ReducedRegularTensorEmbedding.isometry U
  change R (regularCollapseEmbedding β E
    (regularAssociatorEmbedding β E
      (interiorModuleTensorMk (E := Module β E) (regularCoefficientRepresentation β) (mk β E x c) z))) = _
  calc
    _ = R (regularCollapseEmbedding β E
        (interiorModuleTensorMk (E := E)
          (InteriorModuleTensorAssociator.rightRepresentation
            (coefficientRepresentation β) (regularCoefficientRepresentation β)) x
          (interiorModuleTensorMk (E := (ReducedCrossedProduct β)ᵐᵒᵖ) (regularCoefficientRepresentation β) c z))) :=
      congrArg (fun q => R (regularCollapseEmbedding β E q))
        (regularAssociatorEmbedding_triple β E x c z)
    _ = R (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x
        (StandardModuleTensorEmbedding.isometry (regularCoefficientRepresentation β)
          (interiorModuleTensorMk (E := (ReducedCrossedProduct β)ᵐᵒᵖ) (regularCoefficientRepresentation β) c z))) :=
      congrArg R (regularCollapseEmbedding_mk β E x
        (interiorModuleTensorMk (E := (ReducedCrossedProduct β)ᵐᵒᵖ) (regularCoefficientRepresentation β) c z))
    _ = _ := congrArg (fun q => R (interiorModuleTensorMk (reducedCrossedCoefficientHom β) x q))
      (StandardModuleTensorEmbedding.isometry_mk (regularCoefficientRepresentation β) c z)

/-- The full coefficient-valued pairing is preserved by the actual embedding. -/
theorem regularEmbedding_inner (U : EquivariantHilbertModule β E)
    (u v : InteriorModuleTensor (E := Module β E) (regularCoefficientRepresentation β)) :
    ⟪regularEmbedding β E U u, regularEmbedding β E U v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) := by
  let P := regularAssociatorEmbedding β E
  let C := regularCollapseEmbedding β E
  let R := ReducedRegularTensorEmbedding.isometry U
  change ⟪R (C (P u)), R (C (P v))⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ)
  calc
    _ = ⟪C (P u), C (P v)⟫_(Bᵐᵒᵖ) :=
      ReducedRegularTensorEmbedding.isometry_inner U _ _
    _ = ⟪P u, P v⟫_(Bᵐᵒᵖ) := regularCollapseEmbedding_inner β E (P u) (P v)
    _ = ⟪u, v⟫_(Bᵐᵒᵖ) := regularAssociatorEmbedding_inner β E u v

/-- This amplification detects the actual adjointable operator norm because
the crossed coefficient representation is the concrete faithful inclusion. -/
theorem norm_regularAmplification (T :
    AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E)) :
    ‖interiorModuleTensorOperator (regularCoefficientRepresentation β) T‖ = ‖T‖ :=
  norm_interiorModuleTensorOperator_of_faithful (regularCoefficientRepresentation β)
    (regularCoefficientRepresentation_injective β) T

end BC4lean.KKTheory.KasparovDescent
