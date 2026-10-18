import BC4lean.EquivariantOperatorAutomorphism
import BC4lean.EquivariantCompactOperator

/-! # The compact-operator action needed for Kasparov descent

The given semilinear Hilbert-module action induces actual actions on all
adjointable endomorphisms and on their compact ideal. The latter is the
coefficient action used in a linking-algebra construction of crossed-product
modules. This file does not construct a crossed product or a descent map.
-/

noncomputable section
namespace BC4lean.KKTheory.EquivariantHilbertModule

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ B}

/-- Conjugation is an actual action on the adjointable endomorphism algebra. -/
def adjointableAction (U : EquivariantHilbertModule α E) :
    CStarAlgebraAction Γ (AdjointableMap B E E) where
  automorphism :=
    { toFun := U.conjugateOperatorStarAlgEquiv
      map_one' := by
        ext T x
        simp [conjugateOperatorStarAlgEquiv]
      map_mul' := by
        intro g h
        ext T x
        simp [conjugateOperatorStarAlgEquiv, conjugateMap_apply,
          mul_inv_rev] }

@[simp] theorem adjointableAction_apply (U : EquivariantHilbertModule α E)
    (g : Γ) (T : AdjointableMap B E E) :
    U.adjointableAction.automorphism g T = U.conjugateOperator g T := rfl

/-- Restrict conjugation and its actual inverse to the compact ideal. -/
def compactOperatorStarAlgEquiv (U : EquivariantHilbertModule α E) (g : Γ) :
    CompactModuleOperator B E ≃⋆ₐ[ℂ] CompactModuleOperator B E where
  toFun T := ⟨U.conjugateOperator g T, U.conjugateOperator_mem_moduleCompact g T.property⟩
  invFun T := ⟨U.conjugateOperator g⁻¹ T,
    U.conjugateOperator_mem_moduleCompact g⁻¹ T.property⟩
  left_inv T := by
    apply Subtype.ext
    exact (U.conjugateOperatorStarAlgEquiv g).left_inv T
  right_inv T := by
    apply Subtype.ext
    exact (U.conjugateOperatorStarAlgEquiv g).right_inv T
  map_mul' S T := Subtype.ext (map_mul (U.conjugateOperatorStarAlgEquiv g)
    (S : AdjointableMap B E E) (T : AdjointableMap B E E))
  map_add' S T := Subtype.ext (map_add (U.conjugateOperatorStarAlgEquiv g)
    (S : AdjointableMap B E E) (T : AdjointableMap B E E))
  map_star' T := Subtype.ext (map_star (U.conjugateOperatorStarAlgEquiv g)
    (T : AdjointableMap B E E))
  map_smul' c T := Subtype.ext (map_smul (U.conjugateOperatorStarAlgEquiv g) c
    (T : AdjointableMap B E E))

omit [CompleteSpace E] in
@[simp] theorem compactOperatorStarAlgEquiv_coe
    (U : EquivariantHilbertModule α E) (g : Γ) (T : CompactModuleOperator B E) :
    (U.compactOperatorStarAlgEquiv g T : AdjointableMap B E E) =
      U.conjugateOperator g T := rfl

/-- The compact ideal carries the genuine conjugation action. -/
def compactOperatorAction (U : EquivariantHilbertModule α E) :
    CStarAlgebraAction Γ (CompactModuleOperator B E) where
  automorphism :=
    { toFun := U.compactOperatorStarAlgEquiv
      map_one' := by
        ext T x
        simp [compactOperatorStarAlgEquiv]
      map_mul' := by
        intro g h
        ext T x
        simp [compactOperatorStarAlgEquiv, conjugateMap_apply, mul_inv_rev] }

@[simp] theorem compactOperatorAction_coe (U : EquivariantHilbertModule α E)
    (g : Γ) (T : CompactModuleOperator B E) :
    (U.compactOperatorAction.automorphism g T : AdjointableMap B E E) =
      U.conjugateOperator g T := rfl

/-- The compact inclusion intertwines the two actual actions. -/
theorem compactOperatorAction_equivariant (U : EquivariantHilbertModule α E)
    (g : Γ) (T : CompactModuleOperator B E) :
    (U.compactOperatorAction.automorphism g T : AdjointableMap B E E) =
      U.adjointableAction.automorphism g T := rfl

/-- On rank-one operators the compact action acts on both vectors. -/
@[simp] theorem compactOperatorAction_rankOne (U : EquivariantHilbertModule α E)
    (g : Γ) (x y : E) :
    U.compactOperatorAction.automorphism g
        ⟨moduleRankOne x y, moduleRankOne_mem_moduleCompact x y⟩ =
      ⟨moduleRankOne (U.action g x) (U.action g y),
        moduleRankOne_mem_moduleCompact (U.action g x) (U.action g y)⟩ := by
  apply Subtype.ext
  exact U.conjugateMap_rankOne U g x y

end BC4lean.KKTheory.EquivariantHilbertModule
