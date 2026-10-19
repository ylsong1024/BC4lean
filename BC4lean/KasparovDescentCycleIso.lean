import BC4lean.KasparovDescentRawCycle
import BC4lean.InteriorModuleTensorFirstFactorEquiv
import BC4lean.KasparovCycleIso
import BC4lean.OddKasparovCycleIso
import BC4lean.OddKasparovInverseRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Descent of genuine whole-cycle isomorphisms and opposite cycles

`KasparovDescentRawCycle` imports the concrete
reduced-norm source representation. Its actual norm bridge and
generator formula are construction prerequisites, never supplied as
hypotheses.


The map of whole Hilbert modules is the existing completed first-factor tensor
unitary, obtained from the actual source module unitary. It intertwines the
diagonal group action on elementary tensors and hence on all completed vectors.
The source action is intertwined first on each genuine crossed-product
generator, then on finite sums, and finally by the actual reduced-norm dense
range. This handles arbitrary, including degenerate, source representations.
It does not claim compatibility with full interval homotopy or Kasparov products.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

variable (β : CStarAlgebraAction Γ B)

/-- The actual completed tensor unitary induced by a whole source module unitary. -/
def moduleEquiv (u : HilbertModuleEquiv B E F) :
    HilbertModuleEquiv (ReducedCrossedProduct β) (Module β E) (Module β F) :=
  InteriorModuleTensorFirstFactorEquiv.hilbertEquiv (coefficientRepresentation β) u

@[simp] theorem moduleEquiv_mk (u : HilbertModuleEquiv B E F)
    (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    moduleEquiv β u (mk β E x c) = mk β F (u x) c :=
  InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_mk (coefficientRepresentation β) u x c

/-- Exact intertwining of first-factor operators survives balancing and completion. -/
theorem moduleEquiv_operator (u : HilbertModuleEquiv B E F)
    (S : AdjointableMap B E E) (T : AdjointableMap B F F)
    (hST : ∀ x, u (S x) = T (u x)) (z : Module β E) :
    moduleEquiv β u (operatorHom β E S z) =
      operatorHom β F T (moduleEquiv β u z) :=
  InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_operator
    (coefficientRepresentation β) u S T hST z

/-- The grading is intertwined on the entire actual completed module. -/
theorem moduleEquiv_grading (u : HilbertModuleEquiv B E F)
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (K : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) F)
    (hJK : ∀ x, u (J.grading x) = K.grading (u x)) (z : Module β E) :
    moduleEquiv β u ((ordinaryModuleGrading β J).grading z) =
      (ordinaryModuleGrading β K).grading (moduleEquiv β u z) := by
  let L := (moduleEquiv β u).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let JE := (ordinaryModuleGrading β J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let KF := (ordinaryModuleGrading β K).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp JE = KF.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x c
    change moduleEquiv β u ((ordinaryModuleGrading β J).grading (mk β E x c)) =
      (ordinaryModuleGrading β K).grading (moduleEquiv β u (mk β E x c))
    rw [ordinaryModuleGrading_mk, moduleEquiv_mk, moduleEquiv_mk,
      ordinaryModuleGrading_mk, hJK]
  exact DFunLike.congr_fun h z

/-- The source equivariant module unitary intertwines the actual diagonal tensor
unitaries, with the same left regular multiplier in their second factors. -/
theorem moduleEquiv_groupOperator (u : HilbertModuleEquiv B E F)
    (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F)
    (hUV : ∀ g x, u (U.action g x) = V.action g (u x))
    (g : Γ) (z : Module β E) :
    moduleEquiv β u (groupOperator β E U g z) =
      groupOperator β F V g (moduleEquiv β u z) := by
  let L := (moduleEquiv β u).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (groupOperator β E U g).toCLM =
      (groupOperator β F V g).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x c
    change moduleEquiv β u (groupOperator β E U g (mk β E x c)) =
      groupOperator β F V g (moduleEquiv β u (mk β E x c))
    rw [groupOperator_mk, moduleEquiv_mk, moduleEquiv_mk, groupOperator_mk, hUV]
  exact DFunLike.congr_fun h z

omit [PartialOrder A] [StarOrderedRing A] in
/-- The concrete covariant generators are intertwined on whole completed vectors. -/
theorem moduleEquiv_sourceGenerator (u : HilbertModuleEquiv B E F)
    (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (σ : A →⋆ₙₐ[ℂ] AdjointableMap B F F)
    (hUV : ∀ g x, u (U.action g x) = V.action g (u x))
    (hπσ : ∀ a x, u (π a x) = σ a (u x))
    (a : A) (g : Γ) (z : Module β E) :
    moduleEquiv β u (sourceGenerator β E U π a g z) =
      sourceGenerator β F V σ a g (moduleEquiv β u z) := by
  change moduleEquiv β u
    (operatorHom β E (π a) (groupOperator β E U g z)) =
      operatorHom β F (σ a) (groupOperator β F V g (moduleEquiv β u z))
  rw [moduleEquiv_operator β u (π a) (σ a) (hπσ a),
    moduleEquiv_groupOperator β u U V hUV]

variable (α : CStarAlgebraAction Γ A)

/-- Finite generator induction and actual reduced-norm density extend the exact
intertwining law to every element of the completed source crossed product. -/
theorem moduleEquiv_reducedSourceRepresentation (u : HilbertModuleEquiv B E F)
    (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (σ : A →⋆ₙₐ[ℂ] AdjointableMap B F F)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (hσ : ∀ g a, V.conjugateOperator g (σ a) = σ (α.automorphism g a))
    (hUV : ∀ g x, u (U.action g x) = V.action g (u x))
    (hπσ : ∀ a x, u (π a x) = σ a (u x))
    (z : ReducedCrossedProduct α) (x : Module β E) :
    moduleEquiv β u (reducedSourceRepresentation β E α U π hπ z x) =
      reducedSourceRepresentation β F α V σ hσ z (moduleEquiv β u x) := by
  have hE : Continuous (fun w : ReducedCrossedProduct α =>
      reducedSourceRepresentation β E α U π hπ w x) :=
    (AdjointableMap.toCLM_isometry.continuous.comp
      (map_continuous (reducedSourceRepresentation β E α U π hπ))).clm_apply continuous_const
  have hF : Continuous (fun w : ReducedCrossedProduct α =>
      reducedSourceRepresentation β F α V σ hσ w (moduleEquiv β u x)) :=
    (AdjointableMap.toCLM_isometry.continuous.comp
      (map_continuous (reducedSourceRepresentation β F α V σ hσ))).clm_apply continuous_const
  refine (algebraicToReducedCrossed_denseRange α).induction_on z
    (isClosed_eq ((moduleEquiv β u).linearIsometryEquiv.continuous.comp hE) hF) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero =>
    simp only [map_zero, AdjointableMap.coe_zero_apply]
  | single g a =>
    simpa only [reducedSourceRepresentation_single] using
      moduleEquiv_sourceGenerator β u U V π σ hUV hπσ a g x
  | add f h ihf ihh =>
    simp only [map_add, AdjointableMap.coe_add_apply, ihf, ihh]

variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- Reduced descent respects the actual even whole-cycle isomorphism relation. -/
def evenCycleIso {c : KasparovCycle α β E} {d : KasparovCycle α β F}
    (u : KasparovCycleIso c d) :
    KasparovCycleIso (evenCycle β α c) (evenCycle β α d) where
  moduleEquiv := moduleEquiv β u.moduleEquiv
  grading_intertwine := moduleEquiv_grading β u.moduleEquiv c.grading d.grading
    u.grading_intertwine
  action_intertwine _ _ := rfl
  representation_intertwine := moduleEquiv_reducedSourceRepresentation β α u.moduleEquiv
    c.groupAction d.groupAction c.representation d.representation
    c.representation_equivariant d.representation_equivariant
    u.action_intertwine u.representation_intertwine
  operator_intertwine := moduleEquiv_operator β u.moduleEquiv c.operator d.operator
    u.operator_intertwine

/-- Reduced descent respects genuine odd whole-cycle isomorphisms too. -/
def oddCycleIso {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
    (u : OddKasparovCycleIso c d) :
    OddKasparovCycleIso (oddCycle β α c) (oddCycle β α d) where
  moduleEquiv := moduleEquiv β u.moduleEquiv
  action_intertwine _ _ := rfl
  representation_intertwine := moduleEquiv_reducedSourceRepresentation β α u.moduleEquiv
    c.groupAction d.groupAction c.representation d.representation
    c.representation_equivariant d.representation_equivariant
    u.action_intertwine u.representation_intertwine
  operator_intertwine := moduleEquiv_operator β u.moduleEquiv c.operator d.operator
    u.operator_intertwine

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] in
/-- Opposite module gradings commute with this genuine trivial-coefficient tensor
grading. The statement is on all vectors, proved by completed-tensor extensionality. -/
theorem ordinaryModuleGrading_opposite
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (z : Module β E) :
    (ordinaryModuleGrading β J.opposite).grading z =
      -(ordinaryModuleGrading β J).grading z := by
  let L := (ordinaryModuleGrading β J.opposite).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let R := -(ordinaryModuleGrading β J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L = R := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x c
    change (ordinaryModuleGrading β J.opposite).grading (mk β E x c) =
      -(ordinaryModuleGrading β J).grading (mk β E x c)
    rw [ordinaryModuleGrading_mk, ordinaryModuleGrading_mk,
      GradedHilbertModule.opposite_grading_apply]
    change interiorModuleTensorMk (coefficientRepresentation β) (-J.grading x) c =
      -interiorModuleTensorMk (coefficientRepresentation β) (J.grading x) c
    exact congrArg (fun L => L c)
      ((interiorModuleTensorMk (coefficientRepresentation β)).map_neg (J.grading x))
  exact DFunLike.congr_fun h z

/-- Even descent respects the actual opposite cycle, reversing both grading and
Fredholm operator. The identity is a whole-cycle unitary, not an assumed equality. -/
def evenOppositeIso (c : KasparovCycle α β E) :
    KasparovCycleIso (evenCycle β α c.opposite) (evenCycle β α c).opposite where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine := ordinaryModuleGrading_opposite β c.grading
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine z := by
    simp only [HilbertModuleEquiv.refl_apply, evenCycle_operator,
      KasparovCycle.opposite_operator, map_neg, AdjointableMap.coe_neg_apply]

/-- Odd descent respects the actual opposite Fredholm operator. -/
def oddOppositeIso (c : OddKasparovCycle α β E) :
    OddKasparovCycleIso (oddCycle β α c.opposite) (oddCycle β α c).opposite where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine z := by
    simp only [HilbertModuleEquiv.refl_apply, oddCycle_operator,
      OddKasparovCycle.opposite_operator, map_neg, AdjointableMap.coe_neg_apply]

end BC4lean.KKTheory.KasparovDescent
