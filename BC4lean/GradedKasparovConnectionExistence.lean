import BC4lean.GradedModuleFrameConnection
import BC4lean.GradedKasparovCycle
import BC4lean.KasparovConnection

/-! # Constructed odd connections for genuine graded Kasparov cycles

For arbitrary source, intermediate and target coefficient gradings, actual
countable generation constructs a homogeneous Parseval frame. Its actual
creation-row coisometry and signed diagonal construct an odd operator on the
genuine interior tensor satisfying all four homogeneous compact connection
conditions. Nonunital and degenerate representations are allowed.

This proves connection existence, not the Kasparov product theorem: the
cycle defects and localized positivity of a product operator require the
separate technical-theorem construction.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

/-- The exact four homogeneous compact conditions for an odd connection to
the second genuine graded cycle on the actual balanced and completed tensor. -/
structure GradedKasparovConnection
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) : Prop where
  even (x : E) (hx : c.grading.grading x = x) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp d.operator -
      R.comp (moduleCreationMap d.representation x))
  even_adjoint (x : E) (hx : c.grading.grading x = x) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp (star d.operator) -
      (star R).comp (moduleCreationMap d.representation x))
  odd (x : E) (hx : c.grading.grading x = -x) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp d.operator +
      R.comp (moduleCreationMap d.representation x))
  odd_adjoint (x : E) (hx : c.grading.grading x = -x) :
    IsModuleCompact ((moduleCreationMap d.representation x).comp (star d.operator) +
      (star R).comp (moduleCreationMap d.representation x))

theorem homogeneous_frame_gradedKasparovConnection
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    {ξ : ℕ → E} (P : ModuleParsevalFrame (B := B) ξ) (p : ℕ → Bool)
    (hξ : ∀ n, c.grading.grading (ξ n) = if p n then -ξ n else ξ n) :
    GradedKasparovConnection c d (P.gradedConnection d.representation p d.operator) where
  even x hx := by
    have h := (P.gradedConnection_comp_creation_sub_compact c.grading d.representation
      p hξ d.operator d.commutator_compact x false
        (by simpa only [if_neg (by decide : (false : Bool) ≠ true)] using hx)).neg
    simpa only [if_neg (by decide : (false : Bool) ≠ true), neg_sub] using h
  even_adjoint x hx := by
    rw [AdjointableMap.star_eq_adjoint d.operator,
      AdjointableMap.star_eq_adjoint (P.gradedConnection d.representation p d.operator),
      P.gradedConnection_adjoint]
    have h := (P.gradedConnection_comp_creation_sub_compact c.grading d.representation
      p hξ d.operator.adjoint (graded_coefficient_commutator_adjoint_compact
        d.representation d.operator d.commutator_compact) x false
        (by simpa only [if_neg (by decide : (false : Bool) ≠ true)] using hx)).neg
    simpa only [if_neg (by decide : (false : Bool) ≠ true), neg_sub] using h
  odd x hx := by
    have h := P.gradedConnection_comp_creation_sub_compact c.grading d.representation
      p hξ d.operator d.commutator_compact x true (by simpa only [if_true] using hx)
    convert h using 1
    ext y
    simp only [if_true, AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply, map_neg]
    abel
  odd_adjoint x hx := by
    rw [AdjointableMap.star_eq_adjoint d.operator,
      AdjointableMap.star_eq_adjoint (P.gradedConnection d.representation p d.operator),
      P.gradedConnection_adjoint]
    have h := P.gradedConnection_comp_creation_sub_compact c.grading d.representation
      p hξ d.operator.adjoint (graded_coefficient_commutator_adjoint_compact
        d.representation d.operator d.commutator_compact) x true
        (by simpa only [if_true] using hx)
    convert h using 1
    ext y
    simp only [if_true, AdjointableMap.comp_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_neg_apply, map_neg]
    abel

/-- Actual odd graded connections are constructed from the two genuine
cycles; no frame, completion, connection or product operator is assumed. -/
theorem exists_odd_gradedKasparovConnection
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F) :
    ∃ R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation),
      (c.grading.interiorTensor d.grading d.representation_graded).IsOdd
        (c.grading.interiorTensor d.grading d.representation_graded) R ∧
      GradedKasparovConnection c d R := by
  obtain ⟨ξ, p, ⟨P⟩, hξ⟩ := exists_homogeneousModuleParsevalFrame c.grading c.countablyGenerated
  exact ⟨P.gradedConnection d.representation p d.operator,
    P.gradedConnection_isOdd c.grading d.grading d.representation d.representation_graded
      p hξ d.operator_odd,
    homogeneous_frame_gradedKasparovConnection c d P p hξ⟩

/-- A genuine selfadjoint contractive second operator has an actual odd
selfadjoint contractive connection on the constructed interior tensor. -/
theorem exists_odd_selfadjoint_contractive_gradedKasparovConnection
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (hdsa : IsSelfAdjoint d.operator) (hdnorm : ‖d.operator‖ ≤ 1) :
    ∃ R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation),
      (c.grading.interiorTensor d.grading d.representation_graded).IsOdd
        (c.grading.interiorTensor d.grading d.representation_graded) R ∧
      IsSelfAdjoint R ∧ ‖R‖ ≤ 1 ∧ GradedKasparovConnection c d R := by
  obtain ⟨ξ, p, ⟨P⟩, hξ⟩ := exists_homogeneousModuleParsevalFrame c.grading c.countablyGenerated
  exact ⟨P.gradedConnection d.representation p d.operator,
    P.gradedConnection_isOdd c.grading d.grading d.representation d.representation_graded
      p hξ d.operator_odd,
    P.gradedConnection_selfadjoint d.representation p hdsa,
    (P.norm_gradedConnection_le d.representation p d.operator).trans hdnorm,
    homogeneous_frame_gradedKasparovConnection c d P p hξ⟩

/-- The actual odd-connection theorem specializes to the repository's raw
cycles over trivially graded algebras, preserving all four compact identities. -/
theorem exists_odd_kasparovConnection
    (c : KasparovCycle α β E) (d : KasparovCycle β γ F) :
    ∃ R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation),
      (c.grading.interiorTensor d.grading d.representation_even).IsOdd
        (c.grading.interiorTensor d.grading d.representation_even) R ∧
      KasparovConnection c d R := by
  obtain ⟨R, hodd, hR⟩ := exists_odd_gradedKasparovConnection
    (GradedKasparovCycle.ofKasparovCycle c) (GradedKasparovCycle.ofKasparovCycle d)
  exact ⟨R, hodd, ⟨hR.even, hR.even_adjoint, hR.odd, hR.odd_adjoint⟩⟩

end BC4lean.KKTheory
