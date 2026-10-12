import BC4lean.CliffordParityCycle
import BC4lean.OddKasparovCycleIso

/-! # Clifford extraction and expansion preserve actual whole-cycle isomorphisms -/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

section Extraction
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (B × B)ᵐᵒᵖ E]
  [CStarModule (B × B)ᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul (B × B)ᵐᵒᵖ F]
  [CStarModule (B × B)ᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Restriction of an actual product-coefficient unitary to its actual range. -/
def HilbertModuleEquiv.cliffordRange (u : HilbertModuleEquiv (B × B) E F) (k : Bool) :
    HilbertModuleEquiv B (CliffordCoefficientRange B E k) (CliffordCoefficientRange B F k) where
  linearIsometryEquiv :=
    { toFun x := ⟨u (x : E), by
        change coordinateModuleProjection k (u (x : E)) = u (x : E)
        simpa only [HilbertModuleEquiv.toAdjointable_apply,
          cliffordCoefficientRange_projection] using
          (coordinateModuleProjection_map k u.toAdjointable (x : E)).symm⟩
      invFun y := ⟨u.symm (y : F), by
        change coordinateModuleProjection k (u.symm (y : F)) = u.symm (y : F)
        simpa only [HilbertModuleEquiv.toAdjointable_apply,
          cliffordCoefficientRange_projection] using
          (coordinateModuleProjection_map k u.symm.toAdjointable (y : F)).symm⟩
      left_inv x := by apply Subtype.ext; exact u.symm_apply_apply _
      right_inv y := by apply Subtype.ext; exact u.apply_symm_apply _
      map_add' x y := by apply Subtype.ext; exact u.map_add _ _
      map_smul' c x := by apply Subtype.ext; exact u.map_smul _ _
      norm_map' x := u.norm_map (x : E) }
  inner_map x y := congrArg (cliffordCoordinateExtraction k) (u.inner_map (x : E) (y : E))

@[simp] theorem HilbertModuleEquiv.cliffordRange_coe
    (u : HilbertModuleEquiv (B × B) E F) (k : Bool)
    (x : CliffordCoefficientRange B E k) : (u.cliffordRange k x : F) = u (x : E) := rfl

/-- The same extracted range unitary intertwines action, representation,
and Fredholm operator exactly. -/
def GradedKasparovCycleIso.cliffordExtraction
    {c : GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading E}
    {d : GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading F}
    (u : GradedKasparovCycleIso c d) (k : Bool) :
    OddKasparovCycleIso (cliffordExtractOddCycle k c) (cliffordExtractOddCycle k d) where
  moduleEquiv := u.moduleEquiv.cliffordRange k
  action_intertwine g x := by apply Subtype.ext; exact u.action_intertwine g (x : E)
  representation_intertwine a x := by apply Subtype.ext; exact u.representation_intertwine a (x : E)
  operator_intertwine x := by apply Subtype.ext; exact u.operator_intertwine (x : E)

/-- The genuine reconstruction unitary also intertwines every part of the
cycle. Its second coordinate is `J P₋x`, and oddness produces the minus sign. -/
def GradedKasparovCycle.cliffordReconstructionIso
    (c : GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading E) :
    GradedKasparovCycleIso c (cliffordExtractOddCycle true c).cliffordExpansion where
  moduleEquiv := cliffordModuleReconstruction c.grading
  grading_intertwine x := by
    apply Prod.ext <;> apply Subtype.ext
    · change coordinateModuleProjection true (c.grading.grading x) =
        c.grading.grading (coordinateModuleProjection false x)
      exact (coordinateModuleProjection_grading c.grading false x).symm
    · change c.grading.grading (coordinateModuleProjection false (c.grading.grading x)) =
        coordinateModuleProjection true x
      have htf : (!true : Bool) = false := rfl
      have h := coordinateModuleProjection_grading c.grading true x
      rw [htf] at h
      rw [← h, c.grading.grading_sq]
  action_intertwine g x := by
    apply Prod.ext <;> apply Subtype.ext
    · change coordinateModuleProjection true (c.groupAction.action g x) =
        c.groupAction.action g (coordinateModuleProjection true x)
      exact (coordinateModuleProjection_action c.groupAction g true x).symm
    · change c.grading.grading (coordinateModuleProjection false (c.groupAction.action g x)) =
        c.groupAction.action g (c.grading.grading (coordinateModuleProjection false x))
      rw [← coordinateModuleProjection_action, ← c.grading_preserved]
  representation_intertwine a x := by
    apply Prod.ext <;> apply Subtype.ext
    · change coordinateModuleProjection true (c.representation a x) =
        c.representation a (coordinateModuleProjection true x)
      exact (coordinateModuleProjection_map true (c.representation a) x).symm
    · change c.grading.grading (coordinateModuleProjection false (c.representation a x)) =
        c.representation a (c.grading.grading (coordinateModuleProjection false x))
      rw [← coordinateModuleProjection_map, c.representation_graded, CStarGrading.trivial_apply]
  operator_intertwine x := by
    change cliffordModuleReconstruction c.grading (c.operator x) =
      cliffordPairMap (cliffordRangeRestriction true c.operator)
        (-(cliffordRangeRestriction true c.operator))
        (cliffordModuleReconstruction c.grading x)
    simp only [cliffordPairMap_apply, AdjointableMap.coe_neg_apply]
    apply Prod.ext <;> apply Subtype.ext
    · change coordinateModuleProjection true (c.operator x) =
        c.operator (coordinateModuleProjection true x)
      exact (coordinateModuleProjection_map true c.operator x).symm
    · change c.grading.grading (coordinateModuleProjection false (c.operator x)) =
        -c.operator (c.grading.grading (coordinateModuleProjection false x))
      rw [← coordinateModuleProjection_map]
      exact c.operator_odd _

end Extraction

section Expansion
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- The constructed approximate-unit projections are exactly the coordinate
projections on the genuine product-coefficient pair module. -/
theorem coordinateModuleProjection_cliffordPair (k : Bool) (x : CliffordPairModule B E) :
    coordinateModuleProjection (B := B) k x =
      if k then cliffordPairMk x.1 0 else cliffordPairMk 0 x.2 := by
  apply module_inner_ext_left (B := B × B)
  intro y
  rw [coordinateModuleProjection_inner_left]
  cases k
  · change MulOpposite.op ((0 : B), MulOpposite.unop ⟪x.2, y.2⟫_(Bᵐᵒᵖ)) =
      MulOpposite.op (MulOpposite.unop ⟪(0 : E), y.1⟫_(Bᵐᵒᵖ),
        MulOpposite.unop ⟪x.2, y.2⟫_(Bᵐᵒᵖ))
    simp only [CStarModule.inner_zero_left, MulOpposite.unop_zero]
  · change MulOpposite.op (MulOpposite.unop ⟪x.1, y.1⟫_(Bᵐᵒᵖ), (0 : B)) =
      MulOpposite.op (MulOpposite.unop ⟪x.1, y.1⟫_(Bᵐᵒᵖ),
        MulOpposite.unop ⟪(0 : E), y.2⟫_(Bᵐᵒᵖ))
    simp only [CStarModule.inner_zero_left, MulOpposite.unop_zero]

/-- The actual first range of the pair module is unitarily isomorphic to
the original module by first-coordinate evaluation. -/
def cliffordPairFirstRangeEquiv :
    HilbertModuleEquiv B (CliffordCoefficientRange B (CliffordPairModule B E) true) E where
  linearIsometryEquiv :=
    { toFun x := (x : CliffordPairModule B E).1
      invFun x := ⟨cliffordPairMk x 0, by
        change coordinateModuleProjection true (cliffordPairMk x 0) = cliffordPairMk x 0
        rw [coordinateModuleProjection_cliffordPair]
        rfl⟩
      left_inv x := by
        apply Subtype.ext
        exact (coordinateModuleProjection_cliffordPair true (x : CliffordPairModule B E)).symm.trans
          (cliffordCoefficientRange_projection true x)
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      norm_map' x := by
        have h := congrArg (fun z : CliffordPairModule B E => z.2)
          (cliffordCoefficientRange_projection true x)
        rw [coordinateModuleProjection_cliffordPair] at h
        change 0 = (x : CliffordPairModule B E).2 at h
        change ‖(x : CliffordPairModule B E).1‖ =
          max ‖(x : CliffordPairModule B E).1‖ ‖(x : CliffordPairModule B E).2‖
        rw [← h, norm_zero, max_eq_left (norm_nonneg _)] }
  inner_map _ _ := rfl

/-- Extracting the plus range of an odd expansion returns the same entire
odd cycle up to an actual module unitary. -/
def OddKasparovCycle.cliffordExtractionExpansionIso (c : OddKasparovCycle α β E) :
    OddKasparovCycleIso (cliffordExtractOddCycle true c.cliffordExpansion) c where
  moduleEquiv := cliffordPairFirstRangeEquiv
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- An actual module unitary acts independently on the two Clifford coordinates. -/
def HilbertModuleEquiv.cliffordPair (u : HilbertModuleEquiv B E F) :
    HilbertModuleEquiv (B × B) (CliffordPairModule B E) (CliffordPairModule B F) where
  linearIsometryEquiv :=
    { toFun x := (u x.1, u x.2)
      invFun y := (u.symm y.1, u.symm y.2)
      left_inv x := by apply Prod.ext <;> exact u.symm_apply_apply _
      right_inv y := by apply Prod.ext <;> exact u.apply_symm_apply _
      map_add' x y := by apply Prod.ext <;> exact u.map_add _ _
      map_smul' c x := by apply Prod.ext <;> exact u.map_smul _ _
      norm_map' x := by
        change max ‖u x.1‖ ‖u x.2‖ = max ‖x.1‖ ‖x.2‖
        rw [u.norm_map, u.norm_map] }
  inner_map x y := by
    apply MulOpposite.unop_injective
    apply Prod.ext <;> exact congrArg MulOpposite.unop (u.inner_map _ _)

/-- Expansion preserves genuine isomorphisms of entire odd cycles. -/
def OddKasparovCycleIso.cliffordExpansion
    {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
    (u : OddKasparovCycleIso c d) :
    GradedKasparovCycleIso c.cliffordExpansion d.cliffordExpansion where
  moduleEquiv := u.moduleEquiv.cliffordPair
  grading_intertwine x := rfl
  action_intertwine g x := by apply Prod.ext <;> exact u.action_intertwine g _
  representation_intertwine a x := by apply Prod.ext <;> exact u.representation_intertwine a _
  operator_intertwine x := by
    change u.moduleEquiv.cliffordPair (cliffordPairMap c.operator (-c.operator) x) =
      cliffordPairMap d.operator (-d.operator) (u.moduleEquiv.cliffordPair x)
    simp only [cliffordPairMap_apply, AdjointableMap.coe_neg_apply]
    apply Prod.ext
    · exact u.operator_intertwine x.1
    · change u.moduleEquiv (-c.operator x.2) = -d.operator (u.moduleEquiv x.2)
      rw [u.moduleEquiv.map_neg, u.operator_intertwine]

end Expansion
end BC4lean.KKTheory
