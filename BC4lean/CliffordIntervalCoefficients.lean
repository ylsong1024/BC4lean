import BC4lean.GradedCycleCoefficientTransport
import BC4lean.GradedIntervalKasparovFibre
import BC4lean.CliffordParityCycle

/-! # The actual coefficient equivalence for Clifford interval cycles

Continuous functions into a product are identified with pairs of continuous
functions by their two coordinates. The equivalence is an actual nonunital
complex star-algebra equivalence and therefore isometric. Its compatibility
with evaluation, the coefficient group action, and the swap grading is
proved explicitly. Arbitrary interval modules transport along this map.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B X M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]

/-- The genuine star equivalence `C(X,B×B) ≃ C(X,B) × C(X,B)`. -/
def continuousProductCoefficientEquiv : C(X, B × B) ≃⋆ₐ[ℂ] C(X, B) × C(X, B) where
  toFun f :=
    (⟨fun t => (f t).1, continuous_fst.comp f.continuous⟩,
      ⟨fun t => (f t).2, continuous_snd.comp f.continuous⟩)
  invFun f := ⟨fun t => (f.1 t, f.2 t), f.1.continuous.prodMk f.2.continuous⟩
  left_inv f := by ext t <;> rfl
  right_inv f := by apply Prod.ext <;> ext t <;> rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem continuousProductCoefficientEquiv_fst_apply
    (f : C(X, B × B)) (t : X) : (continuousProductCoefficientEquiv f).1 t = (f t).1 := rfl

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem continuousProductCoefficientEquiv_snd_apply
    (f : C(X, B × B)) (t : X) : (continuousProductCoefficientEquiv f).2 t = (f t).2 := rfl

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem continuousProductCoefficientEquiv_symm_apply
    (f : C(X, B) × C(X, B)) (t : X) :
    continuousProductCoefficientEquiv.symm f t = (f.1 t, f.2 t) := rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem continuousProductCoefficientEquiv_norm (f : C(X, B × B)) :
    ‖continuousProductCoefficientEquiv f‖ = ‖f‖ := StarAlgEquiv.norm_map _ _

theorem continuousProductCoefficientEquiv_action (β : CStarAlgebraAction Γ B)
    (g : Γ) (f : C(X, B × B)) :
    continuousProductCoefficientEquiv
        (((cliffordCoefficientAction β).continuousSections (X := X)).automorphism g f) =
      (cliffordCoefficientAction (β.continuousSections (X := X))).automorphism g
        (continuousProductCoefficientEquiv f) := rfl

theorem continuousProductCoefficientEquiv_grading (f : C(X, B × B)) :
    continuousProductCoefficientEquiv
        ((cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections.automorphism f) =
      cliffordCoefficientGrading.automorphism (continuousProductCoefficientEquiv f) := rfl

theorem continuousProductCoefficientEquiv_symm_action (β : CStarAlgebraAction Γ B)
    (g : Γ) (f : C(X, B) × C(X, B)) :
    continuousProductCoefficientEquiv.symm
        ((cliffordCoefficientAction (β.continuousSections (X := X))).automorphism g f) =
      (((cliffordCoefficientAction β).continuousSections (X := X)).automorphism g)
        (continuousProductCoefficientEquiv.symm f) := rfl

theorem continuousProductCoefficientEquiv_symm_grading (f : C(X, B) × C(X, B)) :
    continuousProductCoefficientEquiv.symm (cliffordCoefficientGrading.automorphism f) =
      (cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections.automorphism
        (continuousProductCoefficientEquiv.symm f) := rfl

section IntervalCycles

variable [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B × B)ᵐᵒᵖ M] [CStarModule C(X, B × B)ᵐᵒᵖ M] [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- The actual arbitrary interval module, now over a product of coefficient
function algebras. No section-module or fixed-module hypothesis is imposed. -/
abbrev CliffordSplitIntervalModule (B M : Type*) [NonUnitalCStarAlgebra B]
    {X : Type*} [TopologicalSpace X] [CompactSpace X] :=
  CoefficientChangedModule (continuousProductCoefficientEquiv (B := B) (X := X)) M

/-- A general graded interval cycle can be extracted after actual coefficient
transport. The result is an odd cycle over the coefficient function algebra. -/
def GradedKasparovCycle.cliffordIntervalExtraction
    (c : GradedKasparovCycle α ((cliffordCoefficientAction β).continuousSections (X := X))
      CStarGrading.trivial (cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections M) :
    OddKasparovCycle α (β.continuousSections (X := X))
      (CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) true) :=
  cliffordExtractOddCycle true
    (c.coefficientChanged continuousProductCoefficientEquiv
      (cliffordCoefficientAction (β.continuousSections (X := X))) cliffordCoefficientGrading
      (continuousProductCoefficientEquiv_action β) continuousProductCoefficientEquiv_grading)

end IntervalCycles

section OddExpansion

variable [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Expand an arbitrary odd interval cycle and transport the genuine
product coefficient algebra back to continuous Clifford-valued functions. -/
def OddKasparovCycle.cliffordIntervalExpansion
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) :
    GradedKasparovCycle α ((cliffordCoefficientAction β).continuousSections (X := X))
      CStarGrading.trivial (cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections
      (CoefficientChangedModule (continuousProductCoefficientEquiv (B := B) (X := X)).symm
        (CliffordPairModule C(X, B) M)) :=
  c.cliffordExpansion.coefficientChanged continuousProductCoefficientEquiv.symm
    ((cliffordCoefficientAction β).continuousSections (X := X))
    cliffordCoefficientGrading.continuousSections
    (continuousProductCoefficientEquiv_symm_action β)
    continuousProductCoefficientEquiv_symm_grading

end OddExpansion
end BC4lean.KKTheory
