import BC4lean.GradedStandardIdentityCycle
import BC4lean.GradedKasparovSourcePullback

/-! # Cycles of arbitrary graded equivariant nonunital homomorphisms

The standard target module, compact left multiplication by f(b), and
zero operator give the actual homomorphism cycle. It is the genuine
source pullback of the target identity cycle. Identity and composition
pullbacks are identified by whole-cycle identity unitaries. No
nondegeneracy, unit preservation, or complemented essential range is
required, and no tensor-surjectivity assertion is made.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B C D : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D]

def gradedStandardModuleHomCycle
    (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
    (δB : CStarGrading B) (δC : CStarGrading C)
    (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
    (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b)) :
    GradedKasparovCycle β γ δB δC Cᵐᵒᵖ :=
  (gradedStandardIdentityCycle γ δC hγ).sourcePullback β δB hβ f hact hgrade

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem gradedStandardModuleHomCycle_operator
    (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
    (δB : CStarGrading B) (δC : CStarGrading C)
    (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
    (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b)) :
    (gradedStandardModuleHomCycle β γ δB δC hβ hγ f hact hgrade).operator = 0 := rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem gradedStandardModuleHomCycle_representation
    (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
    (δB : CStarGrading B) (δC : CStarGrading C)
    (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
    (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b)) (b : B) :
    (gradedStandardModuleHomCycle β γ δB δC hβ hγ f hact hgrade).representation b =
      standardLeftMul (f b) := rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem gradedStandardModuleHomCycle_representation_compact
    (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
    (δB : CStarGrading B) (δC : CStarGrading C)
    (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
    (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b)) (b : B) :
    IsModuleCompact ((gradedStandardModuleHomCycle β γ δB δC hβ hγ f hact hgrade).representation b) :=
  standardLeftMul_mem_moduleCompact (f b)

def gradedStandardModuleHomIdentityIso
    (γ : CStarAlgebraAction Γ C) (δC : CStarGrading C) (hγ : γ.PreservesGrading δC) :
    GradedKasparovCycleIso
      (gradedStandardModuleHomCycle γ γ δC δC hγ hγ
        (NonUnitalStarAlgHom.id ℂ C) (fun _ _ => rfl) (fun _ => rfl))
      (gradedStandardIdentityCycle γ δC hγ) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

def gradedStandardModuleHomCompositionPullbackIso
    (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C) (η : CStarAlgebraAction Γ D)
    (δB : CStarGrading B) (δC : CStarGrading C) (δD : CStarGrading D)
    (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC) (hη : η.PreservesGrading δD)
    (f : B →⋆ₙₐ[ℂ] C) (g : C →⋆ₙₐ[ℂ] D)
    (hactf : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (hgradef : ∀ b, f (δB.automorphism b) = δC.automorphism (f b))
    (hactg : ∀ k c, g (γ.automorphism k c) = η.automorphism k (g c))
    (hgradeg : ∀ c, g (δC.automorphism c) = δD.automorphism (g c)) :
    GradedKasparovCycleIso
      ((gradedStandardModuleHomCycle γ η δC δD hγ hη g hactg hgradeg).sourcePullback
        β δB hβ f hactf hgradef)
      (gradedStandardModuleHomCycle β η δB δD hβ hη (g.comp f)
        (fun k b => by change g (f (β.automorphism k b)) = η.automorphism k (g (f b)); rw [hactf,hactg])
        (fun b => by change g (f (δB.automorphism b)) = δD.automorphism (g (f b)); rw [hgradef,hgradeg])) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end BC4lean.KKTheory
