import BC4lean.OperatorK0Equivalence
import BC4lean.ReducedCompletion
import BC4lean.ReducedOperatorK0

/-! # Abstract and concrete models of the degree-zero analytic target

The actual reduced-norm completion and the concrete reduced group C⋆-algebra
are equipped with their canonical spectral orders. Their already verified
star-algebra equivalence induces the comparison on projection classes and K₀.
No countability assumption, computation of K₀, or assembly theorem is used.
-/

noncomputable section
namespace BC4lean
open OperatorKTheory

universe u
variable (Γ : Type u) [Group Γ]

local instance completionSpectralOrder : PartialOrder (ReducedCompletion Γ) :=
  CStarAlgebra.spectralOrder (ReducedCompletion Γ)

local instance completionSpectralOrderedRing : StarOrderedRing (ReducedCompletion Γ) :=
  CStarAlgebra.spectralOrderedRing (ReducedCompletion Γ)

local instance reducedSpectralOrder : PartialOrder (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)

local instance reducedSpectralOrderedRing : StarOrderedRing (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)

/-- Stable projection classes in the actual abstract reduced-norm completion. -/
def ReducedCompletionProjectionMonoid : Type _ := StableProjectionMonoid (ReducedCompletion Γ)

instance reducedCompletionProjectionAddCommMonoid :
    AddCommMonoid (ReducedCompletionProjectionMonoid Γ) :=
  inferInstanceAs (AddCommMonoid (StableProjectionMonoid (ReducedCompletion Γ)))

/-- K₀ of the abstract reduced-norm completion, using its canonical spectral order. -/
def ReducedCompletionK0 : Type _ := K0 (ReducedCompletion Γ)

instance reducedCompletionK0AddCommGroup : AddCommGroup (ReducedCompletionK0 Γ) :=
  inferInstanceAs (AddCommGroup (K0 (ReducedCompletion Γ)))

/-- The group-completion map for stable projection classes in the abstract model. -/
def reducedCompletionK0Class : ReducedCompletionProjectionMonoid Γ →+ ReducedCompletionK0 Γ :=
  k0Class

/-- Apply the canonical algebra comparison entrywise to a finite matrix projection. -/
def reducedCompletionProjectionMap (p : FiniteProjection (ReducedCompletion Γ)) :
    FiniteProjection (ReducedGroupCStar Γ) :=
  FiniteProjection.map (reducedCompletionEquiv Γ).toStarAlgHom p

@[simp] theorem reducedCompletionProjectionMap_entry (p : FiniteProjection (ReducedCompletion Γ))
    (i j : p.Index) :
    projectionMatrix (reducedCompletionProjectionMap Γ p).projection i j =
      reducedCompletionEquiv Γ (projectionMatrix p.projection i j) := rfl

/-- Canonical comparison of the stable projection monoids of the two models. -/
def reducedCompletionProjectionEquiv :
    ReducedCompletionProjectionMonoid Γ ≃+ ReducedProjectionMonoid Γ :=
  StableProjectionMonoid.mapEquiv (reducedCompletionEquiv Γ)

@[simp] theorem reducedCompletionProjectionEquiv_of (p : FiniteProjection (ReducedCompletion Γ)) :
    reducedCompletionProjectionEquiv Γ (StableProjectionMonoid.of p) =
      StableProjectionMonoid.of (reducedCompletionProjectionMap Γ p) :=
  StableProjectionMonoid.mapEquiv_of (reducedCompletionEquiv Γ) p

@[simp] theorem reducedCompletionProjectionEquiv_symm_of
    (p : FiniteProjection (ReducedGroupCStar Γ)) :
    (reducedCompletionProjectionEquiv Γ).symm (StableProjectionMonoid.of p) =
      StableProjectionMonoid.of
        (FiniteProjection.map (reducedCompletionEquiv Γ).symm.toStarAlgHom p) := rfl

/-- The abstract completion gives canonically the same degree-zero analytic target. -/
def reducedCompletionK0Equiv : ReducedCompletionK0 Γ ≃+ ReducedK0 Γ :=
  k0Equiv (reducedCompletionEquiv Γ)

@[simp] theorem reducedCompletionK0Equiv_class (x : ReducedCompletionProjectionMonoid Γ) :
    reducedCompletionK0Equiv Γ (reducedCompletionK0Class Γ x) =
      reducedK0Class Γ (reducedCompletionProjectionEquiv Γ x) :=
  k0Equiv_class (reducedCompletionEquiv Γ) x

@[simp] theorem reducedCompletionK0Equiv_symm_class (x : ReducedProjectionMonoid Γ) :
    (reducedCompletionK0Equiv Γ).symm (reducedK0Class Γ x) =
      reducedCompletionK0Class Γ ((reducedCompletionProjectionEquiv Γ).symm x) :=
  k0Equiv_class (reducedCompletionEquiv Γ).symm x

/-- Naturality of group completion for the abstract/concrete comparison. -/
theorem reducedCompletionK0Equiv_comp_class :
    (reducedCompletionK0Equiv Γ).toAddMonoidHom.comp (reducedCompletionK0Class Γ) =
      (reducedK0Class Γ).comp (reducedCompletionProjectionEquiv Γ).toAddMonoidHom := by
  ext x
  exact reducedCompletionK0Equiv_class Γ x

@[simp] theorem reducedCompletionK0Equiv_projection (p : FiniteProjection (ReducedCompletion Γ)) :
    reducedCompletionK0Equiv Γ (reducedCompletionK0Class Γ (StableProjectionMonoid.of p)) =
      reducedK0Class Γ (StableProjectionMonoid.of (reducedCompletionProjectionMap Γ p)) :=
  k0Equiv_projection (reducedCompletionEquiv Γ) p

/-- The comparison is uniquely determined by compatibility with projection classes. -/
theorem reducedCompletionK0Equiv_unique (f : ReducedCompletionK0 Γ →+ ReducedK0 Γ)
    (h : f.comp (reducedCompletionK0Class Γ) =
      (reducedK0Class Γ).comp (reducedCompletionProjectionEquiv Γ).toAddMonoidHom) :
    (reducedCompletionK0Equiv Γ).toAddMonoidHom = f := by
  apply k0Hom_ext
  intro p
  exact (reducedCompletionK0Equiv_class Γ (StableProjectionMonoid.of p)).trans
    (DFunLike.congr_fun h (StableProjectionMonoid.of p)).symm

end BC4lean
