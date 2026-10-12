import BC4lean.StandardCountableModuleFibre
import BC4lean.HilbertModuleEquiv
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! # Actual standard endomorphism evaluation on completed coefficient fibres

The genuine radical-quotient fibre operator is transported through the
already constructed whole standard-module fibre unitary. This gives an
actual unital star algebra homomorphism into End(H_B), with norm and compact
ideal bounds. In particular evaluation commutes with the real completed
coordinate cutoff, rather than assuming a canonical fibre identification.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped CStarAlgebra

variable {B X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]

def standardCountableFibreOperatorHom (t : X) :
    AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B)) →⋆ₐ[ℂ]
    AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B) :=
  (standardCountableModuleFibreEquiv (B := B) t).transportStarAlgEquiv.toStarAlgHom.comp
    (hilbertModuleFibreOperatorHom (B := B)
      (M := StandardCountableHilbertModule C(X, B)) t)

theorem standardCountableFibreOperatorHom_apply (t : X)
    (T : AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B))) :
    standardCountableFibreOperatorHom t T =
      (standardCountableModuleFibreEquiv (B := B) t).transport
        (hilbertModuleFibreOperator (B := B) t T) := rfl

/-- The actual evaluated operator intertwines whole completed coefficient
evaluation, including vectors outside the canonical finite span. -/
theorem standardCountableFibreOperatorHom_evaluation (t : X)
    (T : AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B)))
    (x : StandardCountableHilbertModule C(X, B)) :
    standardCountableFibreOperatorHom t T (standardCountableCoefficientEvaluation t x) =
      standardCountableCoefficientEvaluation t (T x) := by
  let u : HilbertModuleEquiv B
      (HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t)
      (StandardCountableHilbertModule B) := standardCountableModuleFibreEquiv (B := B) t
  let Q : AdjointableMap B
      (HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t)
      (HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t) :=
    hilbertModuleFibreOperator (B := B) t T
  have hu (v : StandardCountableHilbertModule C(X, B)) :
      u (hilbertModuleFibreMk (B := B) t v) = standardCountableCoefficientEvaluation t v :=
    standardCountableModuleFibreEquiv_mk (B := B) t v
  have hinv : u.symm (standardCountableCoefficientEvaluation t x) =
      hilbertModuleFibreMk (B := B) t x := by
    calc
      _ = u.symm (u (hilbertModuleFibreMk (B := B) t x)) :=
        congrArg (fun y : StandardCountableHilbertModule B => u.symm y) (hu x).symm
      _ = _ := u.symm_apply_apply (hilbertModuleFibreMk (B := B) t x)
  calc
    standardCountableFibreOperatorHom t T (standardCountableCoefficientEvaluation t x) =
        u (Q (u.symm (standardCountableCoefficientEvaluation t x))) := by
      change u.transport Q (standardCountableCoefficientEvaluation t x) = _
      exact HilbertModuleEquiv.transport_apply u Q (standardCountableCoefficientEvaluation t x)
    _ = u (Q (hilbertModuleFibreMk (B := B) t x)) :=
      congrArg (fun v : HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t =>
        u (Q v)) hinv
    _ = u (hilbertModuleFibreMk (B := B) t (T x)) :=
      congrArg (fun v : HilbertModuleFibre B (StandardCountableHilbertModule C(X, B)) t =>
        u v) (hilbertModuleFibreOperator_mk (B := B) t T x)
    _ = standardCountableCoefficientEvaluation t (T x) := hu (T x)

theorem standardCountableFibreOperatorHom_norm_le (t : X)
    (T : AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B))) :
    ‖standardCountableFibreOperatorHom t T‖ ≤ ‖T‖ := by
  rw [standardCountableFibreOperatorHom_apply, HilbertModuleEquiv.transport_norm]
  exact hilbertModuleFibreOperator_norm_le t T

theorem standardCountableFibreOperatorHom_isModuleCompact (t : X)
    {T : AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B))} (hT : IsModuleCompact T) :
    IsModuleCompact (standardCountableFibreOperatorHom t T) :=
  (standardCountableModuleFibreEquiv (B := B) t).transportMap_isModuleCompact
    (standardCountableModuleFibreEquiv (B := B) t) (hT.fibre t)

@[simp] theorem standardCountableFibreOperatorHom_cutoff (t : X) (n : ℕ) :
    standardCountableFibreOperatorHom (B := B) t (standardCountableCutoff n) =
      standardCountableCutoff n := by
  ext y
  obtain ⟨x, rfl⟩ := standardCountableCoefficientEvaluation_surjective t y
  rw [standardCountableFibreOperatorHom_evaluation, standardCountableCoefficientEvaluation_cutoff]

@[simp] theorem standardCountableFibreOperatorHom_embedding (t : X) (e : ℕ ↪ ℕ) :
    standardCountableFibreOperatorHom (B := B) t (standardCountableEmbedding e) =
      standardCountableEmbedding e := by
  ext y
  obtain ⟨x, rfl⟩ := standardCountableCoefficientEvaluation_surjective t y
  rw [standardCountableFibreOperatorHom_evaluation, standardCountableCoefficientEvaluation_embedding]

@[simp] theorem standardCountableFibreOperatorHom_embedding_adjoint (t : X) (e : ℕ ↪ ℕ) :
    standardCountableFibreOperatorHom (B := B) t (standardCountableEmbedding e).adjoint =
      (standardCountableEmbedding e).adjoint := by
  change standardCountableFibreOperatorHom t (star (standardCountableEmbedding e)) = _
  rw [map_star, standardCountableFibreOperatorHom_embedding]
  rfl

theorem standardCountableFibreOperatorHom_isSelfAdjoint (t : X)
    {T : AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B))} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (standardCountableFibreOperatorHom t T) :=
  hT.map (standardCountableFibreOperatorHom t)

theorem standardCountableFibreOperatorHom_isStarProjection (t : X)
    {T : AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B))} (hT : IsStarProjection T) :
    IsStarProjection (standardCountableFibreOperatorHom t T) :=
  hT.map (standardCountableFibreOperatorHom t)

def standardCountableFibreUnitary (t : X)
    (U : unitary (AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B)))) :
    unitary (AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :=
  ⟨standardCountableFibreOperatorHom t (U : _),
    Unitary.map_mem (standardCountableFibreOperatorHom t) U.property⟩

theorem standardCountableFibreUnitary_sub_one_isModuleCompact (t : X)
    (U : unitary (AdjointableMap C(X, B) (StandardCountableHilbertModule C(X, B))
      (StandardCountableHilbertModule C(X, B))))
    (hU : IsModuleCompact ((U : AdjointableMap C(X, B)
      (StandardCountableHilbertModule C(X, B)) (StandardCountableHilbertModule C(X, B))) - 1)) :
    IsModuleCompact ((standardCountableFibreUnitary t U : AdjointableMap B
      (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) - 1) := by
  have h := standardCountableFibreOperatorHom_isModuleCompact t hU
  simpa only [map_sub, map_one, standardCountableFibreUnitary] using h

end BC4lean.KKTheory
