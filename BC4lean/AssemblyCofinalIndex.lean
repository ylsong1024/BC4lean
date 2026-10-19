import BC4lean.AssemblyColimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Assembly and actual cofinal indexing comparisons

The restricted homomorphism uses the same actual piece assembly family.
Reindexing compatibility requires a monotone indexing map. Identifying its
colimit with the full topological group additionally retains the genuine
cofinal upper-bound hypothesis from Chapter 6.

-/

noncomputable section
universe uΓ uX uJ uL
namespace BC4lean.Assembly
open ProperActions

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]
  {J : Type uJ} [Preorder J] [Nonempty J] [IsDirectedOrder J]

/-- The actual compatible family on a monotone indexing restriction. -/
def indexedAssemblyHom (p : Bool) (φ : J →o CocompactPiece Γ X) :
    ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).Colimit →+
      analyticGroup Γ p :=
  ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).desc
    (fun j => pieceAssemblyHom Γ X p (φ j))
    (fun _ _ hij x => pieceAssemblyHom_transition Γ X p (φ.monotone hij) x)

@[simp] theorem indexedAssemblyHom_of (p : Bool) (φ : J →o CocompactPiece Γ X)
    (j : J) (x : TopologicalKHomology.pieceGroup p (φ j)) :
    indexedAssemblyHom Γ X p φ
      (((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).of j x) =
      pieceAssemblyHom Γ X p (φ j) x := rfl

/-- Reindexing is compatible with the actual constructed assembly map. -/
theorem assemblyHom_reindex (p : Bool) (φ : J →o CocompactPiece Γ X)
    (x : ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).Colimit) :
    assemblyHom Γ X p
        ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).reindex φ x) =
      indexedAssemblyHom Γ X p φ x := by
  obtain ⟨j, y, rfl⟩ :=
    ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).exists_of x
  rfl

/-- Actual indexing independence retains cofinality, rather than mere
pointwise covering of the ambient proper space. -/
theorem assemblyHom_cofinalIndexEquiv (p : Bool) (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j)
    (x : ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).Colimit) :
    assemblyHom Γ X p (TopologicalKHomology.cofinalIndexEquiv p φ hφ x) =
      indexedAssemblyHom Γ X p φ x :=
  assemblyHom_reindex Γ X p φ x

variable {L : Type uL} [Preorder L] [Nonempty L] [IsDirectedOrder L]

/-- Two genuinely cofinal restricted systems give the same assembly value
under Chapter 6's actual additive colimit comparison equivalence. -/
theorem indexedAssemblyHom_cofinalComparisonEquiv (p : Bool)
    (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) (hψ : ∀ S, ∃ j, S ≤ ψ j)
    (x : ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).restrict φ).Colimit) :
    indexedAssemblyHom Γ X p ψ
        ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalComparisonEquiv
          φ ψ hφ hψ x) = indexedAssemblyHom Γ X p φ x := by
  rw [← assemblyHom_cofinalIndexEquiv Γ X p ψ hψ]
  change assemblyHom Γ X p
      ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalEquiv ψ hψ
        (((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalEquiv ψ hψ).symm
          ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalEquiv φ hφ x))) = _
  rw [AddEquiv.apply_symm_apply]
  exact assemblyHom_cofinalIndexEquiv Γ X p φ hφ x

end BC4lean.Assembly
