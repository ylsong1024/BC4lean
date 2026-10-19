import BC4lean.AssemblyColimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Exact cocompact-piece criteria for the actual assembly map

These equivalences identify the separate mathematical conditions needed for
assembly bijectivity. They do not assert either condition for a group. They
use the actual assembly restriction formula and the existing colimit's
representative and eventual-equality theorems.
-/

universe uΓ uX
namespace BC4lean.Assembly
open ProperActions

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

/-- Assembly is surjective exactly when each analytic class is the actual
assembly value of a class on some cocompact piece. -/
theorem assemblyHom_surjective_iff_pieceImages (p : Bool) :
    Function.Surjective (assemblyHom Γ X p) ↔
      ∀ y : analyticGroup Γ p,
        ∃ (S : CocompactPiece Γ X) (x : TopologicalKHomology.pieceGroup p S),
          pieceAssemblyHom Γ X p S x = y := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h y
    obtain ⟨S, x, rfl⟩ :=
      (TopologicalKHomology.diagram (Γ := Γ) (X := X) p).exists_of z
    change TopologicalKHomology.pieceGroup p S at x
    have hz' : assemblyHom Γ X p (TopologicalKHomology.ofPiece p S x) = y := hz
    exact ⟨S, x, (assemblyHom_ofPiece Γ X p S x).symm.trans hz'⟩
  · intro h y
    obtain ⟨S, x, hx⟩ := h y
    exact ⟨TopologicalKHomology.ofPiece p S x,
      (assemblyHom_ofPiece Γ X p S x).trans hx⟩

/-- Assembly is injective exactly when equal piece assembly values become
equal after transition to one common larger cocompact piece. -/
theorem assemblyHom_injective_iff_commonTransition (p : Bool) :
    Function.Injective (assemblyHom Γ X p) ↔
      ∀ (S T : CocompactPiece Γ X)
        (x : TopologicalKHomology.pieceGroup p S)
        (y : TopologicalKHomology.pieceGroup p T),
        pieceAssemblyHom Γ X p S x = pieceAssemblyHom Γ X p T y →
          ∃ (U : CocompactPiece Γ X) (hSU : S ≤ U) (hTU : T ≤ U),
            TopologicalKHomology.transition p hSU x =
              TopologicalKHomology.transition p hTU y := by
  constructor
  · intro h S T x y hxy
    apply (TopologicalKHomology.ofPiece_eq_iff p x y).mp
    apply h
    rw [assemblyHom_ofPiece, assemblyHom_ofPiece]
    exact hxy
  · intro h z w hzw
    obtain ⟨S, x, rfl⟩ :=
      (TopologicalKHomology.diagram (Γ := Γ) (X := X) p).exists_of z
    obtain ⟨T, y, rfl⟩ :=
      (TopologicalKHomology.diagram (Γ := Γ) (X := X) p).exists_of w
    change TopologicalKHomology.pieceGroup p S at x
    change TopologicalKHomology.pieceGroup p T at y
    change assemblyHom Γ X p (TopologicalKHomology.ofPiece p S x) =
      assemblyHom Γ X p (TopologicalKHomology.ofPiece p T y) at hzw
    rw [assemblyHom_ofPiece, assemblyHom_ofPiece] at hzw
    exact (TopologicalKHomology.ofPiece_eq_iff p x y).mpr (h S T x y hzw)

/-- Exact piecewise reformulation of assembly bijectivity. Neither component
is asserted by this equivalence. -/
theorem assemblyHom_bijective_iff_pieceCriteria (p : Bool) :
    Function.Bijective (assemblyHom Γ X p) ↔
      (∀ (S T : CocompactPiece Γ X)
        (x : TopologicalKHomology.pieceGroup p S)
        (y : TopologicalKHomology.pieceGroup p T),
        pieceAssemblyHom Γ X p S x = pieceAssemblyHom Γ X p T y →
          ∃ (U : CocompactPiece Γ X) (hSU : S ≤ U) (hTU : T ≤ U),
            TopologicalKHomology.transition p hSU x =
              TopologicalKHomology.transition p hTU y) ∧
      (∀ y : analyticGroup Γ p,
        ∃ (S : CocompactPiece Γ X) (x : TopologicalKHomology.pieceGroup p S),
          pieceAssemblyHom Γ X p S x = y) :=
  and_congr (assemblyHom_injective_iff_commonTransition Γ X p)
    (assemblyHom_surjective_iff_pieceImages Γ X p)

end BC4lean.Assembly
