import BC4lean.ReducedGroupCStar

/-! # The reduced group C⋆-algebra of a trivial group -/

noncomputable section

namespace BC4lean

variable {Γ : Type*} [Group Γ] [Subsingleton Γ]

theorem reducedAlgebra_le_scalars :
    reducedAlgebra Γ ≤ (StarAlgHom.ofId ℂ (L2Group Γ →L[ℂ] L2Group Γ)).range := by
  apply reducedAlgebra_minimal
  · exact (algebraMap_isometry (𝕜 := ℂ) (𝕜' := L2Group Γ →L[ℂ] L2Group Γ)).isClosedEmbedding.isClosed_range
  · intro g
    refine ⟨1, ?_⟩
    rw [Subsingleton.elim g 1, regularOperator_one]
    exact map_one _

theorem scalarToReduced_surjective :
    Function.Surjective (StarAlgHom.ofId ℂ (ReducedGroupCStar Γ)) := by
  intro T
  obtain ⟨z, hz⟩ := reducedAlgebra_le_scalars T.property
  refine ⟨z, Subtype.ext ?_⟩
  exact hz

/-- Canonical scalar identification for any group with one element. -/
def trivialReducedEquiv : ℂ ≃⋆ₐ[ℂ] ReducedGroupCStar Γ :=
  StarAlgEquiv.ofBijective (StarAlgHom.ofId ℂ (ReducedGroupCStar Γ))
    ⟨(algebraMap_isometry (𝕜 := ℂ) (𝕜' := ReducedGroupCStar Γ)).injective,
      scalarToReduced_surjective⟩

@[simp] theorem trivialReducedEquiv_apply (z : ℂ) :
    trivialReducedEquiv (Γ := Γ) z = algebraMap ℂ (ReducedGroupCStar Γ) z := rfl

theorem trivialReducedEquiv_isometry : Isometry (trivialReducedEquiv (Γ := Γ)) :=
  algebraMap_isometry ℂ (ReducedGroupCStar Γ)

end BC4lean
