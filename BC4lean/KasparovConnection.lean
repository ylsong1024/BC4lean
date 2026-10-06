import BC4lean.ModuleCreationMap
import BC4lean.InteriorModuleTensor
import BC4lean.KasparovCycle

/-! # Connections on the actual interior tensor

For the odd operator of a genuine second Kasparov cycle, a connection satisfies
the two localized compactness conditions on every homogeneous first-module
vector, including the condition involving adjoints. The creation maps here are
the actual bounded adjointable maps into the constructed interior tensor; they
are not assumed compact. This definition and its compact-perturbation law do
not assume existence of a Kasparov product.
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

/-- The exact odd-operator connection conditions, split into the two homogeneous degrees. -/
structure KasparovConnection (c : KasparovCycle α β E) (d : KasparovCycle β γ F)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) : Prop where
  even (ξ : E) (hξ : c.grading.grading ξ = ξ) :
    IsModuleCompact ((moduleCreationMap d.representation ξ).comp d.operator -
      R.comp (moduleCreationMap d.representation ξ))
  even_adjoint (ξ : E) (hξ : c.grading.grading ξ = ξ) :
    IsModuleCompact ((moduleCreationMap d.representation ξ).comp (star d.operator) -
      (star R).comp (moduleCreationMap d.representation ξ))
  odd (ξ : E) (hξ : c.grading.grading ξ = -ξ) :
    IsModuleCompact ((moduleCreationMap d.representation ξ).comp d.operator +
      R.comp (moduleCreationMap d.representation ξ))
  odd_adjoint (ξ : E) (hξ : c.grading.grading ξ = -ξ) :
    IsModuleCompact ((moduleCreationMap d.representation ξ).comp (star d.operator) +
      (star R).comp (moduleCreationMap d.representation ξ))

namespace KasparovConnection

variable {c : KasparovCycle α β E} {d : KasparovCycle β γ F}
  {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}

/-- A globally compact change of the connection preserves every homogeneous condition. -/
theorem add_compact (hR : KasparovConnection c d R)
    (K : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (hK : IsModuleCompact K) :
    KasparovConnection c d (R + K) where
  even ξ hξ := by
    have heq : (moduleCreationMap d.representation ξ).comp d.operator -
        (R + K).comp (moduleCreationMap d.representation ξ) =
        ((moduleCreationMap d.representation ξ).comp d.operator -
          R.comp (moduleCreationMap d.representation ξ)) -
        K.comp (moduleCreationMap d.representation ξ) := by
      ext y
      simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply,
        AdjointableMap.coe_add_apply]
      abel
    rw [heq]
    exact (hR.even ξ hξ).sub (hK.comp_right _)
  even_adjoint ξ hξ := by
    have heq : (moduleCreationMap d.representation ξ).comp (star d.operator) -
        (star (R + K)).comp (moduleCreationMap d.representation ξ) =
        ((moduleCreationMap d.representation ξ).comp (star d.operator) -
          (star R).comp (moduleCreationMap d.representation ξ)) -
        (star K).comp (moduleCreationMap d.representation ξ) := by
      rw [star_add]
      ext y
      simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply,
        AdjointableMap.coe_add_apply]
      abel
    rw [heq]
    exact (hR.even_adjoint ξ hξ).sub (hK.adjoint.comp_right _)
  odd ξ hξ := by
    have heq : (moduleCreationMap d.representation ξ).comp d.operator +
        (R + K).comp (moduleCreationMap d.representation ξ) =
        ((moduleCreationMap d.representation ξ).comp d.operator +
          R.comp (moduleCreationMap d.representation ξ)) +
        K.comp (moduleCreationMap d.representation ξ) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply]
      abel
    rw [heq]
    exact (hR.odd ξ hξ).add (hK.comp_right _)
  odd_adjoint ξ hξ := by
    have heq : (moduleCreationMap d.representation ξ).comp (star d.operator) +
        (star (R + K)).comp (moduleCreationMap d.representation ξ) =
        ((moduleCreationMap d.representation ξ).comp (star d.operator) +
          (star R).comp (moduleCreationMap d.representation ξ)) +
        (star K).comp (moduleCreationMap d.representation ξ) := by
      rw [star_add]
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply]
      abel
    rw [heq]
    exact (hR.odd_adjoint ξ hξ).add (hK.adjoint.comp_right _)

end KasparovConnection
end BC4lean.KKTheory
