import BC4lean.RelativeProjectionTransport

/-! # Actual relative-cycle transport with named target projections

Whole ambient intertwining determines the transported projections. The
existing true supported-range transport then gives a whole-cycle unitary
with the named target projections and their independently proved defects.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

def relativeProjectionIntertwiningCycleIso (U : HilbertModuleEquiv B E F)
    (P Q : AdjointableMap B E E) (P' Q' : AdjointableMap B F F)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hP' : IsStarProjection P') (hQ' : IsStarProjection Q')
    (hc : IsModuleCompact (P - Q)) (hc' : IsModuleCompact (P' - Q'))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hUP : ∀ x, U (P x) = P' (U x)) (hUQ : ∀ x, U (Q x) = Q' (U x)) :
    KasparovCycleIso (relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE)
      (relativeProjectionCycle (Γ := Γ) P' Q' hP' hQ' hc' hF) := by
  have hp : U.transport P = P' := by
    ext x
    change U (P (U.symm x)) = P' x
    rw [hUP, U.apply_symm_apply]
  have hq : U.transport Q = Q' := by
    ext x
    change U (Q (U.symm x)) = Q' x
    rw [hUQ, U.apply_symm_apply]
  subst P'
  subst Q'
  exact relativeProjectionTransportCycleIso (Γ := Γ) U P Q hP hQ hc hE

end BC4lean.KKTheory
