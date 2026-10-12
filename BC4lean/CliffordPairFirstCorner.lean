import BC4lean.CliffordCycleIso
import BC4lean.EssentialModulePositivityFibre

/-! # The genuine first corner of a product-coefficient module map

Restriction to the actual first coefficient ranges is followed by the
whole first-coordinate range unitaries. The resulting rectangular map
preserves adjoints and compositions and takes genuine compact maps to
compact maps. Positive lifts pass through its actual endomorphism star
homomorphism using the proved star-square characterization.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

def cliffordPairFirstCorner
    (T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) :
    AdjointableMap B E F :=
  (cliffordPairFirstRangeEquiv (B := B) (E := E)).transportMap
    (cliffordPairFirstRangeEquiv (B := B) (E := F)) (cliffordRangeRestriction true T)

@[simp] theorem cliffordPairFirstCorner_apply
    (T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) (x : E) :
    cliffordPairFirstCorner T x = (T (cliffordPairMk x 0)).1 := rfl

@[simp] theorem cliffordPairFirstCorner_pair (S T : AdjointableMap B E F) :
    cliffordPairFirstCorner (cliffordPairMap S T) = S := by ext x; rfl

@[simp] theorem cliffordPairFirstCorner_add
    (S T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) :
    cliffordPairFirstCorner (S + T) = cliffordPairFirstCorner S + cliffordPairFirstCorner T := by
  ext x
  rfl

@[simp] theorem cliffordPairFirstCorner_sub
    (S T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) :
    cliffordPairFirstCorner (S - T) = cliffordPairFirstCorner S - cliffordPairFirstCorner T := by
  ext x
  rfl

@[simp] theorem cliffordPairFirstCorner_comp
    (S : AdjointableMap (B × B) (CliffordPairModule B F) (CliffordPairModule B G))
    (T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) :
    cliffordPairFirstCorner (S.comp T) = (cliffordPairFirstCorner S).comp (cliffordPairFirstCorner T) := by
  ext x
  simp only [cliffordPairFirstCorner, cliffordRangeRestriction_comp,
    HilbertModuleEquiv.transportMap_apply, AdjointableMap.comp_apply,
    HilbertModuleEquiv.symm_apply_apply]

@[simp] theorem cliffordPairFirstCorner_adjoint
    (T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B F)) :
    cliffordPairFirstCorner T.adjoint = (cliffordPairFirstCorner T).adjoint := by
  simp only [cliffordPairFirstCorner, HilbertModuleEquiv.transportMap_adjoint,
    cliffordRangeRestriction_adjoint]

theorem cliffordPairFirstCorner_isModuleCompact
    {T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B F)}
    (hT : IsModuleCompact T) : IsModuleCompact (cliffordPairFirstCorner T) :=
  HilbertModuleEquiv.transportMap_isModuleCompact _ _ (cliffordRangeRestriction_isModuleCompact true hT)

def cliffordPairFirstCornerHom :
    AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B E) →⋆ₐ[ℂ]
      AdjointableMap B E E :=
  (cliffordPairFirstRangeEquiv (B := B) (E := E)).transportStarAlgEquiv.toStarAlgHom.comp
    (cliffordRangeRestrictionHom true)

@[simp] theorem cliffordPairFirstCornerHom_apply
    (T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B E)) :
    cliffordPairFirstCornerHom T = cliffordPairFirstCorner T := rfl

@[simp] theorem cliffordPairFirstCorner_star
    (T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B E)) :
    cliffordPairFirstCorner (star T) = star (cliffordPairFirstCorner T) :=
  cliffordPairFirstCorner_adjoint T

theorem IsPositiveModuloModuleCompact.cliffordPairFirstCorner
    {T : AdjointableMap (B × B) (CliffordPairModule B E) (CliffordPairModule B E)}
    (hT : IsPositiveModuloModuleCompact T) :
    IsPositiveModuloModuleCompact (cliffordPairFirstCorner T) := by
  obtain ⟨V, hV⟩ := hT.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).2
  refine ⟨BC4lean.KKTheory.cliffordPairFirstCorner V, ?_⟩
  have h := cliffordPairFirstCorner_isModuleCompact hV
  change IsModuleCompact (cliffordPairFirstCornerHom (T - star V * V)) at h
  simpa only [map_sub, map_mul, map_star, cliffordPairFirstCornerHom_apply] using h

end BC4lean.KKTheory
