import BC4lean.HilbertModuleJuliaUnitary
import BC4lean.AdjointableComplete
import BC4lean.InjectiveStarHomPositivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Tactic.NoncommRing

/-! # Actual square-root Julia unitary of a contractive module map

The diagonal sum is an injective star homomorphism of the complete operator
algebras. Positivity reflection proves that both rectangular adjoint squares
are positive in their actual spectral orders. Their contractive norm bounds
give positive defects. The square roots D=√(1−TT*) and S=√(1−T*T) are then
constructed by the continuous functional calculus. In the linking direct-sum
algebra, √(1−L²)=diag(D,S) commutes with L=[0 T; T* 0]. Its rectangular entry
is exactly DT=TS. Thus the finite Julia unitary is constructed from T itself.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardHilbertModuleJuliaSqrtLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardHilbertModuleJuliaSqrtLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance standardHilbertModuleJuliaSqrtLocalInstance03 : PartialOrder (AdjointableMap B F F) := CStarAlgebra.spectralOrder _
local instance standardHilbertModuleJuliaSqrtLocalInstance04 : StarOrderedRing (AdjointableMap B F F) := CStarAlgebra.spectralOrderedRing _
local instance standardHilbertModuleJuliaSqrtLocalInstance05 : PartialOrder (AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) :=
  CStarAlgebra.spectralOrder _
local instance standardHilbertModuleJuliaSqrtLocalInstance06 : StarOrderedRing (AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) :=
  CStarAlgebra.spectralOrderedRing _

/-- The actual diagonal star homomorphism, with the ordinary product norm only
on its parameter algebra. -/
def sumMapStarAlgHom : (AdjointableMap B E E × AdjointableMap B F F) →⋆ₐ[ℂ]
    AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) where
  toFun p := sumMap p.1 p.2
  map_zero' := sumMap_zero
  map_one' := sumMap_one
  map_add' p q := sumMap_add p.1 q.1 p.2 q.2
  map_mul' p q := sumMap_mul p.1 q.1 p.2 q.2
  map_star' p := sumMap_star p.1 p.2
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change sumMap (c • 1) (c • 1) = c • 1
    rw [sumMap_smul, sumMap_one]

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem sumMapStarAlgHom_apply (D : AdjointableMap B E E) (S : AdjointableMap B F F) :
    sumMapStarAlgHom (D, S) = sumMap D S := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem sumMapStarAlgHom_injective : Function.Injective (sumMapStarAlgHom (B := B) (E := E) (F := F)) := by
  intro p q h
  apply Prod.ext
  · ext x
    have hv := congrArg (fun R => (R (sumMk (B := B) x (0 : F))).fst) h
    change (sumMap p.1 p.2 (sumMk (B := B) x (0 : F))).fst =
      (sumMap q.1 q.2 (sumMk (B := B) x (0 : F))).fst at hv
    simpa only [sumMapStarAlgHom_apply, sumMap_apply, sumMk_fst, sumMk_snd] using hv
  · ext x
    have hv := congrArg (fun R => (R (sumMk (B := B) (0 : E) x)).snd) h
    change (sumMap p.1 p.2 (sumMk (B := B) (0 : E) x)).snd =
      (sumMap q.1 q.2 (sumMk (B := B) (0 : E) x)).snd at hv
    simpa only [sumMapStarAlgHom_apply, sumMap_apply, sumMk_fst, sumMk_snd] using hv

/-- The selfadjoint rectangular linking operator on the genuine direct sum. -/
def moduleLinkingOperator (T : AdjointableMap B F E) :
    AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) :=
  (sumInl.comp T).comp sumSnd + (sumInr.comp T.adjoint).comp sumFst

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem moduleLinkingOperator_apply (T : AdjointableMap B F E) (x : HilbertModuleSum B E F) :
    moduleLinkingOperator T x = sumMk (T x.snd) (T.adjoint x.fst) := by
  simp only [moduleLinkingOperator, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
    sumInl_apply, sumInr_apply, sumFst_apply, sumSnd_apply]
  apply Prod.ext <;> simp

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem moduleLinkingOperator_star (T : AdjointableMap B F E) :
    star (moduleLinkingOperator T) = moduleLinkingOperator T := by
  ext x
  change ((0 : E), T.adjoint x.fst) + (T x.snd, (0 : F)) =
    (T x.snd, (0 : F)) + ((0 : E), T.adjoint x.fst)
  simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem moduleLinkingOperator_square (T : AdjointableMap B F E) :
    moduleLinkingOperator T * moduleLinkingOperator T = sumMap (T.comp T.adjoint) (T.adjoint.comp T) := by
  ext x
  simp only [AdjointableMap.mul_apply, moduleLinkingOperator_apply, sumMap_apply,
    sumMk_fst, sumMk_snd, AdjointableMap.comp_apply]

/-- Both rectangular adjoint squares are actually positive in the corresponding
complete endomorphism C*-algebras. -/
theorem rectangular_adjoint_squares_nonneg (T : AdjointableMap B F E) :
    0 ≤ T.comp T.adjoint ∧ 0 ≤ T.adjoint.comp T := by
  have hl : 0 ≤ moduleLinkingOperator T * moduleLinkingOperator T := by
    simpa only [moduleLinkingOperator_star] using star_mul_self_nonneg (moduleLinkingOperator T)
  rw [moduleLinkingOperator_square] at hl
  have hp := (injectiveStarHom_nonneg_iff
    (sumMapStarAlgHom (B := B) (E := E) (F := F)).toNonUnitalStarAlgHom
    sumMapStarAlgHom_injective (T.comp T.adjoint, T.adjoint.comp T)).mp hl
  exact hp

/-- A contractive rectangular map has positive target square defect. -/
theorem one_sub_self_comp_adjoint_nonneg (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    0 ≤ 1 - T.comp T.adjoint := by
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (rectangular_adjoint_squares_nonneg T).1).mp
  change ‖(T.comp T.adjoint).toCLM‖ ≤ 1
  rw [AdjointableMap.norm_toCLM_self_comp_adjoint]
  change ‖T‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg T]

/-- A contractive rectangular map has positive source square defect. -/
theorem one_sub_adjoint_comp_self_nonneg (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    0 ≤ 1 - T.adjoint.comp T := by
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (rectangular_adjoint_squares_nonneg T).2).mp
  change ‖(T.adjoint.comp T).toCLM‖ ≤ 1
  rw [AdjointableMap.norm_toCLM_adjoint_comp_self]
  change ‖T‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg T]

/-- The actual target defect square root. -/
def juliaTargetDefect (T : AdjointableMap B F E) : AdjointableMap B E E :=
  CFC.sqrt (1 - T.comp T.adjoint)

/-- The actual source defect square root. -/
def juliaSourceDefect (T : AdjointableMap B F E) : AdjointableMap B F F :=
  CFC.sqrt (1 - T.adjoint.comp T)

omit [CompleteSpace F] in
theorem juliaTargetDefect_nonneg (T : AdjointableMap B F E) : 0 ≤ juliaTargetDefect T := CFC.sqrt_nonneg _
omit [CompleteSpace E] in
theorem juliaSourceDefect_nonneg (T : AdjointableMap B F E) : 0 ≤ juliaSourceDefect T := CFC.sqrt_nonneg _

omit [CompleteSpace F] in
@[simp] theorem juliaTargetDefect_adjoint (T : AdjointableMap B F E) :
    (juliaTargetDefect T).adjoint = juliaTargetDefect T :=
  (juliaTargetDefect_nonneg T).isSelfAdjoint.star_eq

omit [CompleteSpace E] in
@[simp] theorem juliaSourceDefect_adjoint (T : AdjointableMap B F E) :
    (juliaSourceDefect T).adjoint = juliaSourceDefect T :=
  (juliaSourceDefect_nonneg T).isSelfAdjoint.star_eq

theorem juliaTargetDefect_square (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    juliaTargetDefect T * juliaTargetDefect T + T.comp T.adjoint = 1 := by
  rw [juliaTargetDefect, CFC.sqrt_mul_sqrt_self _ (one_sub_self_comp_adjoint_nonneg T hT)]
  abel

theorem juliaSourceDefect_square (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    juliaSourceDefect T * juliaSourceDefect T + T.adjoint.comp T = 1 := by
  rw [juliaSourceDefect, CFC.sqrt_mul_sqrt_self _ (one_sub_adjoint_comp_self_nonneg T hT)]
  abel

set_option maxHeartbeats 500000 in
/-- The linking square root is the diagonal of the two actual defect roots. -/
theorem julia_linking_defect_sqrt (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    CFC.sqrt (1 - moduleLinkingOperator T * moduleLinkingOperator T) =
      sumMap (juliaTargetDefect T) (juliaSourceDefect T) := by
  apply CFC.sqrt_unique
  · rw [← sumMap_mul]
    have hD : juliaTargetDefect T * juliaTargetDefect T = 1 - T.comp T.adjoint :=
      CFC.sqrt_mul_sqrt_self _ (one_sub_self_comp_adjoint_nonneg T hT)
    have hS : juliaSourceDefect T * juliaSourceDefect T = 1 - T.adjoint.comp T :=
      CFC.sqrt_mul_sqrt_self _ (one_sub_adjoint_comp_self_nonneg T hT)
    rw [hD, hS, sumMap_sub, sumMap_one, moduleLinkingOperator_square]
  · exact (injectiveStarHom_nonneg_iff
      (sumMapStarAlgHom (B := B) (E := E) (F := F)).toNonUnitalStarAlgHom
      sumMapStarAlgHom_injective (juliaTargetDefect T, juliaSourceDefect T)).mpr
        ⟨juliaTargetDefect_nonneg T, juliaSourceDefect_nonneg T⟩

/-- Functional calculus proves the exact rectangular square-root intertwiner. -/
theorem juliaDefect_intertwine (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    (juliaTargetDefect T).comp T = T.comp (juliaSourceDefect T) := by
  have hc : Commute (1 - moduleLinkingOperator T * moduleLinkingOperator T) (moduleLinkingOperator T) := by
    change (1 - moduleLinkingOperator T * moduleLinkingOperator T) * moduleLinkingOperator T =
      moduleLinkingOperator T * (1 - moduleLinkingOperator T * moduleLinkingOperator T)
    noncomm_ring
  have hs := hc.cfcₙ_nnreal NNReal.sqrt
  change Commute (CFC.sqrt (1 - moduleLinkingOperator T * moduleLinkingOperator T))
    (moduleLinkingOperator T) at hs
  rw [julia_linking_defect_sqrt T hT] at hs
  ext y
  have hv := congrArg (fun R => (R (sumMk (B := B) (0 : E) y)).fst) hs.eq
  simpa only [AdjointableMap.mul_apply, sumMap_apply, moduleLinkingOperator_apply,
    sumMk_fst, sumMk_snd, AdjointableMap.comp_apply] using hv

/-- A contractive adjointable rectangular map supplies its actual Julia unitary,
with no square-root identities assumed as extra data. -/
def contractiveJuliaEquiv (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1) :
    HilbertModuleEquiv B (HilbertModuleSum B E F) (HilbertModuleSum B E F) :=
  juliaBlockEquiv T (juliaTargetDefect T) (juliaSourceDefect T)
    (juliaTargetDefect_adjoint T) (juliaSourceDefect_adjoint T)
    (juliaTargetDefect_square T hT) (juliaSourceDefect_square T hT) (juliaDefect_intertwine T hT)

@[simp] theorem contractiveJuliaEquiv_apply (T : AdjointableMap B F E) (hT : ‖T‖ ≤ 1)
    (x : HilbertModuleSum B E F) :
    contractiveJuliaEquiv T hT x =
      sumMk (juliaTargetDefect T x.fst + T x.snd)
        (-T.adjoint x.fst + juliaSourceDefect T x.snd) :=
  juliaBlock_apply _ _ _ _

end BC4lean.KKTheory
