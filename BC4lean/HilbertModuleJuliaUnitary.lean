import BC4lean.HilbertModuleSum
import BC4lean.HilbertModuleEquiv

/-! # The finite Julia block unitary in Hilbert-module stabilization

The block operator [D T; -T* S] is an actual coefficient-inner-preserving unitary
when the displayed selfadjoint square-defect and intertwining identities hold.
This algebraic result does not assume surjectivity of T. Constructing D and S
by functional calculus, proving the strong vanishing of iterated residuals,
and completing the countable block construction remain separate obligations
for stabilization.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The actual finite Julia operator on the genuine coefficient-normed direct sum. -/
def juliaBlock (T : AdjointableMap B F E) (D : AdjointableMap B E E) (S : AdjointableMap B F F) :
    AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) :=
  sumMap D S + (sumInl.comp T).comp sumSnd - (sumInr.comp T.adjoint).comp sumFst

@[simp] theorem juliaBlock_apply (T : AdjointableMap B F E)
    (D : AdjointableMap B E E) (S : AdjointableMap B F F) (x : HilbertModuleSum B E F) :
    juliaBlock T D S x = sumMk (D x.fst + T x.snd) (-T.adjoint x.fst + S x.snd) := by
  simp only [juliaBlock, AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply,
    sumMap_apply, AdjointableMap.comp_apply, sumInl_apply, sumInr_apply,
    sumFst_apply, sumSnd_apply]
  apply Prod.ext <;> simp
  abel

@[simp] theorem juliaBlock_adjoint_apply (T : AdjointableMap B F E)
    (D : AdjointableMap B E E) (S : AdjointableMap B F F) (x : HilbertModuleSum B E F) :
    (juliaBlock T D S).adjoint x =
      sumMk (D.adjoint x.fst - T x.snd) (T.adjoint x.fst + S.adjoint x.snd) := by
  have hAdj : (juliaBlock T D S).adjoint = sumMap D.adjoint S.adjoint +
      (sumInr.comp T.adjoint).comp sumFst - (sumInl.comp T).comp sumSnd := by
    change star (juliaBlock T D S) = _
    simp only [juliaBlock, star_sub, star_add, AdjointableMap.star_eq_adjoint,
      sumMap_adjoint, AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint,
      sumInl_adjoint, sumInr_adjoint, sumFst_adjoint, sumSnd_adjoint,
      AdjointableMap.comp_assoc]
  rw [hAdj]
  simp only [AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply,
    sumMap_apply, AdjointableMap.comp_apply, sumInl_apply, sumInr_apply,
    sumFst_apply, sumSnd_apply]
  apply Prod.ext <;> simp
  abel

omit [StarOrderedRing B] in
/-- Taking the adjoint gives the second rectangular square-root intertwiner. -/
theorem julia_adjoint_intertwine (T : AdjointableMap B F E)
    (D : AdjointableMap B E E) (S : AdjointableMap B F F)
    (hD : D.adjoint = D) (hS : S.adjoint = S) (hT : D.comp T = T.comp S) :
    T.adjoint.comp D = S.comp T.adjoint := by
  have h := congrArg AdjointableMap.adjoint hT
  simpa only [AdjointableMap.adjoint_comp, hD, hS] using h

/-- The Julia operator has its actual adjoint as a left inverse. -/
theorem juliaBlock_adjoint_comp_self (T : AdjointableMap B F E)
    (D : AdjointableMap B E E) (S : AdjointableMap B F F)
    (hD : D.adjoint = D) (hS : S.adjoint = S)
    (hDE : D * D + T.comp T.adjoint = 1) (hSF : S * S + T.adjoint.comp T = 1)
    (hT : D.comp T = T.comp S) :
    (juliaBlock T D S).adjoint.comp (juliaBlock T D S) = AdjointableMap.id := by
  have hDv (x : E) : D (D x) + T (T.adjoint x) = x :=
    congrArg (fun R : AdjointableMap B E E => R x) hDE
  have hSv (x : F) : S (S x) + T.adjoint (T x) = x :=
    congrArg (fun R : AdjointableMap B F F => R x) hSF
  have hTv (x : F) : D (T x) = T (S x) :=
    congrArg (fun R : AdjointableMap B F E => R x) hT
  have hTav (x : E) : T.adjoint (D x) = S (T.adjoint x) :=
    congrArg (fun R : AdjointableMap B E F => R x) (julia_adjoint_intertwine T D S hD hS hT)
  ext x
  simp only [AdjointableMap.comp_apply, juliaBlock_apply, juliaBlock_adjoint_apply,
    sumMk_fst, sumMk_snd, hD, hS, AdjointableMap.id_apply]
  apply Prod.ext
  · change D (D x.fst + T x.snd) - T (-T.adjoint x.fst + S x.snd) = x.fst
    rw [D.toCLM.map_add, T.toCLM.map_add, T.toCLM.map_neg, hTv]
    calc
      _ = D (D x.fst) + T (T.adjoint x.fst) := by abel
      _ = x.fst := hDv x.fst
  · change T.adjoint (D x.fst + T x.snd) + S (-T.adjoint x.fst + S x.snd) = x.snd
    rw [T.adjoint.toCLM.map_add, S.toCLM.map_add, S.toCLM.map_neg, hTav]
    calc
      _ = S (S x.snd) + T.adjoint (T x.snd) := by abel
      _ = x.snd := hSv x.snd

/-- The Julia operator has its actual adjoint as a right inverse. -/
theorem juliaBlock_comp_adjoint (T : AdjointableMap B F E)
    (D : AdjointableMap B E E) (S : AdjointableMap B F F)
    (hD : D.adjoint = D) (hS : S.adjoint = S)
    (hDE : D * D + T.comp T.adjoint = 1) (hSF : S * S + T.adjoint.comp T = 1)
    (hT : D.comp T = T.comp S) :
    (juliaBlock T D S).comp (juliaBlock T D S).adjoint = AdjointableMap.id := by
  have hDv (x : E) : D (D x) + T (T.adjoint x) = x :=
    congrArg (fun R : AdjointableMap B E E => R x) hDE
  have hSv (x : F) : S (S x) + T.adjoint (T x) = x :=
    congrArg (fun R : AdjointableMap B F F => R x) hSF
  have hTv (x : F) : D (T x) = T (S x) :=
    congrArg (fun R : AdjointableMap B F E => R x) hT
  have hTav (x : E) : T.adjoint (D x) = S (T.adjoint x) :=
    congrArg (fun R : AdjointableMap B E F => R x) (julia_adjoint_intertwine T D S hD hS hT)
  ext x
  simp only [AdjointableMap.comp_apply, juliaBlock_apply, juliaBlock_adjoint_apply,
    sumMk_fst, sumMk_snd, hD, hS, AdjointableMap.id_apply]
  apply Prod.ext
  · change D (D x.fst - T x.snd) + T (T.adjoint x.fst + S x.snd) = x.fst
    rw [D.toCLM.map_sub, T.toCLM.map_add, hTv]
    calc
      _ = D (D x.fst) + T (T.adjoint x.fst) := by abel
      _ = x.fst := hDv x.fst
  · change -T.adjoint (D x.fst - T x.snd) + S (T.adjoint x.fst + S x.snd) = x.snd
    rw [T.adjoint.toCLM.map_sub, S.toCLM.map_add, hTav]
    calc
      _ = S (S x.snd) + T.adjoint (T x.snd) := by abel
      _ = x.snd := hSv x.snd

/-- Both inverse identities give a genuine Hilbert-module unitary. -/
def juliaBlockEquiv (T : AdjointableMap B F E)
    (D : AdjointableMap B E E) (S : AdjointableMap B F F)
    (hD : D.adjoint = D) (hS : S.adjoint = S)
    (hDE : D * D + T.comp T.adjoint = 1) (hSF : S * S + T.adjoint.comp T = 1)
    (hT : D.comp T = T.comp S) :
    HilbertModuleEquiv B (HilbertModuleSum B E F) (HilbertModuleSum B E F) := by
  have hinner (x y : HilbertModuleSum B E F) :
      ⟪juliaBlock T D S x, juliaBlock T D S y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
    rw [(juliaBlock T D S).adjoint_identity]
    change ⟪x, (juliaBlock T D S).adjoint (juliaBlock T D S y)⟫_(Bᵐᵒᵖ) = _
    have h := congrArg (fun R : AdjointableMap B (HilbertModuleSum B E F)
      (HilbertModuleSum B E F) => R y)
        (juliaBlock_adjoint_comp_self T D S hD hS hDE hSF hT)
    simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg
      (fun z : HilbertModuleSum B E F => ⟪x, z⟫_(Bᵐᵒᵖ)) h
  exact
    { linearIsometryEquiv :=
        { toLinearEquiv :=
            { toFun := juliaBlock T D S
              invFun := (juliaBlock T D S).adjoint
              left_inv := fun x => by
                simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
                  congrArg (fun R => R x) (juliaBlock_adjoint_comp_self T D S hD hS hDE hSF hT)
              right_inv := fun x => by
                simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
                  congrArg (fun R => R x) (juliaBlock_comp_adjoint T D S hD hS hDE hSF hT)
              map_add' := (juliaBlock T D S).toCLM.map_add
              map_smul' := (juliaBlock T D S).toCLM.map_smul }
          norm_map' x := by
            change ‖juliaBlock T D S x‖ = ‖x‖
            rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (juliaBlock T D S x), hinner]
            exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
      inner_map := hinner }

end BC4lean.KKTheory
