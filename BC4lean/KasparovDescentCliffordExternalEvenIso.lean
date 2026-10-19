import BC4lean.KasparovDescentCliffordExpansionIso
import BC4lean.KasparovDescentCliffordSignedSource
import BC4lean.CliffordExternalEvenCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual descent of the external even Clifford cycle



The external source is the genuine Koszul representation, whose two halves
involve the original module grading and its negative. The first-factor
operator homomorphism carries that grading to the actual descended grading;
the actual regular group operator commutes with it. These elementary identities
give equality of the two finite source representations and then of the
completed source representations by density. The same actual completed pair
unitary intertwines grading, ordinary group action, representation and F.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra
open CliffordExternalEvenRepresentation

variable {Γ A B E : Type*} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] in
theorem operatorHom_originalGrading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) :
    operatorHom β E J.toAdjointable = (ordinaryModuleGrading β J).toAdjointable := by
  apply AdjointableMap.ext
  intro z
  have h : (operatorHom β E J.toAdjointable).toCLM =
      (ordinaryModuleGrading β J).toAdjointable.toCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x d
    change operatorHom β E J.toAdjointable (mk β E x d) =
      (ordinaryModuleGrading β J).grading (mk β E x d)
    rw [operatorHom_mk, ordinaryModuleGrading_mk]
    rfl
  exact DFunLike.congr_fun h z

omit [Countable Γ] [TopologicalSpace.SeparableSpace B] in
theorem pairModuleMap_externalGrading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      ((moduleGrading (cliffordCoefficientAction β) cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading β) (cliffordExternalEvenGrading J)).grading z) =
      (cliffordExternalEvenGrading (ordinaryModuleGrading β J)).grading (pairModuleMap β z) := by
  let W : Module (cliffordCoefficientAction β) (CliffordPairModule B E) →L[ℂ]
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
    (pairModuleMap (E := E) β).toContinuousLinearMap
  let JS : Module (cliffordCoefficientAction β) (CliffordPairModule B E) →L[ℂ]
      Module (cliffordCoefficientAction β) (CliffordPairModule B E) :=
    (moduleGrading (cliffordCoefficientAction β) cliffordCoefficientGrading
      (cliffordCoefficientAction_preservesGrading β)
      (cliffordExternalEvenGrading J)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let JT : CliffordPairModule (ReducedCrossedProduct β) (Module β E) →L[ℂ]
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) :=
    (cliffordExternalEvenGrading (ordinaryModuleGrading β J)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let JD : Module β E →L[ℂ] Module β E :=
    (ordinaryModuleGrading β J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let G : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ →
      (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ := fun d =>
    MulOpposite.op
      ((reducedCrossedProductGrading (cliffordCoefficientAction β)
        cliffordCoefficientGrading (cliffordCoefficientAction_preservesGrading β)).automorphism
          (MulOpposite.unop d))
  let P : CliffordPairModule B E →
      (ReducedCrossedProduct β × ReducedCrossedProduct β) →
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) := fun y q =>
    cliffordPairMk (mk β E y.1 (MulOpposite.op q.1))
      (mk β E y.2 (MulOpposite.op q.2))
  have hW (y : CliffordPairModule B E)
      (d : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :
      W (mk (cliffordCoefficientAction β) (CliffordPairModule B E) y d) =
        P y ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop d)) :=
    pairModuleMap_mk (Γ := Γ) (B := B) (E := E) β y d
  have hJS (y : CliffordPairModule B E)
      (d : (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ) :
      JS (mk (cliffordCoefficientAction β) (CliffordPairModule B E) y d) =
        mk (cliffordCoefficientAction β) (CliffordPairModule B E)
          ((cliffordExternalEvenGrading J).grading y) (G d) :=
    moduleGrading_mk (Γ := Γ) (B := B × B) (E := CliffordPairModule B E)
      (cliffordCoefficientAction β) cliffordCoefficientGrading
      (cliffordCoefficientAction_preservesGrading β) (cliffordExternalEvenGrading J) y d
  have hJD (y : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      JD (mk β E y d) = mk β E (J.grading y) d :=
    ordinaryModuleGrading_mk (Γ := Γ) (B := B) (E := E) β J y d
  have hP (y : CliffordPairModule B E)
      (q : ReducedCrossedProduct β × ReducedCrossedProduct β) :
      P ((cliffordExternalEvenGrading J).grading y)
          ((cliffordCoefficientGrading :
            CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism q) =
        JT (P y q) := by
    calc
      P ((cliffordExternalEvenGrading J).grading y)
          ((cliffordCoefficientGrading :
            CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism q) =
          cliffordPairMk
            (mk β E (J.grading y.2) (MulOpposite.op q.2))
            (mk β E (J.grading y.1) (MulOpposite.op q.1)) := rfl
      _ = cliffordPairMk
          (JD (mk β E y.2 (MulOpposite.op q.2)))
          (JD (mk β E y.1 (MulOpposite.op q.1))) :=
        congrArg₂
          (fun u v : Module β E => cliffordPairMk (B := ReducedCrossedProduct β) u v)
          (hJD y.2 (MulOpposite.op q.2)).symm
          (hJD y.1 (MulOpposite.op q.1)).symm
      _ = JT (P y q) := rfl
  have h : W.comp JS = JT.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B × B) (C := ReducedCrossedProduct (cliffordCoefficientAction β))
      (E := CliffordPairModule B E)
      (F := (ReducedCrossedProduct (cliffordCoefficientAction β))ᵐᵒᵖ)
      (φ := coefficientRepresentation (cliffordCoefficientAction β))
      (P := CliffordPairModule (ReducedCrossedProduct β) (Module β E))
      (f := W.comp JS) (g := JT.comp W)
    intro x d
    have hd : (ReducedCrossedProductPair.equiv β) (MulOpposite.unop (G d)) =
        (cliffordCoefficientGrading :
          CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism
            ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop d)) :=
      ReducedCrossedProductPair.equiv_grading β (MulOpposite.unop d)
    calc
      (W.comp JS) (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x d) =
          W (mk (cliffordCoefficientAction β) (CliffordPairModule B E)
            ((cliffordExternalEvenGrading J).grading x) (G d)) :=
        congrArg (fun v : Module (cliffordCoefficientAction β) (CliffordPairModule B E) => W v)
          (hJS x d)
      _ = P ((cliffordExternalEvenGrading J).grading x)
          ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop (G d))) :=
        hW ((cliffordExternalEvenGrading J).grading x) (G d)
      _ = P ((cliffordExternalEvenGrading J).grading x)
          ((cliffordCoefficientGrading :
            CStarGrading (ReducedCrossedProduct β × ReducedCrossedProduct β)).automorphism
              ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop d))) :=
        congrArg (P ((cliffordExternalEvenGrading J).grading x)) hd
      _ = JT (P x ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop d))) :=
        hP x ((ReducedCrossedProductPair.equiv β) (MulOpposite.unop d))
      _ = (JT.comp W) (mk (cliffordCoefficientAction β) (CliffordPairModule B E) x d) :=
        congrArg (fun v : CliffordPairModule (ReducedCrossedProduct β) (Module β E) => JT v)
          (hW x d).symm
  exact DFunLike.congr_fun h z

omit [Countable Γ] [TopologicalSpace.SeparableSpace B]
  [PartialOrder A] [StarOrderedRing A] in
/-- The actual grading projections commute with each actual regular group
operator. This is a consequence of the original grading-preserving action. -/
theorem externalEven_projection_commutes (c : KasparovCycle α β E) (g : Γ) :
    CliffordOne.plusProjection (ordinaryModuleGrading β c.grading).toAdjointable *
        groupOperator β E c.groupAction g =
      groupOperator β E c.groupAction g *
        CliffordOne.plusProjection (ordinaryModuleGrading β c.grading).toAdjointable ∧
    CliffordOne.minusProjection (ordinaryModuleGrading β c.grading).toAdjointable *
        groupOperator β E c.groupAction g =
      groupOperator β E c.groupAction g *
        CliffordOne.minusProjection (ordinaryModuleGrading β c.grading).toAdjointable := by
  have hJ : (ordinaryModuleGrading β c.grading).toAdjointable * groupOperator β E c.groupAction g =
      groupOperator β E c.groupAction g * (ordinaryModuleGrading β c.grading).toAdjointable := by
    ext z
    exact groupOperator_ordinary_even β c.groupAction c.grading c.grading_preserved g z
  constructor
  · simp only [CliffordOne.plusProjection, smul_mul_assoc, mul_smul_comm,
      add_mul, mul_add, one_mul, mul_one, hJ]
  · simp only [CliffordOne.minusProjection, smul_mul_assoc, mul_smul_comm,
      sub_mul, mul_sub, one_mul, mul_one, hJ]

private theorem externalEven_half_mul_aux {D : Type*} [NonUnitalSemiring D]
    (X Y P M V : D) (hP : P * V = V * P) (hM : M * V = V * M) :
    (X * P + Y * M) * V = (X * V) * P + (Y * V) * M := by
  calc
    _ = (X * P) * V + (Y * M) * V := add_mul (X * P) (Y * M) V
    _ = X * (P * V) + Y * (M * V) :=
      congrArg₂ (fun Z W : D => Z + W) (mul_assoc X P V) (mul_assoc Y M V)
    _ = X * (V * P) + Y * (V * M) :=
      congrArg₂ (fun Z W : D => X * Z + Y * W) hP hM
    _ = (X * V) * P + (Y * V) * M :=
      congrArg₂ (fun Z W : D => Z + W)
        (mul_assoc X V P).symm (mul_assoc Y V M).symm

omit [Countable Γ] [TopologicalSpace.SeparableSpace B]
  [PartialOrder A] [StarOrderedRing A] in
private theorem externalEven_half_operator_aux (c : KasparovCycle α β E) (a : A × A) :
    operatorHom β E (CliffordExternalEvenCycle.half (GradedKasparovCycle.ofKasparovCycle c) a) =
      operatorHom β E (c.representation a.1) *
          CliffordOne.plusProjection (ordinaryModuleGrading β c.grading).toAdjointable +
        operatorHom β E (c.representation a.2) *
          CliffordOne.minusProjection (ordinaryModuleGrading β c.grading).toAdjointable := by
  simp only [CliffordExternalEvenCycle.half, halfRepresentation_eq,
    GradedKasparovCycle.ofKasparovCycle, CliffordOne.plusProjection,
    CliffordOne.minusProjection, map_add, map_mul, map_smul, map_one, map_sub,
    operatorHom_originalGrading]

private theorem externalEven_half_target_aux (c : KasparovCycle α β E)
    (a : A × A) (g : Γ) :
    CliffordExternalEvenCycle.half
      (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.1),
          algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.2)) =
      (operatorHom β E (c.representation a.1) * groupOperator β E c.groupAction g) *
          CliffordOne.plusProjection (ordinaryModuleGrading β c.grading).toAdjointable +
        (operatorHom β E (c.representation a.2) * groupOperator β E c.groupAction g) *
          CliffordOne.minusProjection (ordinaryModuleGrading β c.grading).toAdjointable := by
  simp only [CliffordExternalEvenCycle.half, halfRepresentation_eq,
    GradedKasparovCycle.ofKasparovCycle, evenCycle, reducedSourceRepresentation_single,
    sourceGenerator, sourceRepresentation_apply]

/-- The exact Koszul half representation identity for a finite regular generator. -/
theorem externalEven_half_single (c : KasparovCycle α β E) (a : A × A) (g : Γ) :
    operatorHom β E (CliffordExternalEvenCycle.half (GradedKasparovCycle.ofKasparovCycle c) a) *
        groupOperator β E c.groupAction g =
      CliffordExternalEvenCycle.half (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.1),
          algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.2)) := by
  let V : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    groupOperator β E c.groupAction g
  let P : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    CliffordOne.plusProjection (ordinaryModuleGrading β c.grading).toAdjointable
  let M : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    CliffordOne.minusProjection (ordinaryModuleGrading β c.grading).toAdjointable
  exact (congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) => T * V)
    (externalEven_half_operator_aux (Γ := Γ) (A := A) (B := B) (E := E) β α c a)).trans
      ((externalEven_half_mul_aux
        (operatorHom β E (c.representation a.1))
        (operatorHom β E (c.representation a.2)) P M V
        (externalEven_projection_commutes (Γ := Γ) (A := A) (B := B) (E := E) β α c g).1
        (externalEven_projection_commutes (Γ := Γ) (A := A) (B := B) (E := E) β α c g).2).trans
          (externalEven_half_target_aux (Γ := Γ) (A := A) (B := B) (E := E) β α c a g).symm)

theorem pairModuleMap_externalSourceGenerator (c : KasparovCycle α β E)
    (a : A × A) (g : Γ)
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      (sourceGenerator (cliffordCoefficientAction β) (CliffordPairModule B E)
        (cliffordPairAction c.groupAction)
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c)).representation a g z) =
      (CliffordExternalEvenCycle.cycle
        (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))).representation
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.1),
            algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.2))
              (pairModuleMap β z) := by
  let S : AdjointableMap B E E :=
    CliffordExternalEvenCycle.half (GradedKasparovCycle.ofKasparovCycle c) a
  let T : AdjointableMap B E E :=
    CliffordExternalEvenCycle.half (GradedKasparovCycle.ofKasparovCycle c)
      ((cliffordCoefficientGrading : CStarGrading (A × A)).automorphism a)
  let HS : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    operatorHom β E S
  let HT : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    operatorHom β E T
  let V : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    groupOperator β E c.groupAction g
  let y : CliffordPairModule (ReducedCrossedProduct β) (Module β E) := pairModuleMap β z
  let ev :
      AdjointableMap (ReducedCrossedProduct β × ReducedCrossedProduct β)
        (CliffordPairModule (ReducedCrossedProduct β) (Module β E))
        (CliffordPairModule (ReducedCrossedProduct β) (Module β E)) →
      CliffordPairModule (ReducedCrossedProduct β) (Module β E) := fun L => L y
  change pairModuleMap β
    (operatorHom (cliffordCoefficientAction β) (CliffordPairModule B E)
      (cliffordPairMap S T)
      (groupOperator (cliffordCoefficientAction β) (CliffordPairModule B E)
        (cliffordPairAction c.groupAction) g z)) = _
  have hOp := pairModuleMap_operator (Γ := Γ) (B := B) (E := E) β S T
    (groupOperator (cliffordCoefficientAction β) (CliffordPairModule B E)
      (cliffordPairAction c.groupAction) g z)
  have hG := congrArg
    (fun v : CliffordPairModule (ReducedCrossedProduct β) (Module β E) =>
      cliffordPairMap HS HT v)
    (pairModuleMap_groupOperator (Γ := Γ) (B := B) (E := E) β c.groupAction g z)
  have hComp := congrArg ev
    (cliffordPairMap_mul (B := ReducedCrossedProduct β) (H := Module β E) HS HT V V).symm
  have hHalf := congrArg ev
    (congrArg₂
      (fun R S : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
        cliffordPairMap R S)
      (externalEven_half_single (Γ := Γ) (A := A) (B := B) (E := E) β α c a g)
      (externalEven_half_single (Γ := Γ) (A := A) (B := B) (E := E) β α c
        ((cliffordCoefficientGrading : CStarGrading (A × A)).automorphism a) g))
  exact hOp.trans (hG.trans (hComp.trans hHalf))

theorem pairModuleMap_externalRepresentation (c : KasparovCycle α β E)
    (a : ReducedCrossedProduct (cliffordCoefficientAction α))
    (z : Module (cliffordCoefficientAction β) (CliffordPairModule B E)) :
    pairModuleMap β
      ((gradedCycle (cliffordCoefficientAction β) (cliffordCoefficientAction α)
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c))).representation a z) =
      (CliffordExternalEvenCycle.cycle
        (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))).representation
          (ReducedCrossedProductPair.equiv α a) (pairModuleMap β z) := by
  let ρS := (gradedCycle (cliffordCoefficientAction β) (cliffordCoefficientAction α)
    (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c))).representation
  let ρT := (CliffordExternalEvenCycle.cycle
    (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))).representation.comp
      (ReducedCrossedProductPair.equiv α).toNonUnitalStarAlgHom
  let W := (pairModuleMap (E := E) β).toContinuousLinearMap
  have hS : Continuous (fun a => W (ρS a z)) :=
    W.continuous.comp
      ((AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρS)).clm_apply continuous_const)
  have hT : Continuous (fun a => ρT a (W z)) :=
    (AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρT)).clm_apply continuous_const
  change W (ρS a z) = ρT a (W z)
  refine (algebraicToReducedCrossed_denseRange (cliffordCoefficientAction α)).induction_on a
    (isClosed_eq hS hT) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on (cliffordCoefficientAction α) with
  | zero => simp only [map_zero, AdjointableMap.coe_zero_apply]
  | single g b =>
    have hs : ρS (algebraicToReducedCrossed (cliffordCoefficientAction α)
        (AlgebraicCrossedProduct.single (cliffordCoefficientAction α) g b)) =
        sourceGenerator (cliffordCoefficientAction β) (CliffordPairModule B E)
          (cliffordPairAction c.groupAction)
          (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c)).representation b g :=
      reducedSourceRepresentation_single (cliffordCoefficientAction β) (CliffordPairModule B E)
        (cliffordCoefficientAction α) (cliffordPairAction c.groupAction)
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c)).representation
        (CliffordExternalEvenCycle.cycle
          (GradedKasparovCycle.ofKasparovCycle c)).representation_equivariant g b
    have ht : ρT (algebraicToReducedCrossed (cliffordCoefficientAction α)
        (AlgebraicCrossedProduct.single (cliffordCoefficientAction α) g b)) =
        (CliffordExternalEvenCycle.cycle
          (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))).representation
            (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g b.1),
              algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g b.2)) :=
      congrArg
        (fun q : ReducedCrossedProduct α × ReducedCrossedProduct α =>
          (CliffordExternalEvenCycle.cycle
            (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))).representation q)
        (pairCrossed_equiv_single α b g)
    exact (congrArg
      (fun T : AdjointableMap (ReducedCrossedProduct (cliffordCoefficientAction β))
        (Module (cliffordCoefficientAction β) (CliffordPairModule B E))
        (Module (cliffordCoefficientAction β) (CliffordPairModule B E)) => W (T z)) hs).trans
      ((pairModuleMap_externalSourceGenerator β α c b g z).trans
        (congrArg
          (fun T : AdjointableMap (ReducedCrossedProduct β × ReducedCrossedProduct β)
            (CliffordPairModule (ReducedCrossedProduct β) (Module β E))
            (CliffordPairModule (ReducedCrossedProduct β) (Module β E)) => T (W z)) ht).symm)
  | add f h ihf ihh =>
    simpa only [map_add, AdjointableMap.coe_add_apply] using congrArg₂ (· + ·) ihf ihh

def descendedExternalEven (c : KasparovCycle α β E) :=
  (gradedCycle (cliffordCoefficientAction β) (cliffordCoefficientAction α)
    (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c))).changeCoefficients
      (KasparovDescentPairCoefficientEquiv.equiv β)

def externalEvenOfDescent (c : KasparovCycle α β E) :=
  (CliffordExternalEvenCycle.cycle
    (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c))).sourcePullback
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (cliffordCoefficientAction α)))
      (reducedCrossedProductGrading (cliffordCoefficientAction α) cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading α))
      (fun _ _ => rfl) (ReducedCrossedProductPair.equiv α).toNonUnitalStarAlgHom
      (fun _ _ => rfl) (ReducedCrossedProductPair.equiv_grading α)

private theorem externalEvenDescentIso_grading_aux
    (c : KasparovCycle α β E) (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedExternalEven β α c).grading.grading z) =
      (externalEvenOfDescent β α c).grading.grading (pairModuleEquiv (E := E) β z) := by
  exact pairModuleMap_externalGrading (Γ := Γ) (B := B) (E := E) β c.grading
    (coefficientChangedToOriginal (ReducedCrossedProductPair.equiv β) z)

private theorem externalEvenDescentIso_action_aux
    (c : KasparovCycle α β E) (g : Unit) (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedExternalEven β α c).groupAction.action g z) =
      (externalEvenOfDescent β α c).groupAction.action g (pairModuleEquiv (E := E) β z) := by
  have hg : g = (1 : Unit) := Subsingleton.elim _ _
  have hsource : (descendedExternalEven β α c).groupAction.action g z = z :=
    (congrArg
      (fun k : Unit => (descendedExternalEven β α c).groupAction.action k z) hg).trans
      (EquivariantHilbertModule.one_apply (descendedExternalEven β α c).groupAction z)
  have htarget :
      (externalEvenOfDescent β α c).groupAction.action g (pairModuleEquiv (E := E) β z) =
        pairModuleEquiv (E := E) β z :=
    (congrArg
      (fun k : Unit => (externalEvenOfDescent β α c).groupAction.action k
        (pairModuleEquiv (E := E) β z)) hg).trans
      (EquivariantHilbertModule.one_apply (externalEvenOfDescent β α c).groupAction
        (pairModuleEquiv (E := E) β z))
  exact (congrArg
    (fun v : PairChangedModule (E := E) β => pairModuleEquiv (E := E) β v) hsource).trans
    htarget.symm

private theorem externalEvenDescentIso_representation_aux
    (c : KasparovCycle α β E) (a : ReducedCrossedProduct (cliffordCoefficientAction α))
    (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedExternalEven β α c).representation a z) =
      (externalEvenOfDescent β α c).representation a (pairModuleEquiv (E := E) β z) := by
  exact pairModuleMap_externalRepresentation (Γ := Γ) (A := A) (B := B) (E := E) β α c a
    (coefficientChangedToOriginal (ReducedCrossedProductPair.equiv β) z)

private theorem externalEvenDescentIso_operator_aux
    (c : KasparovCycle α β E) (z : PairChangedModule (E := E) β) :
    pairModuleEquiv (E := E) β ((descendedExternalEven β α c).operator z) =
      (externalEvenOfDescent β α c).operator (pairModuleEquiv (E := E) β z) := by
  exact pairModuleMap_operator (Γ := Γ) (B := B) (E := E) β c.operator c.operator
    (coefficientChangedToOriginal (ReducedCrossedProductPair.equiv β) z)

/-- Whole actual external-even coherence, including its Koszul source action. -/
def externalEvenDescentIso (c : KasparovCycle α β E) :
    GradedKasparovCycleIso (descendedExternalEven β α c) (externalEvenOfDescent β α c) where
  moduleEquiv := pairModuleEquiv β
  grading_intertwine z := externalEvenDescentIso_grading_aux (E := E) β α c z
  action_intertwine g z := externalEvenDescentIso_action_aux (E := E) β α c g z
  representation_intertwine a z := externalEvenDescentIso_representation_aux (E := E) β α c a z
  operator_intertwine z := externalEvenDescentIso_operator_aux (E := E) β α c z

end BC4lean.KKTheory.KasparovDescent
