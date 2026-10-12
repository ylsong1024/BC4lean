import BC4lean.CliffordOddOddSourceHilbert

/-! # Genuine final odd-odd-odd product criterion

The original product's full diagonal σ_y creator error is composed with
the true Fourier eigenvector embeddings. Both coefficient coordinates and
both adjoints are retained. Localized positivity first uses the actual
even anticommutator and its orthogonal swap projections, then transports
through the same whole module unitary.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddOddSource
open CliffordOddOddFourier CliffordQuarterPhase CliffordExternalEvenRepresentation

variable {Γ A B C H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : OddKasparovCycle α β H) (d : OddKasparovCycle β γ F)

local instance cliffordOddOddSourceCriterionSourceSumComplete : CompleteSpace (HilbertModuleSum B H H) := hilbertModuleSum_complete
local instance cliffordOddOddSourceCriterionTargetSumComplete : CompleteSpace (Sum (H := H) d) := hilbertModuleSum_complete
local instance secondSumComplete : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete

def coordinateCreation (x : HilbertModuleSum B H H) :=
  cliffordPairMap (column (moduleCreationMap d.representation x.fst) (moduleCreationMap d.representation x.snd))
    (column (moduleCreationMap d.representation x.fst) (moduleCreationMap d.representation x.snd))

theorem creation_operator (x : HilbertModuleSum B H H) :
    (pairDistribution d).toAdjointable.comp (moduleCreationMap d.cliffordExpansion.representation x) =
      coordinateCreation d x := by
  have hcolumn (T S : AdjointableMap C F (Base (H := H) d)) (v : F) :
      (column T S).toCLM v = sumMk (B := C) (T.toCLM v) (S.toCLM v) := by
    change column T S v = sumMk (B := C) (T v) (S v)
    exact column_apply T S v
  ext y
  change pairDistribution (H := H) d
      (interiorModuleTensorMk d.cliffordExpansion.representation x y) =
    (coordinateCreation d x).toCLM y
  rw [pairDistribution_mk]
  dsimp only [coordinateCreation, cliffordPairMap]
  erw [ContinuousLinearMap.coe_prodMap']
  dsimp only [Prod.map, cliffordPairMk]
  rcases y with ⟨y₁, y₂⟩
  dsimp only
  erw [hcolumn, hcolumn]
  rfl

theorem creation_sub_error
    (P : AdjointableMap (C × C) (Source d) (Source d))
    (D : AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F))
    (x : HilbertModuleSum B H H) :
    (coordinateCreation d x).comp D - ((pairDistribution d).transport P).comp (coordinateCreation d x) =
      (pairDistribution d).toAdjointable.comp
        ((moduleCreationMap d.cliffordExpansion.representation x).comp D -
          P.comp (moduleCreationMap d.cliffordExpansion.representation x)) := by
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.transport_apply,
    ← creation_operator d x, AdjointableMap.comp_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.symm_apply_apply, map_sub]

theorem creation_add_error
    (P : AdjointableMap (C × C) (Source d) (Source d))
    (D : AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F))
    (x : HilbertModuleSum B H H) :
    (coordinateCreation d x).comp D + ((pairDistribution d).transport P).comp (coordinateCreation d x) =
      (pairDistribution d).toAdjointable.comp
        ((moduleCreationMap d.cliffordExpansion.representation x).comp D +
          P.comp (moduleCreationMap d.cliffordExpansion.representation x)) := by
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.transport_apply,
    ← creation_operator d x, AdjointableMap.comp_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.symm_apply_apply, map_add]

theorem sub_compact_of_coordinate
    (P : AdjointableMap (C × C) (Source d) (Source d))
    (D : AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F))
    (x : HilbertModuleSum B H H)
    (h : IsModuleCompact ((coordinateCreation d x).comp D -
      ((pairDistribution d).transport P).comp (coordinateCreation d x))) :
    IsModuleCompact ((moduleCreationMap d.cliffordExpansion.representation x).comp D -
      P.comp (moduleCreationMap d.cliffordExpansion.representation x)) := by
  rw [creation_sub_error] at h
  have hout := h.comp_left (pairDistribution d).symm.toAdjointable
  convert hout using 1
  ext y
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.symm_apply_apply]

theorem add_compact_of_coordinate
    (P : AdjointableMap (C × C) (Source d) (Source d))
    (D : AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F))
    (x : HilbertModuleSum B H H)
    (h : IsModuleCompact ((coordinateCreation d x).comp D +
      ((pairDistribution d).transport P).comp (coordinateCreation d x))) :
    IsModuleCompact ((moduleCreationMap d.cliffordExpansion.representation x).comp D +
      P.comp (moduleCreationMap d.cliffordExpansion.representation x)) := by
  rw [creation_add_error] at h
  have hout := h.comp_left (pairDistribution d).symm.toAdjointable
  convert hout using 1
  ext y
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.symm_apply_apply]

variable (R : AdjointableMap C (CliffordOddOddCoordinate.Source (H := H) d) (CliffordOddOddCoordinate.Source (H := H) d))
  (hR : IsGradedKasparovProductOperator c.cliffordExpansion (CliffordOddSourceCycle.cycle d) R)

theorem original_diagonal_error (x : H) :
    IsModuleCompact ((CliffordOddOddCoordinate.cycle c d R hR.cycleConditions).operator.comp
      (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)) -
        (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)).comp
          (CliffordOddSourceCycle.operator d.operator)) := by
  have h := CliffordOddBalancedTensor.coordinate_connection_creation_defect c d R hR.connection
    (cliffordPairMk x x)
  have hswap : cliffordPairGrading.grading (cliffordPairMk (B := B) x x) =
      cliffordPairMk (B := B) x x := rfl
  rw [hswap] at h
  change IsModuleCompact ((CliffordOddBalancedTensor.coordinateOperator d.representation R).comp
    (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)) -
      (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)).comp
        (CliffordOddSourceCycle.operator d.operator)) at h
  exact h

theorem original_diagonal_adjoint_error (x : H) :
    IsModuleCompact ((star (CliffordOddOddCoordinate.cycle c d R hR.cycleConditions).operator).comp
      (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)) -
        (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)).comp
          (CliffordOddSourceCycle.operator (star d.operator))) := by
  have h := CliffordOddBalancedTensor.coordinate_connection_creation_adjoint_defect c d R hR.connection
    (cliffordPairMk x x)
  have hswap : cliffordPairGrading.grading (cliffordPairMk (B := B) x x) =
      cliffordPairMk (B := B) x x := rfl
  rw [hswap] at h
  change IsModuleCompact ((star (CliffordOddBalancedTensor.coordinateOperator d.representation R)).comp
    (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)) -
      (sumMap (moduleCreationMap d.representation x) (moduleCreationMap d.representation x)).comp
        (CliffordOddSourceCycle.operator (star d.operator))) at h
  exact h

private theorem even_coordinate_error
    (G : AdjointableMap C (Sum d) (Sum d)) (D : AdjointableMap C F F)
    (x : HilbertModuleSum B H H) (hx : sumSwap x = x)
    (hc : IsModuleCompact (G.comp (sumMap (moduleCreationMap d.representation x.fst)
      (moduleCreationMap d.representation x.fst)) -
        (sumMap (moduleCreationMap d.representation x.fst) (moduleCreationMap d.representation x.fst)).comp
          (CliffordOddSourceCycle.operator D))) :
    IsModuleCompact ((coordinateCreation d x).comp (cliffordPairMap D (-D)) -
      (cliffordPairMap (hilbertEquiv.transport G) (oppositeEquiv.transport G)).comp (coordinateCreation d x)) := by
  have hx' : x.snd = x.fst := congrArg Prod.fst hx
  have hp := (creator_even G (moduleCreationMap d.representation x.fst) D hc).neg
  have hm := (opposite_creator_even G (moduleCreationMap d.representation x.fst) D hc).neg
  have h := hp.cliffordPairMap hm
  let T : AdjointableMap C F (Sum (H := H) d) :=
    column (moduleCreationMap d.representation x.fst) (moduleCreationMap d.representation x.fst)
  have hpairCompRight (S T : AdjointableMap C F (Sum (H := H) d))
      (U V : AdjointableMap C F F) :
      (cliffordPairMap S T).comp (cliffordPairMap U V) =
        cliffordPairMap (S.comp U) (T.comp V) := by
    ext v
    rcases v with ⟨v₁, v₂⟩
    rfl
  have hpairCompLeft (S T : AdjointableMap C (Sum (H := H) d) (Sum (H := H) d))
      (U V : AdjointableMap C F (Sum (H := H) d)) :
      (cliffordPairMap S T).comp (cliffordPairMap U V) =
        cliffordPairMap (S.comp U) (T.comp V) := by
    ext v
    rcases v with ⟨v₁, v₂⟩
    rfl
  have hcompNeg (S : AdjointableMap C F (Sum (H := H) d)) :
      S.comp (-D) = -(S.comp D) := by
    ext v
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_neg_apply]
    exact S.toCLM.map_neg (D.toCLM v)
  have hcreation : coordinateCreation d x = cliffordPairMap T T := by
    dsimp only [coordinateCreation]
    rw [hx']
  have hfirst : T.comp D - (hilbertEquiv.transport G).comp T =
      -((hilbertEquiv.transport G).comp T - T.comp D) := by abel
  have hsecond : T.comp (-D) - (oppositeEquiv.transport G).comp T =
      -((oppositeEquiv.transport G).comp T + T.comp D) := by
    rw [hcompNeg]
    abel
  rw [hcreation]
  erw [hpairCompRight, hpairCompLeft, ← cliffordPairMap_sub]
  rw [hfirst, hsecond]
  exact h

private theorem odd_coordinate_error
    (G : AdjointableMap C (Sum d) (Sum d)) (D : AdjointableMap C F F)
    (x : HilbertModuleSum B H H) (hx : sumSwap x = -x)
    (hc : IsModuleCompact (G.comp (sumMap (moduleCreationMap d.representation x.fst)
      (moduleCreationMap d.representation x.fst)) -
        (sumMap (moduleCreationMap d.representation x.fst) (moduleCreationMap d.representation x.fst)).comp
          (CliffordOddSourceCycle.operator D))) :
    IsModuleCompact ((coordinateCreation d x).comp (cliffordPairMap D (-D)) +
      (cliffordPairMap (hilbertEquiv.transport G) (oppositeEquiv.transport G)).comp (coordinateCreation d x)) := by
  have hx' : x.snd = -x.fst := congrArg Prod.fst hx
  have hp := creator_odd G (moduleCreationMap d.representation x.fst) D hc
  have hm := opposite_creator_odd G (moduleCreationMap d.representation x.fst) D hc
  have h := hp.cliffordPairMap hm
  let T : AdjointableMap C F (Sum (H := H) d) :=
    column (moduleCreationMap d.representation x.fst) (-moduleCreationMap d.representation x.fst)
  have hpairCompRight (S T : AdjointableMap C F (Sum (H := H) d))
      (U V : AdjointableMap C F F) :
      (cliffordPairMap S T).comp (cliffordPairMap U V) =
        cliffordPairMap (S.comp U) (T.comp V) := by
    ext v
    rcases v with ⟨v₁, v₂⟩
    rfl
  have hpairCompLeft (S T : AdjointableMap C (Sum (H := H) d) (Sum (H := H) d))
      (U V : AdjointableMap C F (Sum (H := H) d)) :
      (cliffordPairMap S T).comp (cliffordPairMap U V) =
        cliffordPairMap (S.comp U) (T.comp V) := by
    ext v
    rcases v with ⟨v₁, v₂⟩
    rfl
  have hcompNeg (S : AdjointableMap C F (Sum (H := H) d)) :
      S.comp (-D) = -(S.comp D) := by
    ext v
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_neg_apply]
    exact S.toCLM.map_neg (D.toCLM v)
  have hcreation : coordinateCreation d x = cliffordPairMap T T := by
    dsimp only [coordinateCreation]
    rw [hx', moduleCreationMap_neg]
  have hfirst : T.comp D + (hilbertEquiv.transport G).comp T =
      (hilbertEquiv.transport G).comp T + T.comp D := by abel
  have hsecond : T.comp (-D) + (oppositeEquiv.transport G).comp T =
      (oppositeEquiv.transport G).comp T - T.comp D := by
    rw [hcompNeg]
    abel
  rw [hcreation]
  erw [hpairCompRight, hpairCompLeft, ← cliffordPairMap_add]
  rw [hfirst, hsecond]
  exact h

set_option maxHeartbeats 1200000 in
theorem connection : GradedKasparovConnection (CliffordOddSourceCycle.cycle c) d.cliffordExpansion
    (productOperator c d R hR.cycleConditions) where
  even x hx := by
    apply sub_compact_of_coordinate (H := H) d
    erw [pairDistribution_productOperator (H := H) c d R hR.cycleConditions]
    exact even_coordinate_error (H := H) d _ d.operator x hx (original_diagonal_error (H := H) c d R hR x.fst)
  even_adjoint x hx := by
    apply sub_compact_of_coordinate (H := H) d
    change IsModuleCompact ((coordinateCreation (H := H) d x).comp (star (cliffordPairMap d.operator (-d.operator))) -
      ((pairDistribution (H := H) d).transport (star (productOperator (H := H) c d R hR.cycleConditions))).comp (coordinateCreation (H := H) d x))
    erw [← cliffordPairMap_star, star_neg, HilbertModuleEquiv.transport_star,
      pairDistribution_productOperator (H := H) c d R hR.cycleConditions, ← cliffordPairMap_star,
      ← HilbertModuleEquiv.transport_star, ← HilbertModuleEquiv.transport_star]
    exact even_coordinate_error (H := H) d _ (star d.operator) x hx (original_diagonal_adjoint_error (H := H) c d R hR x.fst)
  odd x hx := by
    apply add_compact_of_coordinate (H := H) d
    erw [pairDistribution_productOperator (H := H) c d R hR.cycleConditions]
    exact odd_coordinate_error (H := H) d _ d.operator x hx (original_diagonal_error (H := H) c d R hR x.fst)
  odd_adjoint x hx := by
    apply add_compact_of_coordinate (H := H) d
    change IsModuleCompact ((coordinateCreation (H := H) d x).comp (star (cliffordPairMap d.operator (-d.operator))) +
      ((pairDistribution (H := H) d).transport (star (productOperator (H := H) c d R hR.cycleConditions))).comp (coordinateCreation (H := H) d x))
    erw [← cliffordPairMap_star, star_neg, HilbertModuleEquiv.transport_star,
      pairDistribution_productOperator (H := H) c d R hR.cycleConditions, ← cliffordPairMap_star,
      ← HilbertModuleEquiv.transport_star, ← HilbertModuleEquiv.transport_star]
    exact odd_coordinate_error (H := H) d _ (star d.operator) x hx (original_diagonal_adjoint_error (H := H) c d R hR x.fst)

theorem whole_firstOperator (z : Target d) :
    wholeEquiv d (cliffordPairMap
      (sumMap (interiorModuleTensorOperator d.representation c.operator)
        (-interiorModuleTensorOperator d.representation c.operator))
      (sumMap (interiorModuleTensorOperator d.representation c.operator)
        (-interiorModuleTensorOperator d.representation c.operator)) z) =
      interiorModuleTensorOperator d.cliffordExpansion.representation (CliffordOddSourceCycle.cycle c).operator
        (wholeEquiv d z) := by
  apply (pairDistribution d).injective
  rw [pairDistribution_firstOperator c d]
  simp only [wholeEquiv_apply, HilbertModuleEquiv.apply_symm_apply]
  exact pairEquiv_signed _ z

set_option maxHeartbeats 1200000 in
theorem positivity (a : A × A) :
    IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator (CliffordOddSourceCycle.cycle c)
      d.cliffordExpansion (productOperator c d R hR.cycleConditions) a) := by
  let e : GradedKasparovCycle α γ CStarGrading.trivial CStarGrading.trivial (Sum (H := H) d) :=
    CliffordOddOddCoordinate.cycle c d R hR.cycleConditions
  let ρ : A →⋆ₙₐ[ℂ] AdjointableMap C (Sum (H := H) d) (Sum (H := H) d) :=
    CliffordOddOddFourier.diagonalRepresentation (CliffordOddOddCoordinate.baseRepresentation c d)
  let J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) (Sum (H := H) d) :=
    CliffordOddSourceCycle.grading (C := C) (H := Base (H := H) d)
  let Z : AdjointableMap C (Sum (H := H) d) (Sum (H := H) d) :=
    sumMap (interiorModuleTensorOperator d.representation c.operator)
      (-interiorModuleTensorOperator d.representation c.operator)
  let V : AdjointableMap C (Sum (H := H) d) (Sum (H := H) d) :=
    Z * e.operator + e.operator * Z
  have hZodd : J.IsOdd J Z := by
    intro z
    apply Prod.ext <;> simp only [J, Z, CliffordOddSourceCycle.grading, sumSwap_apply,
      sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_neg_apply,
      WithCStarModule.neg_fst, WithCStarModule.neg_snd, neg_neg]
  have hGodd : J.IsOdd J e.operator := by
    intro z
    simpa only [J, e, CliffordOddSourceCycle.grading, CliffordOddOddCoordinate.cycle_grading] using
      (CliffordOddOddCoordinate.cycle c d R hR.cycleConditions).operator_odd z
  have hVeven : J.IsEven J V := (hZodd.comp_odd hGodd).add (hGodd.comp_odd hZodd)
  have hV : J.toAdjointable * V = V * J.toAdjointable := by ext z; exact hVeven z
  have hρ : ∀ b, J.toAdjointable * ρ b = ρ b * J.toAdjointable :=
    diagonalRepresentation_commutes _
  have hpos : ∀ b, IsPositiveModuloModuleCompact (ρ b * V * star (ρ b)) := by
    intro b
    change IsPositiveModuloModuleCompact
      (CliffordOddBalancedTensor.coordinatePositivityOperator c d R b)
    exact CliffordOddBalancedTensor.coordinate_productPositivity c d R hR b
  have hp := CliffordExternalEvenMonoidal.half_localized_positivity ρ J hρ V hV hpos a
  have hm := CliffordExternalEvenMonoidal.half_localized_positivity ρ J hρ V hV hpos
    (cliffordCoefficientGrading.automorphism a)
  have hpair := hp.cliffordPairMap hm
  have hbaseRepresentation (b : A) : e.representation b = ρ b := by
    change (CliffordOddOddCoordinate.cycle c d R hR.cycleConditions).representation b =
      sumMap (CliffordOddOddCoordinate.baseRepresentation c d b)
        (CliffordOddOddCoordinate.baseRepresentation c d b)
    exact CliffordOddOddCoordinate.cycle_representation c d R hR.cycleConditions b
  have hbaseGrading : e.grading.toAdjointable = J.toAdjointable := by
    ext z
    change (CliffordOddOddCoordinate.cycle c d R hR.cycleConditions).grading.grading z =
      sumSwap z
    exact CliffordOddOddCoordinate.cycle_grading c d R hR.cycleConditions z
  have hhalf (b : A × A) : CliffordExternalEvenCycle.half e b =
      halfRepresentation ρ J hρ b := by
    change halfRepresentation e.representation e.grading
      (CliffordExternalEvenCycle.representation_commutes_grading e) b =
        halfRepresentation ρ J hρ b
    simp only [halfRepresentation_eq, hbaseRepresentation, hbaseGrading]
  have hreferenceRep : (externalCycle c d R hR.cycleConditions).representation a =
      cliffordPairMap (halfRepresentation ρ J hρ a)
        (halfRepresentation ρ J hρ (cliffordCoefficientGrading.automorphism a)) := by
    change cliffordPairMap (CliffordExternalEvenCycle.half e a)
      (CliffordExternalEvenCycle.half e (cliffordCoefficientGrading.automorphism a)) = _
    rw [hhalf, hhalf]
  have href : IsPositiveModuloModuleCompact ((externalCycle c d R hR.cycleConditions).representation a *
      (cliffordPairMap Z Z * (externalCycle c d R hR.cycleConditions).operator +
        (externalCycle c d R hR.cycleConditions).operator * cliffordPairMap Z Z) *
      star ((externalCycle c d R hR.cycleConditions).representation a)) := by
    change IsPositiveModuloModuleCompact ((externalCycle c d R hR.cycleConditions).representation a *
      (cliffordPairMap Z Z * cliffordPairMap e.operator e.operator +
        cliffordPairMap e.operator e.operator * cliffordPairMap Z Z) *
      star ((externalCycle c d R hR.cycleConditions).representation a))
    rw [hreferenceRep, ← cliffordPairMap_mul, ← cliffordPairMap_mul,
      ← cliffordPairMap_add, ← cliffordPairMap_star, ← cliffordPairMap_mul,
      ← cliffordPairMap_mul]
    exact hpair
  have hfirst : (wholeEquiv d).transport (cliffordPairMap Z Z) =
      interiorModuleTensorOperator d.cliffordExpansion.representation (CliffordOddSourceCycle.cycle c).operator := by
    ext z
    obtain ⟨w, rfl⟩ := (wholeEquiv d).surjective z
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
    exact whole_firstOperator c d w
  have hrep := transportedCycle_tensorRepresentation (CliffordOddSourceCycle.cycle c) d.cliffordExpansion
    (externalCycle c d R hR.cycleConditions) (wholeEquiv d)
    (whole_representation c d R hR.cycleConditions) a
  have hop : (wholeEquiv d).transport (externalCycle c d R hR.cycleConditions).operator =
      productOperator c d R hR.cycleConditions := rfl
  have h := href.transport (wholeEquiv d)
  change IsPositiveModuloModuleCompact
    (gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d.cliffordExpansion a *
      (interiorModuleTensorOperator d.cliffordExpansion.representation
          (CliffordOddSourceCycle.cycle c).operator * productOperator c d R hR.cycleConditions +
        productOperator c d R hR.cycleConditions *
          interiorModuleTensorOperator d.cliffordExpansion.representation
            (CliffordOddSourceCycle.cycle c).operator) *
      star (gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d.cliffordExpansion a))
  simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_star, hfirst, hrep, hop] using h

theorem isProduct : IsGradedKasparovProductOperator (CliffordOddSourceCycle.cycle c) d.cliffordExpansion
    (productOperator c d R hR.cycleConditions) where
  cycleConditions := productConditions c d R hR.cycleConditions
  connection := connection c d R hR
  positivity := positivity c d R hR

end BC4lean.KKTheory.CliffordOddOddSource
