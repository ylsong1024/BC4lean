import BC4lean.ProjectionHilbertModuleSplit

/-! # The actual orthogonal complement of an adjointable isometric embedding

For an adjointable map J with J*J=I, the image projection is the actual JJ*.
The forward unitary has coordinates J*x and (I-JJ*)x, and its inverse adds
Jm to the included complement vector. All identities use the genuine
coefficient-valued inner product; no complement module is postulated.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B M E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M] [CStarModule Bᵐᵒᵖ M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The actual final projection of an adjointable isometric embedding. -/
def isometricEmbeddingProjection (J : AdjointableMap B M E) : AdjointableMap B E E :=
  J.comp J.adjoint

omit [StarOrderedRing B] in
@[simp] theorem isometricEmbeddingProjection_apply (J : AdjointableMap B M E) (x : E) :
    isometricEmbeddingProjection J x = J (J.adjoint x) := rfl

omit [StarOrderedRing B] in
theorem isometricEmbeddingProjection_isStarProjection (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) :
    IsStarProjection (isometricEmbeddingProjection J) := by
  apply isStarProjection_iff'.mpr
  constructor
  · ext x
    change J (J.adjoint (J (J.adjoint x))) = J (J.adjoint x)
    rw [← AdjointableMap.comp_apply J.adjoint J, hJ, AdjointableMap.id_apply]
  · simp only [AdjointableMap.star_eq_adjoint, isometricEmbeddingProjection,
      AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]

omit [StarOrderedRing B] in
@[simp] theorem isometricEmbeddingProjection_embedding (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (m : M) :
    isometricEmbeddingProjection J (J m) = J m := by
  change J (J.adjoint (J m)) = J m
  rw [← AdjointableMap.comp_apply J.adjoint J, hJ, AdjointableMap.id_apply]

omit [StarOrderedRing B] in
theorem isometricEmbeddingAdjoint_complement_zero (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id)
    (x : ProjectionModule (1 - isometricEmbeddingProjection J)) :
    J.adjoint (x : E) = 0 := by
  have hz : J (J.adjoint (x : E)) = 0 :=
    projection_complement_fixed_eq_zero (isometricEmbeddingProjection J) x
  have ht := congrArg J.adjoint hz
  rw [← AdjointableMap.comp_apply J.adjoint J, hJ, AdjointableMap.id_apply,
    map_zero] at ht
  exact ht

omit [StarOrderedRing B] in
@[simp] theorem isometricEmbeddingComplement_embedding_zero (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (m : M) :
    (1 - isometricEmbeddingProjection J) (J m) = 0 := by
  rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply]
  rw [isometricEmbeddingProjection_embedding J hJ, sub_self]

omit [StarOrderedRing B] in
/-- Both actual components preserve the full coefficient-valued pairing. -/
theorem isometricEmbeddingComplement_inner (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (x y : E) :
    ⟪J.adjoint x, J.adjoint y⟫_(Bᵐᵒᵖ) +
      ⟪projectionCorestrict (1 - isometricEmbeddingProjection J)
          (isometricEmbeddingProjection_isStarProjection J hJ).one_sub x,
        projectionCorestrict (1 - isometricEmbeddingProjection J)
          (isometricEmbeddingProjection_isStarProjection J hJ).one_sub y⟫_(Bᵐᵒᵖ) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := by
  have hfirst : ⟪J.adjoint x, J.adjoint y⟫_(Bᵐᵒᵖ) =
      ⟪x, isometricEmbeddingProjection J y⟫_(Bᵐᵒᵖ) := by
    exact J.adjoint.adjoint_identity x (J.adjoint y)
  have htail :
      ⟪projectionCorestrict (1 - isometricEmbeddingProjection J)
          (isometricEmbeddingProjection_isStarProjection J hJ).one_sub x,
        projectionCorestrict (1 - isometricEmbeddingProjection J)
          (isometricEmbeddingProjection_isStarProjection J hJ).one_sub y⟫_(Bᵐᵒᵖ) =
      ⟪x, (1 - isometricEmbeddingProjection J) y⟫_(Bᵐᵒᵖ) := by
    let Q : AdjointableMap B E E := 1 - isometricEmbeddingProjection J
    have hQ : IsStarProjection Q := (isometricEmbeddingProjection_isStarProjection J hJ).one_sub
    have hQadj : Q.adjoint = Q := by
      simpa only [AdjointableMap.star_eq_adjoint] using hQ.isSelfAdjoint.star_eq
    change ⟪Q x, Q y⟫_(Bᵐᵒᵖ) = ⟪x, Q y⟫_(Bᵐᵒᵖ)
    rw [Q.adjoint_identity]
    change ⟪x, Q.adjoint (Q y)⟫_(Bᵐᵒᵖ) = ⟪x, Q y⟫_(Bᵐᵒᵖ)
    rw [hQadj, ← AdjointableMap.mul_apply, hQ.isIdempotentElem.eq]
  rw [hfirst, htail, ← CStarModule.inner_add_right, projection_complement_apply_add]

/-- The whole ambient module is unitarily the input module plus its actual
orthogonal complement. This constructs both inverse maps and the full pairing. -/
def isometricEmbeddingComplementEquiv (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) :
    HilbertModuleEquiv B E
      (HilbertModuleSum B M (ProjectionModule (1 - isometricEmbeddingProjection J))) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := sumMk (J.adjoint x)
            (projectionCorestrict (1 - isometricEmbeddingProjection J)
              (isometricEmbeddingProjection_isStarProjection J hJ).one_sub x)
          invFun x := J x.fst + (x.snd : E)
          left_inv x := projection_complement_apply_add (isometricEmbeddingProjection J) x
          right_inv x := by
            apply (WithCStarModule.equiv Bᵐᵒᵖ
              (M × ProjectionModule (1 - isometricEmbeddingProjection J))).injective
            apply Prod.ext
            · change J.adjoint (J x.fst + (x.snd : E)) = x.fst
              rw [J.adjoint.toCLM.map_add, ← AdjointableMap.comp_apply J.adjoint J,
                hJ, AdjointableMap.id_apply, isometricEmbeddingAdjoint_complement_zero J hJ,
                add_zero]
            · apply Subtype.ext
              change (1 - isometricEmbeddingProjection J) (J x.fst + (x.snd : E)) = (x.snd : E)
              have hfixed : (1 - isometricEmbeddingProjection J) (x.snd : E) = (x.snd : E) :=
                x.snd.property
              rw [(1 - isometricEmbeddingProjection J).toCLM.map_add,
                isometricEmbeddingComplement_embedding_zero J hJ, hfixed, zero_add]
          map_add' x y := by
            apply (WithCStarModule.equiv Bᵐᵒᵖ
              (M × ProjectionModule (1 - isometricEmbeddingProjection J))).injective
            apply Prod.ext
            · exact J.adjoint.toCLM.map_add x y
            · exact (projectionCorestrict _ _).toCLM.map_add x y
          map_smul' c x := by
            apply (WithCStarModule.equiv Bᵐᵒᵖ
              (M × ProjectionModule (1 - isometricEmbeddingProjection J))).injective
            apply Prod.ext
            · exact J.adjoint.toCLM.map_smul c x
            · exact (projectionCorestrict _ _).toCLM.map_smul c x }
      norm_map' x := by
        change ‖sumMk (B := B) (J.adjoint x)
          (projectionCorestrict (1 - isometricEmbeddingProjection J)
            (isometricEmbeddingProjection_isStarProjection J hJ).one_sub x)‖ = ‖x‖
        calc
          _ = Real.sqrt ‖⟪J.adjoint x, J.adjoint x⟫_(Bᵐᵒᵖ) +
              ⟪projectionCorestrict (1 - isometricEmbeddingProjection J)
                  (isometricEmbeddingProjection_isStarProjection J hJ).one_sub x,
                projectionCorestrict (1 - isometricEmbeddingProjection J)
                  (isometricEmbeddingProjection_isStarProjection J hJ).one_sub x⟫_(Bᵐᵒᵖ)‖ := rfl
          _ = Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ :=
            congrArg (fun b : Bᵐᵒᵖ => Real.sqrt ‖b‖) (isometricEmbeddingComplement_inner J hJ x x)
          _ = ‖x‖ := (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (E := E) x).symm }
  inner_map := isometricEmbeddingComplement_inner J hJ

@[simp] theorem isometricEmbeddingComplementEquiv_apply (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (x : E) :
    isometricEmbeddingComplementEquiv J hJ x =
      sumMk (J.adjoint x) (projectionCorestrict (1 - isometricEmbeddingProjection J)
        (isometricEmbeddingProjection_isStarProjection J hJ).one_sub x) := rfl

@[simp] theorem isometricEmbeddingComplementEquiv_symm_apply (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id)
    (x : HilbertModuleSum B M (ProjectionModule (1 - isometricEmbeddingProjection J))) :
    (isometricEmbeddingComplementEquiv J hJ).symm x = J x.fst + (x.snd : E) := rfl

@[simp] theorem isometricEmbeddingComplementEquiv_embedding (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (m : M) :
    isometricEmbeddingComplementEquiv J hJ (J m) = sumMk m 0 := by
  apply Prod.ext
  · change J.adjoint (J m) = m
    rw [← AdjointableMap.comp_apply J.adjoint J, hJ, AdjointableMap.id_apply]
  · apply Subtype.ext
    exact isometricEmbeddingComplement_embedding_zero J hJ m

@[simp] theorem isometricEmbeddingComplementEquiv_complement (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id)
    (x : ProjectionModule (1 - isometricEmbeddingProjection J)) :
    isometricEmbeddingComplementEquiv J hJ (x : E) = sumMk 0 x := by
  apply Prod.ext
  · exact isometricEmbeddingAdjoint_complement_zero J hJ x
  · apply Subtype.ext
    exact x.property

/-- An operator that acts as S on the embedded module and as identity on the
actual complement becomes the genuine block operator S⊕I under this unitary. -/
theorem isometricEmbeddingComplementEquiv_transport (J : AdjointableMap B M E)
    (hJ : J.adjoint.comp J = AdjointableMap.id)
    (T : AdjointableMap B E E) (S : AdjointableMap B M M)
    (hTJ : ∀ m, T (J m) = J (S m))
    (hTQ : T.comp (1 - isometricEmbeddingProjection J) = 1 - isometricEmbeddingProjection J) :
    (isometricEmbeddingComplementEquiv J hJ).transport T = sumMap S 1 := by
  have ht (z : ProjectionModule (1 - isometricEmbeddingProjection J)) : T (z : E) = (z : E) := by
    have hz := congrArg (fun R : AdjointableMap B E E => R (z : E)) hTQ
    change T ((1 - isometricEmbeddingProjection J) (z : E)) =
      (1 - isometricEmbeddingProjection J) (z : E) at hz
    have hfixed : (1 - isometricEmbeddingProjection J) (z : E) = (z : E) := z.property
    rw [hfixed] at hz
    exact hz
  ext x
  change isometricEmbeddingComplementEquiv J hJ (T (J x.fst + (x.snd : E))) = _
  rw [T.toCLM.map_add, hTJ, ht]
  have hi := (isometricEmbeddingComplementEquiv J hJ).apply_symm_apply (sumMk (S x.fst) x.snd)
  rw [isometricEmbeddingComplementEquiv_symm_apply, sumMk_fst, sumMk_snd] at hi
  simpa only [sumMap_apply, AdjointableMap.one_apply] using hi

end BC4lean.KKTheory
