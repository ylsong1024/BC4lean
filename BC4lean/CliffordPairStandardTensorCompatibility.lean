import BC4lean.CliffordPairStandardTensor
import BC4lean.GradedEquivariantInteriorModuleTensor
import BC4lean.StandardHilbertModuleActions
import BC4lean.CliffordExternalEvenTensor
import BC4lean.CliffordExternalEvenRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Whole Clifford pair compatibility of actual coefficient extension



The completed, onto coefficient-form unitary itself is the existing
`CliffordPairStandardTensor.hilbertEquiv`. These are its remaining grading
and group-action identities. Both coefficient maps and source representations
may be degenerate. The group action on the second standard module may be
the actual left regular multiplier action; it need not be an algebra action
on the vectors. No group unitary is inserted into a nonunital algebra.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordPairStandardTensor
open scoped InnerProductSpace

variable {B C H : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H]
  [CStarModule Bᵐᵒᵖ H] [CompleteSpace H]
  (f : B →⋆ₙₐ[ℂ] C)

omit [PartialOrder B] [StarOrderedRing B] in
theorem representation_graded :
    ModuleTensorRepresentationGraded (δB := cliffordCoefficientGrading)
      (representation f) (GradedHilbertModule.standard cliffordCoefficientGrading) := by
  intro b y
  change MulOpposite.op (cliffordCoefficientGrading.automorphism
      (cliffordCoordinateHom f b * MulOpposite.unop y)) =
    MulOpposite.op (cliffordCoordinateHom f (cliffordCoefficientGrading.automorphism b) *
      cliffordCoefficientGrading.automorphism (MulOpposite.unop y))
  rw [map_mul]
  rfl

def sourceGrading : GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (C × C))
      (Source (H := H) f) :=
  cliffordPairGrading.interiorTensor
    (GradedHilbertModule.standard cliffordCoefficientGrading) (representation_graded f)

/-- In odd expansion both complete Clifford gradings are the actual swap. -/
theorem hilbertEquiv_grading (z : Source (H := H) f) :
    hilbertEquiv f ((sourceGrading f).grading z) =
      cliffordPairGrading.grading (hilbertEquiv f z) := by
  let W := (hilbertEquiv (H := H) f).toAdjointable.toCLM
  let L := (sourceGrading (H := H) f).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (cliffordPairGrading (B := C)
    (H := InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f))).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp L = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv f ((sourceGrading f).grading
      (interiorModuleTensorMk (representation f) x y)) =
        cliffordPairGrading.grading
          (hilbertEquiv f (interiorModuleTensorMk (representation f) x y))
    rw [sourceGrading, GradedHilbertModule.interiorTensor_grading_mk,
      hilbertEquiv_mk, hilbertEquiv_mk]
    rfl
  exact DFunLike.congr_fun h z

def baseGrading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) H) :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
      (InteriorModuleTensor (E := H) (standardCoefficientImageRepresentation f)) :=
  J.interiorTensor GradedHilbertModule.trivial (fun _ _ => rfl)

def externalSourceGrading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) H) :
    GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (C × C))
      (Source (H := H) f) :=
  (cliffordExternalEvenGrading J).interiorTensor
    (GradedHilbertModule.standard cliffordCoefficientGrading) (representation_graded f)

private theorem hilbertEquiv_external_grading_mk_aux
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) H)
    (x : CliffordPairModule B H) (y : (C × C)ᵐᵒᵖ) :
    hilbertEquiv f ((externalSourceGrading f J).grading
      (interiorModuleTensorMk (representation f) x y)) =
      (cliffordExternalEvenGrading (baseGrading f J)).grading
        (hilbertEquiv f (interiorModuleTensorMk (representation f) x y)) := by
  have hs : (externalSourceGrading f J).grading
      (interiorModuleTensorMk (representation f) x y) =
      interiorModuleTensorMk (representation f)
        ((cliffordExternalEvenGrading J).grading x)
        ((GradedHilbertModule.standard
          (cliffordCoefficientGrading : CStarGrading (C × C))).grading y) :=
    GradedHilbertModule.interiorTensor_grading_mk (φ := representation f)
      (cliffordExternalEvenGrading J)
      (GradedHilbertModule.standard (cliffordCoefficientGrading : CStarGrading (C × C)))
      (representation_graded f) x y
  have ht : (cliffordExternalEvenGrading (baseGrading f J)).grading (bilinear f x y) =
      bilinear f ((cliffordExternalEvenGrading J).grading x)
        ((GradedHilbertModule.standard
          (cliffordCoefficientGrading : CStarGrading (C × C))).grading y) := by
    apply Prod.ext
    · change (baseGrading f J).grading
          (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.2
            (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)) =
        interiorModuleTensorMk (standardCoefficientImageRepresentation f) (J.grading x.2)
          (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)
      exact GradedHilbertModule.interiorTensor_grading_mk
        (φ := standardCoefficientImageRepresentation f) J
        (GradedHilbertModule.trivial (B := C) (E := Cᵐᵒᵖ))
        (fun _ _ => rfl) x.2 (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)
    · change (baseGrading f J).grading
          (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x.1
            (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)) =
        interiorModuleTensorMk (standardCoefficientImageRepresentation f) (J.grading x.1)
          (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)
      exact GradedHilbertModule.interiorTensor_grading_mk
        (φ := standardCoefficientImageRepresentation f) J
        (GradedHilbertModule.trivial (B := C) (E := Cᵐᵒᵖ))
        (fun _ _ => rfl) x.1 (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)
  exact (congrArg (fun u : Source (H := H) f => hilbertEquiv f u) hs).trans
    ((hilbertEquiv_mk f _ _).trans
      ((congrArg (fun v : Target (H := H) f =>
        (cliffordExternalEvenGrading (baseGrading f J)).grading v)
          (hilbertEquiv_mk f x y)).trans ht).symm)

/-- The Koszul external even grading includes the original J in both slots. -/
theorem hilbertEquiv_external_grading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) H)
    (z : Source (H := H) f) :
    hilbertEquiv f ((externalSourceGrading f J).grading z) =
      (cliffordExternalEvenGrading (baseGrading f J)).grading (hilbertEquiv f z) := by
  let W := (hilbertEquiv (H := H) f).toAdjointable.toCLM
  let L := (externalSourceGrading f J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (cliffordExternalEvenGrading (baseGrading f J)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp L = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv f ((externalSourceGrading f J).grading
      (interiorModuleTensorMk (representation f) x y)) =
        (cliffordExternalEvenGrading (baseGrading f J)).grading
          (hilbertEquiv f (interiorModuleTensorMk (representation f) x y))
    exact hilbertEquiv_external_grading_mk_aux f J x y
  exact DFunLike.congr_fun h z

section Action
variable {Γ : Type*} [Group Γ]
  {β : CStarAlgebraAction Γ B} {η : CStarAlgebraAction Γ C}
  (U : EquivariantHilbertModule β H) (V : EquivariantHilbertModule η Cᵐᵒᵖ)
  (hf : ModuleTensorRepresentationEquivariant (standardCoefficientImageRepresentation f) β V)

/-- The coordinatewise action on the genuine standard product module.
This accepts an actual semilinear module action V, including left λ_g. -/
def standardPairActionIsometry (g : Γ) : (C × C)ᵐᵒᵖ ≃ₗᵢ[ℂ] (C × C)ᵐᵒᵖ where
  toFun y := MulOpposite.op
    (MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop y).1)),
      MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop y).2)))
  invFun y := MulOpposite.op
    (MulOpposite.unop (V.action g⁻¹ (MulOpposite.op (MulOpposite.unop y).1)),
      MulOpposite.unop (V.action g⁻¹ (MulOpposite.op (MulOpposite.unop y).2)))
  left_inv y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · change MulOpposite.unop
        (V.action g⁻¹ (V.action g (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))) =
          (MulOpposite.unop y).1
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        (V.inv_apply_apply g (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
    · change MulOpposite.unop
        (V.action g⁻¹ (V.action g (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))) =
          (MulOpposite.unop y).2
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        (V.inv_apply_apply g (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))
  right_inv y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · change MulOpposite.unop
        (V.action g (V.action g⁻¹ (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))) =
          (MulOpposite.unop y).1
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        (V.apply_inv_apply g (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
    · change MulOpposite.unop
        (V.action g (V.action g⁻¹ (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))) =
          (MulOpposite.unop y).2
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        (V.apply_inv_apply g (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))
  map_add' x y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · change MulOpposite.unop (V.action g
        ((MulOpposite.op (MulOpposite.unop x).1 : Cᵐᵒᵖ) +
          (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))) =
        MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop x).1 : Cᵐᵒᵖ)) +
          MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        ((V.action g).map_add (MulOpposite.op (MulOpposite.unop x).1 : Cᵐᵒᵖ)
          (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
    · change MulOpposite.unop (V.action g
        ((MulOpposite.op (MulOpposite.unop x).2 : Cᵐᵒᵖ) +
          (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))) =
        MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop x).2 : Cᵐᵒᵖ)) +
          MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        ((V.action g).map_add (MulOpposite.op (MulOpposite.unop x).2 : Cᵐᵒᵖ)
          (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))
  map_smul' a y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · change MulOpposite.unop
        (V.action g (a • (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))) =
        a • MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        ((V.action g).map_smul a (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
    · change MulOpposite.unop
        (V.action g (a • (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))) =
        a • MulOpposite.unop (V.action g (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        ((V.action g).map_smul a (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))
  norm_map' y := by
    change max ‖V.action g (MulOpposite.op (MulOpposite.unop y).1)‖
        ‖V.action g (MulOpposite.op (MulOpposite.unop y).2)‖ =
      max ‖(MulOpposite.unop y).1‖ ‖(MulOpposite.unop y).2‖
    rw [(V.action g).norm_map, (V.action g).norm_map]
    rfl

def standardPairAction :
    EquivariantHilbertModule (cliffordCoefficientAction η) (C × C)ᵐᵒᵖ where
  action :=
    { toFun := standardPairActionIsometry V
      map_one' := by
        ext y
        apply MulOpposite.unop_injective
        apply Prod.ext
        · change MulOpposite.unop
            (V.action 1 (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)) =
              (MulOpposite.unop y).1
          exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
            (V.one_apply (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
        · change MulOpposite.unop
            (V.action 1 (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)) =
              (MulOpposite.unop y).2
          exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
            (V.one_apply (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))
      map_mul' g h := by
        ext y
        apply MulOpposite.unop_injective
        apply Prod.ext
        · change MulOpposite.unop
            (V.action (g * h) (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)) =
            MulOpposite.unop
              (V.action g (V.action h (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)))
          exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
            (V.mul_apply g h (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
        · change MulOpposite.unop
            (V.action (g * h) (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)) =
            MulOpposite.unop
              (V.action g (V.action h (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)))
          exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
            (V.mul_apply g h (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)) }
  inner_action g x y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · change MulOpposite.unop
        (⟪V.action g (MulOpposite.op (MulOpposite.unop x).1 : Cᵐᵒᵖ),
          V.action g (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ)) =
        MulOpposite.unop (opStarAlgEquiv (η.automorphism g)
          ⟪(MulOpposite.op (MulOpposite.unop x).1 : Cᵐᵒᵖ),
            (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ))
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        (V.inner_action g (MulOpposite.op (MulOpposite.unop x).1 : Cᵐᵒᵖ)
          (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
    · change MulOpposite.unop
        (⟪V.action g (MulOpposite.op (MulOpposite.unop x).2 : Cᵐᵒᵖ),
          V.action g (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ)) =
        MulOpposite.unop (opStarAlgEquiv (η.automorphism g)
          ⟪(MulOpposite.op (MulOpposite.unop x).2 : Cᵐᵒᵖ),
            (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)⟫_(Cᵐᵒᵖ))
      exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
        (V.inner_action g (MulOpposite.op (MulOpposite.unop x).2 : Cᵐᵒᵖ)
          (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))

omit [PartialOrder B] [StarOrderedRing B] in
include hf in
theorem representation_equivariant :
    ModuleTensorRepresentationEquivariant (representation f) (cliffordCoefficientAction β)
      (standardPairAction V) := by
  intro g b y
  apply MulOpposite.unop_injective
  apply Prod.ext
  · change MulOpposite.unop (V.action g
      ((standardCoefficientImageRepresentation f b.1)
        (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))) =
      MulOpposite.unop
        ((standardCoefficientImageRepresentation f (β.automorphism g b.1))
          (V.action g (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ)))
    exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
      (hf g b.1 (MulOpposite.op (MulOpposite.unop y).1 : Cᵐᵒᵖ))
  · change MulOpposite.unop (V.action g
      ((standardCoefficientImageRepresentation f b.2)
        (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))) =
      MulOpposite.unop
        ((standardCoefficientImageRepresentation f (β.automorphism g b.2))
          (V.action g (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ)))
    exact congrArg (MulOpposite.unop : Cᵐᵒᵖ → C)
      (hf g b.2 (MulOpposite.op (MulOpposite.unop y).2 : Cᵐᵒᵖ))

/-- The actual full diagonal action is intertwined on every completed vector. -/
theorem hilbertEquiv_action (g : Γ) (z : Source (H := H) f) :
    hilbertEquiv f (((cliffordPairAction U).interiorTensor (standardPairAction V)
      (representation_equivariant f V hf)).action g z) =
      (cliffordPairAction (U.interiorTensor V hf)).action g (hilbertEquiv f z) := by
  let W := (hilbertEquiv (H := H) f).toAdjointable.toCLM
  let L := ((cliffordPairAction U).interiorTensor (standardPairAction V)
    (representation_equivariant f V hf)).action g
  let K := (cliffordPairAction (U.interiorTensor V hf)).action g
  have h : W.comp L.toContinuousLinearEquiv.toContinuousLinearMap =
      K.toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change hilbertEquiv f
      (((cliffordPairAction U).interiorTensor (standardPairAction V)
        (representation_equivariant f V hf)).action g
          (interiorModuleTensorMk (representation f) x y)) =
      (cliffordPairAction (U.interiorTensor V hf)).action g
        (hilbertEquiv f (interiorModuleTensorMk (representation f) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk, hilbertEquiv_mk, hilbertEquiv_mk]
    apply Prod.ext <;>
      exact (EquivariantHilbertModule.interiorTensor_action_mk U V hf g _ _).symm
  exact DFunLike.congr_fun h z
end Action

/-- The odd expansion operator retains its actual minus sign. -/
theorem hilbertEquiv_odd_operator (T : AdjointableMap B H H) (z : Source (H := H) f) :
    hilbertEquiv f (interiorModuleTensorOperator (representation f) (cliffordPairMap T (-T)) z) =
      cliffordPairMap
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T)
        (-(interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T))
          (hilbertEquiv f z) := by
  simpa only [← interiorModuleTensorOperatorHom_apply, map_neg] using
    hilbertEquiv_operator f T (-T) z

end BC4lean.KKTheory.CliffordPairStandardTensor
