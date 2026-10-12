import BC4lean.InteriorModuleTensorAssociator
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # Grading, action and operator compatibility of the genuine associator

The actual triple-pure-tensor formula and completed tensor extensionality
derive compatibility with semilinear coefficient gradings and group actions.
The induced representation on the right-parenthesized middle tensor is proved
graded and equivariant from the original two left representations. The unitary
also intertwines all actual first-factor operators and representations.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorAssociator

variable {B C D E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

variable (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)

/-- The associator intertwines the actual twice-induced first-factor operator. -/
theorem hilbertEquiv_operator_intertwine (T : AdjointableMap B E E)
    (u : LeftTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ
      (interiorModuleTensorOperator ψ (interiorModuleTensorOperator φ T) u) =
    interiorModuleTensorOperator (rightRepresentation φ ψ) T (hilbertEquiv φ ψ u) := by
  let a := (hilbertEquiv (E := E) φ ψ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : a.comp (interiorModuleTensorOperator ψ (interiorModuleTensorOperator φ T)).toCLM =
      (interiorModuleTensorOperator (rightRepresentation φ ψ) T).toCLM.comp a := by
    apply left_clm_ext φ ψ
    intro x y z
    change hilbertEquiv φ ψ
      (interiorModuleTensorOperator ψ (interiorModuleTensorOperator φ T)
        (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z)) =
      interiorModuleTensorOperator (rightRepresentation φ ψ) T
        (hilbertEquiv φ ψ (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z))
    simp only [interiorModuleTensorOperator_mk, hilbertEquiv_triple]
  exact DFunLike.congr_fun h u

/-- Conjugating by the genuine unitary gives the actual induced first-factor operator. -/
theorem hilbertEquiv_transport_operator (T : AdjointableMap B E E) :
    (hilbertEquiv φ ψ).transport
      (interiorModuleTensorOperator ψ (interiorModuleTensorOperator φ T)) =
    interiorModuleTensorOperator (rightRepresentation φ ψ) T := by
  apply AdjointableMap.ext
  intro u
  rw [HilbertModuleEquiv.transport_apply, hilbertEquiv_operator_intertwine,
    HilbertModuleEquiv.apply_symm_apply]

/-- Any genuine first-factor representation intertwines under reassociation. -/
theorem hilbertEquiv_representation_intertwine {A : Type*} [NonUnitalCStarAlgebra A]
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) (u : LeftTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ
      (interiorModuleTensorOperator ψ (interiorModuleTensorOperator φ (ρ a)) u) =
    interiorModuleTensorOperator (rightRepresentation φ ψ) (ρ a) (hilbertEquiv φ ψ u) :=
  hilbertEquiv_operator_intertwine φ ψ (ρ a) u

section Grading

variable {δB : CStarGrading B} {δC : CStarGrading C} {δD : CStarGrading D}

omit [PartialOrder B] [StarOrderedRing B] in
/-- The actual right-parenthesized middle representation is graded, including
the nontrivial first coefficient automorphism. -/
theorem rightRepresentation_graded
    (K : GradedHilbertModule δC F) (L : GradedHilbertModule δD G)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (hψ : ModuleTensorRepresentationGraded (δB := δC) ψ L) :
    ModuleTensorRepresentationGraded (δB := δB) (rightRepresentation φ ψ)
      (K.interiorTensor L hψ) := by
  intro b w
  let j := (K.interiorTensor L hψ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : j.comp (rightRepresentation φ ψ b).toCLM =
      (rightRepresentation φ ψ (δB.automorphism b)).toCLM.comp j := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext (φ := ψ)
    intro y z
    change (K.interiorTensor L hψ).grading
      (rightRepresentation φ ψ b (interiorModuleTensorMk ψ y z)) =
      rightRepresentation φ ψ (δB.automorphism b)
        ((K.interiorTensor L hψ).grading (interiorModuleTensorMk ψ y z))
    simp only [rightRepresentation_mk, GradedHilbertModule.interiorTensor_grading_mk, hφ b y]
  exact DFunLike.congr_fun h w

/-- The genuine associator intertwines both constructed semilinear tensor gradings. -/
theorem hilbertEquiv_grading_intertwine
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
    (L : GradedHilbertModule δD G)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (hψ : ModuleTensorRepresentationGraded (δB := δC) ψ L)
    (u : LeftTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ (((J.interiorTensor K hφ).interiorTensor L hψ).grading u) =
    (J.interiorTensor (K.interiorTensor L hψ) (rightRepresentation_graded φ ψ K L hφ hψ)).grading
      (hilbertEquiv φ ψ u) := by
  let a := (hilbertEquiv (E := E) φ ψ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let jl := ((J.interiorTensor K hφ).interiorTensor L hψ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let jr := (J.interiorTensor (K.interiorTensor L hψ)
    (rightRepresentation_graded φ ψ K L hφ hψ)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : a.comp jl = jr.comp a := by
    apply left_clm_ext φ ψ
    intro x y z
    change hilbertEquiv φ ψ
      (((J.interiorTensor K hφ).interiorTensor L hψ).grading
        (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z)) =
      (J.interiorTensor (K.interiorTensor L hψ)
        (rightRepresentation_graded φ ψ K L hφ hψ)).grading
          (hilbertEquiv φ ψ (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z))
    simp only [GradedHilbertModule.interiorTensor_grading_mk, hilbertEquiv_triple]
  exact DFunLike.congr_fun h u

end Grading

section Action

variable {Γ : Type*} [Group Γ]
  {α : CStarAlgebraAction Γ B} {β : CStarAlgebraAction Γ C}
  {χ : CStarAlgebraAction Γ D}

omit [PartialOrder B] [StarOrderedRing B] in
/-- The induced middle representation is equivariant for the actual semilinear
tensor action. This is derived from the two original representation laws. -/
theorem rightRepresentation_equivariant
    (V : EquivariantHilbertModule β F) (W : EquivariantHilbertModule χ G)
    (hφ : ModuleTensorRepresentationEquivariant φ α V)
    (hψ : ModuleTensorRepresentationEquivariant ψ β W) :
    ModuleTensorRepresentationEquivariant (rightRepresentation φ ψ) α
      (V.interiorTensor W hψ) := by
  intro g b w
  let j := ((V.interiorTensor W hψ).action g).toContinuousLinearEquiv.toContinuousLinearMap
  have h : j.comp (rightRepresentation φ ψ b).toCLM =
      (rightRepresentation φ ψ (α.automorphism g b)).toCLM.comp j := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext (φ := ψ)
    intro y z
    change (V.interiorTensor W hψ).action g
      (rightRepresentation φ ψ b (interiorModuleTensorMk ψ y z)) =
      rightRepresentation φ ψ (α.automorphism g b)
        ((V.interiorTensor W hψ).action g (interiorModuleTensorMk ψ y z))
    simp only [rightRepresentation_mk, EquivariantHilbertModule.interiorTensor_action_mk, hφ g b y]
  exact DFunLike.congr_fun h w

/-- The actual associator intertwines the two genuine semilinear group actions. -/
theorem hilbertEquiv_action_intertwine
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule β F)
    (W : EquivariantHilbertModule χ G)
    (hφ : ModuleTensorRepresentationEquivariant φ α V)
    (hψ : ModuleTensorRepresentationEquivariant ψ β W)
    (g : Γ) (u : LeftTensor (E := E) φ ψ) :
    hilbertEquiv φ ψ (((U.interiorTensor V hφ).interiorTensor W hψ).action g u) =
    (U.interiorTensor (V.interiorTensor W hψ)
      (rightRepresentation_equivariant φ ψ V W hφ hψ)).action g (hilbertEquiv φ ψ u) := by
  let a := (hilbertEquiv (E := E) φ ψ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let jl := (((U.interiorTensor V hφ).interiorTensor W hψ).action g).toContinuousLinearEquiv.toContinuousLinearMap
  let jr := ((U.interiorTensor (V.interiorTensor W hψ)
    (rightRepresentation_equivariant φ ψ V W hφ hψ)).action g).toContinuousLinearEquiv.toContinuousLinearMap
  have h : a.comp jl = jr.comp a := by
    apply left_clm_ext φ ψ
    intro x y z
    change hilbertEquiv φ ψ
      (((U.interiorTensor V hφ).interiorTensor W hψ).action g
        (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z)) =
      (U.interiorTensor (V.interiorTensor W hψ)
        (rightRepresentation_equivariant φ ψ V W hφ hψ)).action g
          (hilbertEquiv φ ψ (interiorModuleTensorMk ψ (interiorModuleTensorMk φ x y) z))
    simp only [EquivariantHilbertModule.interiorTensor_action_mk, hilbertEquiv_triple]
  exact DFunLike.congr_fun h u

end Action
end BC4lean.KKTheory.InteriorModuleTensorAssociator
