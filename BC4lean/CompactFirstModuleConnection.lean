import BC4lean.GradedConnectionDefectAlgebra
import BC4lean.GradingConjugateOperator
import BC4lean.CompactModuleCountableApproximateUnit

/-! # Compact first actions and genuinely localized signed connections

The first compact algebra is handled through its actual closed rank-one
span. A signed connection has compact graded commutators with every first
compact operator. Square and action defects need only be compact on the
creation ranges of the localized first action; a genuine compact
approximate unit then gives the required whole-tensor localized defects.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter TopologicalSpace
open scoped InnerProductSpace Topology

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {δB : CStarGrading B}

/-- The two actual signed all-vector connection identities, including
the independent adjoint identity. -/
structure IsSignedModuleConnection (J : GradedHilbertModule δB E)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (S : AdjointableMap C F F)
    (G : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) : Prop where
  creation (x : E) : IsModuleCompact (G.comp (moduleCreationMap φ x) -
    (moduleCreationMap φ (J.grading x)).comp S)
  creation_adjoint (x : E) : IsModuleCompact ((star G).comp (moduleCreationMap φ x) -
    (moduleCreationMap φ (J.grading x)).comp (star S))

namespace IsSignedModuleConnection
variable {J : GradedHilbertModule δB E}
  {φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F} {S : AdjointableMap C F F}
  {G : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}
  (hG : IsSignedModuleConnection J φ S G)

include hG in
theorem adjoint_creation (y : E) :
    IsModuleCompact (S.comp (moduleCreationMap φ y).adjoint -
      (moduleCreationMap φ (J.grading y)).adjoint.comp G) := by
  have hsub (T R : AdjointableMap C F (InteriorModuleTensor (E := E) φ)) :
      (T - R).adjoint = T.adjoint - R.adjoint := by
    apply AdjointableMap.toCLM_injective
    change (T - R).adjointCLM = (T.adjoint - R.adjoint).toCLM
    rw [AdjointableMap.toCLM_sub]
    exact AdjointableMap.adjointCLM_sub T R
  have h := (hG.creation_adjoint (J.grading y)).adjoint.neg
  simpa only [hsub, AdjointableMap.adjoint_comp,
    ← AdjointableMap.star_eq_adjoint, star_star, J.grading_sq, neg_sub] using h

include hG in
theorem graded_commutator_rankOne (x y : E) :
    IsModuleCompact (G * interiorModuleTensorOperator φ (moduleRankOne (B := B) x y) -
      interiorModuleTensorOperator φ (J.conjugateOperator (moduleRankOne (B := B) x y)) * G) := by
  rw [J.conjugateOperator_rankOne, interiorModuleTensorOperator_rankOne,
    interiorModuleTensorOperator_rankOne]
  have h := ((hG.creation x).comp_right (moduleCreationMap φ y).adjoint).add
    ((hG.adjoint_creation y).comp_left (moduleCreationMap φ (J.grading x)))
  convert h using 1
  ext z
  simp only [AdjointableMap.mul_apply, AdjointableMap.comp_apply,
    AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply, map_sub]
  abel

include hG in
/-- The genuine closed rank-one span extends the compact signed
commutator to every actual first compact operator. -/
theorem graded_commutator_compact {L : AdjointableMap B E E} (hL : IsModuleCompact L) :
    IsModuleCompact (G * interiorModuleTensorOperator φ L -
      interiorModuleTensorOperator φ (J.conjugateOperator L) * G) := by
  let σ := J.conjugateOperatorStarAlgEquiv
  let f : AdjointableMap B E E →ₗ[ℂ]
      AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) := {
    toFun := fun L => G * interiorModuleTensorOperator φ L - interiorModuleTensorOperator φ (σ L) * G
    map_add' := fun L K => by
      change G * (interiorModuleTensorOperatorHom φ) (L + K) -
          (interiorModuleTensorOperatorHom φ) (σ (L + K)) * G =
        (G * (interiorModuleTensorOperatorHom φ) L -
          (interiorModuleTensorOperatorHom φ) (σ L) * G) +
        (G * (interiorModuleTensorOperatorHom φ) K -
          (interiorModuleTensorOperatorHom φ) (σ K) * G)
      simp only [map_add, mul_add, add_mul]
      abel
    map_smul' := fun r L => by
      change G * (interiorModuleTensorOperatorHom φ) (r • L) -
          (interiorModuleTensorOperatorHom φ) (σ (r • L)) * G =
        r • (G * (interiorModuleTensorOperatorHom φ) L -
          (interiorModuleTensorOperatorHom φ) (σ L) * G)
      simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_sub] }
  have hσ : Continuous σ := (NonUnitalStarAlgHom.isometry σ σ.injective).continuous
  have hf : Continuous f := by
    exact (continuous_const.mul (interiorModuleTensorOperatorCLM φ).continuous).sub
      (((interiorModuleTensorOperatorCLM φ).continuous.comp hσ).mul continuous_const)
  let K := (moduleCompact C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) φ)).comap f
  have hK : IsClosed (K : Set (AdjointableMap B E E)) := moduleCompact_isClosed.preimage hf
  exact moduleCompact_le_of_isClosed K hK (fun x y => hG.graded_commutator_rankOne x y) hL

include hG in
/-- The square connection calculation uses both actual grading signs;
only the displayed second defect on this creation range is needed. -/
theorem square_comp_creation (x : E)
    (hlocal : IsModuleCompact ((moduleCreationMap φ x).comp (S * S - 1))) :
    IsModuleCompact ((G * G - 1).comp (moduleCreationMap φ x)) := by
  have h := (((hG.creation x).comp_left G).add
    ((hG.creation (J.grading x)).comp_right S)).add hlocal
  convert h using 1
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.mul_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    J.grading_sq, map_sub]
  abel

end IsSignedModuleConnection

theorem IsSignedModuleConnection.gradedKasparovConnection
    {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    {γ : CStarAlgebraAction Γ C} {δA : CStarGrading A} {δC : CStarGrading C}
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    {G : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hG : IsSignedModuleConnection c.grading d.representation d.operator G) :
    GradedKasparovConnection c d G := by
  constructor
  · intro x hx
    simpa only [hx, neg_sub] using (hG.creation x).neg
  · intro x hx
    simpa only [hx, neg_sub] using (hG.creation_adjoint x).neg
  · intro x hx
    have h := hG.creation x
    rw [hx, moduleCreationMap_neg] at h
    convert h using 1
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
    abel
  · intro x hx
    have h := hG.creation_adjoint x
    rw [hx, moduleCreationMap_neg] at h
    convert h using 1
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
    abel

theorem ModuleParsevalFrame.gradedConnection_isSignedModuleConnection
    {ξ : ℕ → E} (P : ModuleParsevalFrame (B := B) ξ)
    (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (p : ℕ → Bool) (hξ : ∀ n, J.grading (ξ n) = if p n then -ξ n else ξ n)
    (S : AdjointableMap C F F)
    (hS : ∀ b, IsModuleCompact (S * φ b - φ (δB.automorphism b) * S)) :
    IsSignedModuleConnection J φ S (P.gradedConnection φ p S) := by
  have hmain (T : AdjointableMap C F F)
      (hT : ∀ b, IsModuleCompact (T * φ b - φ (δB.automorphism b) * T)) (x : E) :
      IsModuleCompact ((P.gradedConnection φ p T).comp (moduleCreationMap φ x) -
        (moduleCreationMap φ (J.grading x)).comp T) := by
    apply creationConnection_compact_of_homogeneous J φ T (P.gradedConnection φ p T)
    · intro y hy
      simpa only [Bool.false_eq_true, if_false, neg_sub] using
        (P.gradedConnection_comp_creation_sub_compact J φ p hξ T hT y false
          (by simpa only [Bool.false_eq_true, if_false] using hy)).neg
    · intro y hy
      have h := P.gradedConnection_comp_creation_sub_compact J φ p hξ T hT y true
        (by simpa only [if_true] using hy)
      convert h using 1
      ext z
      simp only [if_true, AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
        AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply, map_neg]
      abel
  constructor
  · exact hmain S hS
  · intro x
    change IsModuleCompact ((P.gradedConnection φ p S).adjoint.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S.adjoint)
    rw [P.gradedConnection_adjoint]
    exact hmain S.adjoint (graded_coefficient_commutator_adjoint_compact φ S hS) x

section ActionLocalization
variable {Γ : Type*} [Group Γ] {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (J : GradedHilbertModule δB E) (U : EquivariantHilbertModule β E)
  (V : EquivariantHilbertModule γ F) (hU : U.PreservesGrading J)
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (hφ : ModuleTensorRepresentationEquivariant φ β V)
  {S : AdjointableMap C F F}
  {G : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}

include hU in
theorem IsSignedModuleConnection.action_comp_creation
    (hG : IsSignedModuleConnection J φ S G) (g : Γ) (x : E)
    (hlocal : IsModuleCompact ((moduleCreationMap φ (J.grading x)).comp
      (V.conjugateOperator g S - S))) :
    IsModuleCompact (((U.interiorTensor V hφ).conjugateOperator g G - G).comp
      (moduleCreationMap φ x)) := by
  let W := U.interiorTensor V hφ
  let D := fun y : E => G.comp (moduleCreationMap φ y) -
    (moduleCreationMap φ (J.grading y)).comp S
  have heq : (W.conjugateOperator g G - G).comp (moduleCreationMap φ x) =
      V.conjugateMap W g (D (U.action g⁻¹ x)) +
        (moduleCreationMap φ (J.grading x)).comp (V.conjugateOperator g S - S) - D x := by
    have hW (k : Γ) (z : E) (w : F) :
        W.action k (moduleCreationMap φ z w) =
          moduleCreationMap φ (U.action k z) (V.action k w) := by
      change (U.interiorTensor V hφ).action k (interiorModuleTensorMk φ z w) =
        interiorModuleTensorMk φ (U.action k z) (V.action k w)
      exact EquivariantHilbertModule.interiorTensor_action_mk U V hφ k z w
    ext y
    simp only [D, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_add_apply, EquivariantHilbertModule.conjugateMap_apply]
    have hJ : U.action g (J.grading (U.action g⁻¹ x)) = J.grading x :=
      (hU g (U.action g⁻¹ x)).trans
        (congrArg J.grading (U.apply_inv_apply g x))
    simp only [hW, map_sub, hJ]
    abel
  rw [heq]
  exact (((hG.creation (U.action g⁻¹ x)).conjugateMap V W g).add hlocal).sub (hG.creation x)

end ActionLocalization

/-- Compactness of the actual second adjoint-square compression is the
exact rectangular criterion needed for a localized creation range. -/
theorem moduleCreationMap_comp_isModuleCompact_of_inner_local
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (T : AdjointableMap C F F)
    (hlocal : IsModuleCompact ((star T) * φ (MulOpposite.unop ⟪x, x⟫_(Bᵐᵒᵖ)) * T)) :
    IsModuleCompact ((moduleCreationMap φ x).comp T) := by
  apply (isModuleCompact_iff_adjoint_comp_self _).2
  convert hlocal using 1
  rw [AdjointableMap.adjoint_comp, AdjointableMap.comp_assoc,
    ← AdjointableMap.comp_assoc (moduleCreationMap φ x).adjoint (moduleCreationMap φ x),
    moduleCreationMap_adjoint_comp]
  rfl

/-- A closed rank-one preimage and an actual first compact AU promote
localized creation compactness to the required whole-tensor localization. -/
theorem tensorCompact_left_localization [SeparableSpace B]
    (hE : IsCountablyGeneratedModule B E)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (L : AdjointableMap B E E) (hL : IsModuleCompact L)
    (hlocal : ∀ x : E, IsModuleCompact (T.comp (moduleCreationMap φ (L x)))) :
    IsModuleCompact (T * interiorModuleTensorOperator φ L) := by
  let f := (AdjointableMap.compLeftContinuousLinearMap T).comp
    ((interiorModuleTensorOperatorCLM φ).comp (AdjointableMap.compLeftContinuousLinearMap L))
  let K := (moduleCompact C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) φ)).comap f.toLinearMap
  have hK : IsClosed (K : Set (AdjointableMap B E E)) := moduleCompact_isClosed.preimage f.continuous
  have hθ (x y : E) : moduleRankOne (B := B) x y ∈ K := by
    change IsModuleCompact (T.comp (interiorModuleTensorOperator φ (L.comp (moduleRankOne x y))))
    rw [comp_moduleRankOne, interiorModuleTensorOperator_rankOne, ← AdjointableMap.comp_assoc]
    exact (hlocal x).comp_right (moduleCreationMap φ y).adjoint
  have hcompact := moduleCompact_le_of_isClosed K hK hθ
  obtain ⟨e, _, _, _, _, hleft, _, _⟩ := exists_countablyGenerated_compact_approximateUnit hE
  let LC : CompactModuleOperator B E := ⟨L, hL⟩
  have hlim := continuous_subtype_val.tendsto LC |>.comp (hleft LC)
  have hpost := ((AdjointableMap.compLeftContinuousLinearMap T).comp
    (interiorModuleTensorOperatorCLM φ)).continuous.tendsto L |>.comp hlim
  apply moduleCompact_isClosed.mem_of_tendsto hpost
  apply Eventually.of_forall
  intro n
  exact hcompact (e n).property

end BC4lean.KKTheory
