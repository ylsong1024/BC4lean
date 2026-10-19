import BC4lean.CompactModelColimitCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Finite-group point-model and assembly formula comparisons.
The lifted point is a proper model in the group universe. This reduction
does not assert assembly bijectivity for every finite group. -/

noncomputable section
universe u
namespace BC4lean.Chapter8Examples
open ProperActions KKTheory
open scoped ZeroAtInfty ComplexOrder KasparovDescent

/-- A one-point carrier in the arbitrary common group/space universe. -/
def FiniteGroupPoint : Type u := ULift.{u} Unit

instance finiteGroupPoint_unique : Unique FiniteGroupPoint.{u} :=
  inferInstanceAs (Unique (ULift.{u} Unit))

instance finiteGroupPoint_topologicalSpace : TopologicalSpace FiniteGroupPoint.{u} := ⊥

instance finiteGroupPoint_discreteTopology : DiscreteTopology FiniteGroupPoint.{u} := ⟨rfl⟩

instance finiteGroupPoint_mulAction (Γ : Type u) [Group Γ] :
    MulAction Γ FiniteGroupPoint.{u} where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance finiteGroupPoint_continuousConstSMul (Γ : Type u) [Group Γ] :
    ContinuousConstSMul Γ FiniteGroupPoint.{u} where
  continuous_const_smul _ := continuous_id

/-- The whole subgroup fixed-point space of the actual lifted point is contractible. -/
theorem finiteGroupPoint_fixedPoints_contractible (Γ : Type u) [Group Γ]
    (H : Subgroup Γ) : ContractibleSpace (FixedPointSpace H FiniteGroupPoint.{u}) := by
  let : Nonempty (FixedPointSpace H FiniteGroupPoint.{u}) :=
    ⟨⟨default, fun _ => rfl⟩⟩
  infer_instance

/-- The lifted point satisfies the proper-model fixed-point criterion for finite groups. -/
theorem finiteGroupPoint_fixedPointCriterion (Γ : Type u) [Group Γ] [Finite Γ] :
    FixedPointCriterion Γ FiniteGroupPoint.{u} := by
  refine ⟨fun H _ => finiteGroupPoint_fixedPoints_contractible Γ H, ?_⟩
  intro H hH
  let := hH
  exact False.elim (not_finite H)

instance finiteGroupPoint_proper (Γ : Type u) [Group Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] [Finite Γ] :
    ProperSMul Γ FiniteGroupPoint.{u} := by
  let : ContinuousSMul Γ FiniteGroupPoint.{u} := ⟨continuous_of_discreteTopology⟩
  exact ProperActions.proper_of_finite

variable (Γ : Type u) [Group Γ] [Finite Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- A genuine global fixed point of Chapter 4's canonical model, obtained
from its proved fixed-point criterion at the finite top subgroup. -/
def finiteCanonicalGlobalFixedPoint :
    FixedPointSpace (⊤ : Subgroup Γ) (LabeledOrbitTelescope.Model Γ) := by
  letI : ContractibleSpace
      (FixedPointSpace (⊤ : Subgroup Γ) (LabeledOrbitTelescope.Model Γ)) :=
    (LabeledOrbitTelescope.fixedPointCriterion Γ).1 ⊤ inferInstance
  exact (Classical.choice (ContractibleSpace.hequiv_unit
    (FixedPointSpace (⊤ : Subgroup Γ) (LabeledOrbitTelescope.Model Γ)))).invFun ()

def finiteCanonicalToPoint :
    EquivariantMap Γ (LabeledOrbitTelescope.Model Γ) FiniteGroupPoint.{u} where
  toFun _ := default
  continuous_toFun := continuous_const
  map_smul' _ _ := rfl

def finitePointToCanonical :
    EquivariantMap Γ FiniteGroupPoint.{u} (LabeledOrbitTelescope.Model Γ) where
  toFun _ := (finiteCanonicalGlobalFixedPoint Γ).val
  continuous_toFun := continuous_const
  map_smul' g _ :=
    ((finiteCanonicalGlobalFixedPoint Γ).property ⟨g, Subgroup.mem_top g⟩).symm

/-- Finite groups admit an actual equivariant homotopy equivalence from
the canonical telescope to the same-universe one-point model. -/
def finiteCanonicalPointHomotopyEquiv :
    EquivariantHomotopyEquiv Γ (LabeledOrbitTelescope.Model Γ) FiniteGroupPoint.{u} where
  toMap := finiteCanonicalToPoint Γ
  invMap := finitePointToCanonical Γ
  left_inv :=
    ((LabeledOrbitTelescope.equivariantCWComplex Γ).homotopyTerminal
      (LabeledOrbitTelescope.fixedPointCriterion Γ)).2 _ _
  right_inv := by
    have h : (finiteCanonicalToPoint Γ).comp (finitePointToCanonical Γ) =
        EquivariantMap.id := by
      apply EquivariantMap.ext
      intro x
      exact Subsingleton.elim _ _
    rw [h]
    exact EquivariantlyHomotopic.refl _

/-- The actual finite-group canonical topological group is computed by
the actual point-model topological colimit, in either parity. -/
def finiteCanonicalPointKHomologyEquiv (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ ≃+
      TopologicalKHomology.group (Γ := Γ) (X := FiniteGroupPoint.{u}) p := by
  letI : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) := LabeledOrbitTelescope.proper Γ
  exact TopologicalKHomology.homotopyEquiv p (finiteCanonicalPointHomotopyEquiv Γ)

/-- The real point colimit further collapses to full equivariant KK of the point. -/
def finiteTopologicalPointSpaceEquiv (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ ≃+
      TopologicalKHomology.spaceGroup p Γ FiniteGroupPoint.{u} :=
  (finiteCanonicalPointKHomologyEquiv Γ p).trans
    (compactSpaceGroupEquiv Γ FiniteGroupPoint.{u} p)

/-- A genuine normalized compact cutoff on the actual finite-group point model. -/
def finitePointCutoff : Cutoff.CutoffFunction Γ FiniteGroupPoint.{u} :=
  Classical.choice (Cutoff.exists_cutoffFunction (Γ := Γ) (X := FiniteGroupPoint.{u}))

/-- The constructed canonical assembly value is exactly preserved by the
constructed finite-group model comparison. -/
theorem reducedAssemblyHom_finitePointColimit (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x =
      Assembly.assemblyHom Γ FiniteGroupPoint.{u} p
        (finiteCanonicalPointKHomologyEquiv Γ p x) := by
  let : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) := LabeledOrbitTelescope.proper Γ
  exact (Assembly.assemblyHom_homotopyEquiv Γ (LabeledOrbitTelescope.Model Γ)
    FiniteGroupPoint.{u} p (finiteCanonicalPointHomotopyEquiv Γ) x).symm

/-- The real canonical assembly map for a finite group reduces to the real
point cutoff/product/descent map, not to an assumed isomorphism. -/
theorem reducedAssemblyHom_finitePoint (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x =
      Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{u} p (finitePointCutoff Γ)
        (finiteTopologicalPointSpaceEquiv Γ p x) := by
  exact (reducedAssemblyHom_finitePointColimit Γ p x).trans
    (assemblyHom_eq_compactSpaceAssembly Γ FiniteGroupPoint.{u} p (finitePointCutoff Γ)
      (finiteCanonicalPointKHomologyEquiv Γ p x))

/-- The reduction retains the exact actual analytic comparison, cutoff native
product and descended class, in both degrees. Averaging is not replaced by a unit. -/
theorem reducedAssemblyHom_finitePoint_formula (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x =
      Assembly.reducedScalarKKToAnalyticHom Γ p
        (Assembly.cutoffProductHom Γ FiniteGroupPoint.{u} p (finitePointCutoff Γ)
          (KasparovDescent.classHom
            (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := FiniteGroupPoint.{u})) p
            (finiteTopologicalPointSpaceEquiv Γ p x))) := by
  rw [reducedAssemblyHom_finitePoint]
  rfl

end BC4lean.Chapter8Examples
