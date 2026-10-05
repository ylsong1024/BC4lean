import BC4lean.LabeledOrbitSimplices

/-! # Orbit representatives of labeled simplices -/
noncomputable section
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ]
namespace LabeledOrbitSimplex

theorem card_smul (g : Γ) (s : LabeledOrbitSimplex Γ) :
    (g • s).vertices.card = s.vertices.card := by
  classical
  exact Finset.card_image_of_injective _ (MulAction.injective g)

/-- The simplices whose interiors are cells of dimension `n`. -/
def DimensionSimplex (Γ : Type*) [Group Γ] (n : ℕ) :=
  {s : LabeledOrbitSimplex Γ // s.vertices.card = n + 1}

instance (n : ℕ) : MulAction Γ (DimensionSimplex Γ n) where
  smul g s := ⟨g • s.val, (card_smul g s.val).trans s.property⟩
  one_smul s := Subtype.ext (one_smul Γ s.val)
  mul_smul g h s := Subtype.ext (mul_smul g h s.val)

/-- Exactly one index for each orbit of `n`-dimensional simplices. -/
abbrev CellOrbit (Γ : Type*) [Group Γ] (n : ℕ) :=
  Quotient (MulAction.orbitRel Γ (DimensionSimplex Γ n))

/-- A chosen representative retains the full nonempty simplex. -/
def cellRepresentative {n : ℕ} (q : CellOrbit Γ n) : DimensionSimplex Γ n := q.out

theorem cellRepresentative_nonempty {n : ℕ} (q : CellOrbit Γ n) :
    (cellRepresentative q).val.vertices.Nonempty := by
  apply Finset.card_pos.mp
  rw [(cellRepresentative q).property]
  exact Nat.succ_pos n

/-- The finite isotropy group belonging to each orbit-cell index. -/
def cellStabilizer {n : ℕ} (q : CellOrbit Γ n) : Subgroup Γ :=
  MulAction.stabilizer Γ (cellRepresentative q).val

instance {n : ℕ} (q : CellOrbit Γ n) : Finite (cellStabilizer q) :=
  stabilizer_finite _ (cellRepresentative_nonempty q)

theorem dimension_stabilizer_eq (n : ℕ) (s : DimensionSimplex Γ n) :
    MulAction.stabilizer Γ s = MulAction.stabilizer Γ s.val := by
  ext g
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

/-- Every simplex is a translate of its orbit's chosen representative. -/
theorem exists_smul_cellRepresentative {n : ℕ} (s : DimensionSimplex Γ n) :
    ∃ g : Γ, g • cellRepresentative (Quotient.mk _ s) = s := by
  have hrel : MulAction.orbitRel Γ (DimensionSimplex Γ n)
      s (cellRepresentative (Quotient.mk _ s)) :=
    Quotient.exact (Quotient.out_eq' (Quotient.mk _ s)).symm
  exact MulAction.mem_orbit_iff.mp hrel

/-- The simplex set decomposes into its actual homogeneous orbit cells. -/
def dimensionSimplexEquivOrbits (n : ℕ) :
    DimensionSimplex Γ n ≃ Σ q : CellOrbit Γ n, Γ ⧸ cellStabilizer q := by
  have he := MulAction.selfEquivSigmaOrbitsQuotientStabilizer Γ (DimensionSimplex Γ n)
  simpa only [cellStabilizer, cellRepresentative, dimension_stabilizer_eq] using he

/-- Send an actual orbit coset to its simplex, without a representative choice
for the coset. -/
def cellOrbitSimplex {n : ℕ} (q : CellOrbit Γ n) (a : Γ ⧸ cellStabilizer q) :
    DimensionSimplex Γ n := by
  refine ⟨MulAction.ofQuotientStabilizer Γ (cellRepresentative q).val a, ?_⟩
  refine Quotient.inductionOn' a (fun g => ?_)
  exact (card_smul g (cellRepresentative q).val).trans (cellRepresentative q).property

@[simp] theorem cellOrbitSimplex_mk {n : ℕ} (q : CellOrbit Γ n) (g : Γ) :
    cellOrbitSimplex q (QuotientGroup.mk g) = g • cellRepresentative q := rfl

theorem cellOrbitSimplex_smul {n : ℕ} (q : CellOrbit Γ n)
    (g : Γ) (a : Γ ⧸ cellStabilizer q) :
    cellOrbitSimplex q (g • a) = g • cellOrbitSimplex q a := by
  apply Subtype.ext
  exact MulAction.ofQuotientStabilizer_smul Γ (cellRepresentative q).val g a

theorem cellOrbitSimplex_injective {n : ℕ} (q : CellOrbit Γ n) :
    Function.Injective (cellOrbitSimplex q) := by
  intro a b hab
  exact MulAction.injective_ofQuotientStabilizer Γ (cellRepresentative q).val
    (congrArg Subtype.val hab)

/-- Every simplex belongs to exactly one of the indexed homogeneous orbits. -/
theorem cellOrbitSimplex_surjective (n : ℕ) :
    Function.Surjective (fun p : Σ q : CellOrbit Γ n, Γ ⧸ cellStabilizer q =>
      cellOrbitSimplex p.1 p.2) := by
  intro s
  obtain ⟨g, hg⟩ := exists_smul_cellRepresentative s
  exact ⟨⟨Quotient.mk _ s, QuotientGroup.mk g⟩, hg⟩

@[simp] theorem cellOrbitSimplex_quotient {n : ℕ} (q : CellOrbit Γ n)
    (a : Γ ⧸ cellStabilizer q) : Quotient.mk _ (cellOrbitSimplex q a) = q := by
  refine Quotient.inductionOn' a (fun g => ?_)
  rw [cellOrbitSimplex_mk]
  calc
    Quotient.mk _ (g • cellRepresentative q) = Quotient.mk _ (cellRepresentative q) :=
      Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)
    _ = q := Quotient.out_eq' q

theorem cellOrbitSimplex_sigma_injective (n : ℕ) :
    Function.Injective (fun p : Σ q : CellOrbit Γ n, Γ ⧸ cellStabilizer q =>
      cellOrbitSimplex p.1 p.2) := by
  rintro ⟨q, a⟩ ⟨r, b⟩ hab
  have hqr : q = r := by
    have h := congrArg (Quotient.mk (MulAction.orbitRel Γ (DimensionSimplex Γ n))) hab
    simpa only [cellOrbitSimplex_quotient] using h
  subst r
  exact congrArg (Sigma.mk q) (cellOrbitSimplex_injective q hab)

/-- The explicit orbit parametrization is a bijection, with its computational
formula and equivariance available independently of the chosen inverse. -/
def cellOrbitSimplexEquiv (n : ℕ) :
    (Σ q : CellOrbit Γ n, Γ ⧸ cellStabilizer q) ≃ DimensionSimplex Γ n :=
  Equiv.ofBijective _ ⟨cellOrbitSimplex_sigma_injective n, cellOrbitSimplex_surjective n⟩

end LabeledOrbitSimplex
end BC4lean.ProperActions
