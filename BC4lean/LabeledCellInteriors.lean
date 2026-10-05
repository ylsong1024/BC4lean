import BC4lean.LabeledCellAttachment

/-! # Uniqueness of orbit-disk points outside the attaching skeleton -/
noncomputable section
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
open LabeledOrbitSimplex LabeledOrbitRealization

/-- Away from the preceding skeleton, an orbit disk recovers its exact simplex
orbit and coset from the active support. -/
theorem labeledCellCharacteristic_support {n : ℕ} (q : CellOrbit Γ n)
    (p : OrbitCell (cellStabilizer q) (TopCat.disk.{u} n))
    (hx : labeledCellCharacteristic q p ∉ skeletalCarrier n) :
    supportSimplex (labeledCellCharacteristic q p) = (cellOrbitSimplex q p.1).val := by
  rcases p with ⟨a,d⟩
  induction a using QuotientGroup.induction_on with
  | H g =>
    let s := (cellRepresentative q).val
    let w := (representativeDiskHomeomorph q).symm d.down
    have hw : ∀ v ∈ s.vertices, w.val v ≠ 0 := by
      intro v hv hz
      apply hx
      apply skeletalCarrier_smul _ g
      have hm := labeledChartBoundary_mem_skeletal s w ⟨v,hv,hz⟩
      have hc : s.vertices.card = n + 1 := (cellRepresentative q).property
      change chart s w ∈ skeletalCarrier n
      simpa only [hc, Nat.add_sub_cancel] using hm
    change supportSimplex (g • chart s w) = (g • cellRepresentative q).val
    rw [supportSimplex_smul, (supportSimplex_chart_eq_iff s w).mpr hw]
    rfl

/-- The full coproduct of orbit disks has no identifications outside its sphere
attaching locus. Different orbit indices, cosets, and disk points are recovered. -/
theorem labeledDiskSum_injective_interior (n : ℕ) :
    Set.InjOn (labeledDiskSum (Γ := Γ) n)
      {p | (labeledDiskSum n p).val ∉ skeletalCarrier n} := by
  classical
  rintro ⟨q,⟨a,d⟩⟩ hx ⟨r,⟨b,d'⟩⟩ hy he
  have hv := congrArg Subtype.val he
  change labeledCellCharacteristic q (a,d) = labeledCellCharacteristic r (b,d') at hv
  have hs := congrArg supportSimplex hv
  rw [labeledCellCharacteristic_support q (a,d) hx,
    labeledCellCharacteristic_support r (b,d') hy] at hs
  have hp : (⟨q,a⟩ : Σ q : CellOrbit Γ n, Γ ⧸ cellStabilizer q) = ⟨r,b⟩ :=
    cellOrbitSimplex_sigma_injective n (Subtype.ext hs)
  have hqr : q = r := congrArg Sigma.fst hp
  subst r
  have hab : a = b := eq_of_heq (Sigma.mk.inj_iff.mp hp).2
  subst b
  have hd : d = d' := by
    induction a using QuotientGroup.induction_on with
    | H g =>
      change g • chart (cellRepresentative q).val ((representativeDiskHomeomorph q).symm d.down) =
        g • chart (cellRepresentative q).val ((representativeDiskHomeomorph q).symm d'.down) at hv
      have hc := (MulAction.injective g) hv
      have hw := (chart_isClosedEmbedding (cellRepresentative q).val).injective hc
      apply ULift.ext
      exact (representativeDiskHomeomorph q).symm.injective hw
  subst d'
  rfl

end BC4lean.ProperActions
