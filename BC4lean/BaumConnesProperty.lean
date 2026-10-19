import BC4lean.AssemblyModelNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The coefficient-free reduced Baum–Connes property and conjecture statement

The property is bijectivity of the actual canonical assembly map in both
parities. The general conjecture below is a proposition-valued definition,
not an axiom or an assertion that the proposition holds. Its universe parameter
is polymorphic; Lean does not quantify over universes.
-/

universe u
namespace BC4lean.Assembly

variable (Γ : Type u) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- Coefficient-free reduced Baum–Connes for the given countable discrete group,
using Chapter 7's canonical map on the actual geometric-telescope colimit. -/
def BaumConnesProperty : Prop :=
  ∀ p : Bool, Function.Bijective (reducedAssemblyHom Γ p)

/-- The two Boolean parities are exactly the established even and odd maps. -/
theorem baumConnesProperty_iff_even_and_odd :
    BaumConnesProperty Γ ↔
      Function.Bijective (reducedAssemblyEvenHom Γ) ∧
      Function.Bijective (reducedAssemblyOddHom Γ) := by
  constructor
  · intro h
    exact ⟨h false, h true⟩
  · rintro ⟨hEven, hOdd⟩ p
    cases p
    · exact hEven
    · exact hOdd

/-- The unproved general coefficient-free reduced Baum–Connes statement in
one Lean universe. Defining this proposition supplies no proof of it. -/
def BaumConnesConjecture : Prop :=
  ∀ (G : Type u) [Group G] [Countable G]
    [TopologicalSpace G] [DiscreteTopology G], BaumConnesProperty G

end BC4lean.Assembly
