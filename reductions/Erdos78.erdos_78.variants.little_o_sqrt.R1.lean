import FormalConjectures.ErdosProblems.«78»

/-! # A finite base graph and its hexadecimal lexicographic powers -/
-- Credit: @steveDOTdigital
namespace OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1
open Erdos78 Filter ComplexityTheory
open scoped Asymptotics

-- The first unequal hexadecimal digits decide adjacency using quadratic residues modulo 17.
def H1 : Prop := ∃ color : ℕ → ℕ → Bool,
    IsPolyTime (fun p : List Bool × ℕ × ℕ => color p.2.1 p.2.2) ∧
    ∀ u v : ℕ, color u v =
      (if u = v then false else if u%16 = v%16 then color (u/16) (v/16)
       else decide (((u%16+17-v%16)%17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ)))

-- In each digit, a homogeneous set occupies at most three of the sixteen classes.
def H2 : Prop := ∀ color : ℕ → ℕ → Bool,
    (∀ u v : ℕ, color u v =
      (if u = v then false else if u%16 = v%16 then color (u/16) (v/16)
       else decide (((u%16+17-v%16)%17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ)))) →
    ∀ d n : ℕ, n ≤ 16^d →
      NoHomogeneousSet (explicitGraph (fun p => color p.2.1 p.2.2) n) (3^d+1)

-- The digit bound grows strictly more slowly than the square root of the graph order.
def H3 : Prop := ∃ f : ℕ → ℝ, f =o[atTop] (fun n ↦ Real.sqrt (n : ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, ∃ d : ℕ, n ≤ 16^d ∧ 3^d+1 ≤ ⌈f n⌉₊

theorem main : H1 → H2 → H3 → type_of% @Erdos78.erdos_78.variants.little_o_sqrt := by
  rintro ⟨color,poly,rule⟩ powers ⟨f,limit,eventually⟩
  refine ⟨f,limit,(fun p => color p.2.1 p.2.2),poly,?_⟩
  filter_upwards [eventually] with n hn
  obtain ⟨d,nd,fd⟩ := hn
  obtain ⟨cl,ind⟩ := powers color rule d n nd
  exact ⟨cl.mono fd,ind.mono fd⟩

end OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1
