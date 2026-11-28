import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1
import Mathlib

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.H1.R1.H2.R1
-- of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.H1.R1.H2
-- Credit: @arindale

/-!
# Symbol length one in degree two modulo three: two symbols, then merging

The target says that every class of `K^M_2(C(x, y))/3` is a single symbol.  The literature proof
uses two independent ingredients:

* Matzri's bound for `C_2` fields: every class of `K^M_2(F)/3` is a sum of at most
  `1 * (3^(2-1) - 1) = 2` symbols;
* the period-index theorem over a complex surface function field together with Wedderburn's
  theorem, which merges a sum of two symbols into one symbol (the corresponding exponent-three
  algebra has index three and is cyclic).

We state these two pieces separately.  The main implication is a case split on the number of
symbols in Matzri's representation: zero or one symbol is already within the bound, and two
symbols are merged by the second hypothesis.
-/

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1_H2_R1

open MilnorK

/-- Matzri's bound: every class of `K^M_2(C(x, y))/3` is a sum of at most two symbols. -/
def H1 : Prop :=
  ∀ x ∈ MilnorK.grade (MvRatFunc (Fin 2) ℂ) 3 2,
    ∃ k ≤ 2, ∃ s : Fin k → Fin 2 → (MvRatFunc (Fin 2) ℂ)ˣ,
      x = ∑ i, MilnorK.symbol 3 (s i)

/-- A sum of two symbols in `K^M_2(C(x, y))/3` is itself a single symbol. -/
def H2 : Prop :=
  ∀ s : Fin 2 → Fin 2 → (MvRatFunc (Fin 2) ℂ)ˣ,
    ∃ e f : (MvRatFunc (Fin 2) ℂ)ˣ,
      ∑ i : Fin 2, MilnorK.symbol 3 (s i) = MilnorK.symbol 3 ![e, f]

theorem main : H1 → H2 →
    OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1.H2 := by
  intro h1 h2 x hx
  obtain ⟨k, hk, s, hs⟩ := h1 x hx
  interval_cases k
  · exact ⟨0, Nat.zero_le 1, s, hs⟩
  · exact ⟨1, le_rfl, s, hs⟩
  · obtain ⟨e, f, hef⟩ := h2 s
    refine ⟨1, le_rfl, fun _ => ![e, f], ?_⟩
    rw [Fin.sum_univ_one]
    exact hs.trans hef

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1_H2_R1
