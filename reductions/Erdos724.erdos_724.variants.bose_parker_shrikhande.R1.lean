import FormalConjectures.ErdosProblems.«724»

-- Reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1 of Erdős Problem 724 — bose parker shrikhande
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Two orthogonal Latin squares of every order `n ≥ 7`, split by `n mod 4`

* `H1`: odd orders. The squares `i + j` and `i + 2j` (mod `n`) are orthogonal when `n` is odd.
* `H2`: orders divisible by `4` (MacNeish-type products of finite-field constructions).
* `H3`: orders `n ≡ 2 (mod 4)`, `n ≥ 10`: the theorem of Bose, Parker and Shrikhande proper.
-/

namespace OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1

open Erdos724 Finset

/-- Odd orders `n ≥ 3` have a pair of orthogonal Latin squares. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n → ∃ L M : LatinSquare n, L ≠ M ∧ IsOrthogonal L M

/-- Orders divisible by `4` have a pair of orthogonal Latin squares. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ∣ n → 4 ≤ n → ∃ L M : LatinSquare n, L ≠ M ∧ IsOrthogonal L M

/-- Orders `n ≡ 2 (mod 4)` with `n ≥ 10` have a pair of orthogonal Latin squares. -/
def H3 : Prop :=
  ∀ n : ℕ, n % 4 = 2 → 10 ≤ n → ∃ L M : LatinSquare n, L ≠ M ∧ IsOrthogonal L M

lemma two_le_maxMOLS {n : ℕ} (h : ∃ L M : LatinSquare n, L ≠ M ∧ IsOrthogonal L M) :
    2 ≤ maxMOLS n := by
  classical
  obtain ⟨L, M, hne, hLM⟩ := h
  refine le_csSup ⟨Fintype.card (LatinSquare n), ?_⟩ ⟨{L, M}, card_pair hne, ?_⟩
  · rintro k ⟨S, rfl, -⟩
    exact card_le_univ S
  · rw [coe_pair, Set.pairwise_pair]
    exact fun _ ↦ ⟨hLM, fun p q hpq ↦ hLM (congrArg Prod.swap hpq)⟩

theorem main : H1 → H2 → H3 →
    type_of% @Erdos724.erdos_724.variants.bose_parker_shrikhande := by
  intro h1 h2 h3 n hn
  apply two_le_maxMOLS
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ := he
    rcases Nat.even_or_odd m with hm | hm
    · exact h2 _ (by obtain ⟨j, rfl⟩ := hm; exact ⟨j, by ring⟩) (by omega)
    · exact h3 _ (by obtain ⟨j, rfl⟩ := hm; omega) (by obtain ⟨j, rfl⟩ := hm; omega)
  · exact h1 n ho (by omega)

end OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1
