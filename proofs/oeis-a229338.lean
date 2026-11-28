import OMAStatements.S_oeis_a229338

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: each element of s lies in 2^(|s|-1) subsets, so the square of the powerset product is
-- (prod s)^(2^|s|); with (prod of divisors)^2 = n^tau this gives the formula after taking square roots.

open OMA.S_oeis_a229338

namespace P_oeis_a229338

lemma pow_sq_aux (s : Finset ℕ) :
    (∏ t ∈ s.powerset, ∏ d ∈ t, d) * (∏ t ∈ s.powerset, ∏ d ∈ t, d)
      = (∏ d ∈ s, d) ^ (2 ^ s.card) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_powerset_insert hx, Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    have h2 : ∏ t ∈ s.powerset, ∏ d ∈ insert x t, d
        = x ^ (2 ^ s.card) * ∏ t ∈ s.powerset, ∏ d ∈ t, d := by
      rw [← Finset.card_powerset, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun t ht => ?_)
      have : x ∉ t := fun h => hx (Finset.mem_powerset.mp ht h)
      rw [Finset.prod_insert this]
    rw [h2, pow_succ, mul_pow, pow_mul, pow_mul, ← ih]
    ring

lemma div_sq (n : ℕ) : (∏ d ∈ n.divisors, d) * (∏ d ∈ n.divisors, d) = n ^ n.divisors.card := by
  conv_lhs => arg 2; rw [← Nat.prod_div_divisors n (fun d => d)]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_const]
  refine Finset.prod_congr rfl (fun d hd => ?_)
  exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)

theorem main_proved :
    ∀ n : ℕ, 1 ≤ n → a n = n ^ (n.divisors.card * 2 ^ (n.divisors.card - 2)) := by
  intro n hn
  by_cases h1 : n = 1
  · subst h1; simp [a]
  have ht : 2 ≤ n.divisors.card := by
    have h1' : 1 ∈ n.divisors := by simp; omega
    have hn' : n ∈ n.divisors := by simp; omega
    have : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rw [Finset.card_pair (Ne.symm h1)] at this
    exact this
  obtain ⟨k, hk⟩ : ∃ k, n.divisors.card = k + 2 := ⟨n.divisors.card - 2, by omega⟩
  have hsq : a n ^ 2 = (n ^ (n.divisors.card * 2 ^ (n.divisors.card - 2))) ^ 2 := by
    rw [sq, a, pow_sq_aux, ← pow_mul, hk]
    have e : 2 ^ (k + 2) = 2 * 2 ^ (k+1) := by ring
    rw [e, pow_mul, sq, div_sq, hk, ← pow_mul]
    congr 1
    simp only [Nat.add_sub_cancel]
    ring
  exact Nat.pow_left_injective (by norm_num) hsq

end P_oeis_a229338

theorem OMA.solution : type_of% @OMA.S_oeis_a229338.main := P_oeis_a229338.main_proved
