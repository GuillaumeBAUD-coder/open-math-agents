import OMAStatements.S_oeis_a067076
import Mathlib

-- Problem: A067076: Numbers k such that 2*k + 3 is a prime.
-- Upstream: formal-conjectures statements/oeis-a067076.lean:0 (declaration OMA.S_oeis_a067076.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a067076 in
theorem OMA.solution : type_of% @OMA.S_oeis_a067076.main := by
  have h4 : ∀ k : ℕ, ¬ (2 * k + 3 + 1).Prime := by
    intro k h
    have := h.eq_one_or_self_of_dvd 2 ⟨k + 2, by ring⟩
    omega
  have hq : ∀ k : ℕ, Nat.count (fun j => (2 * j + 3).Prime) k + 1
      = Nat.count Nat.Prime (2 * k + 3) := by
    intro k
    induction k with
    | zero => norm_num [Nat.count_succ]
    | succ k ih =>
      rw [Nat.count_succ _ k, show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 by ring,
        Nat.count_succ _ (2 * k + 3 + 1), Nat.count_succ _ (2 * k + 3), if_neg (h4 k)]
      beta_reduce
      split_ifs <;> omega
  have hE : ∀ k : ℕ, ((Finset.range (2 * k + 3)).filter (fun m => 0 < m ∧ Even m)).card
      = k + 1 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [Finset.card_filter] at ih ⊢
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      have h1 : ¬ (0 < 2 * k + 3 ∧ Even (2 * k + 3)) := by
        rintro ⟨-, h⟩
        rw [Nat.even_iff] at h
        omega
      have h2 : (0 < 2 * k + 3 + 1 ∧ Even (2 * k + 3 + 1)) :=
        ⟨by omega, by rw [Nat.even_iff]; omega⟩
      rw [if_neg h1, if_pos h2]
  have hO : ∀ k : ℕ,
      ((Finset.range (2 * k + 3)).filter (fun m => Odd m ∧ 1 < m ∧ ¬ m.Prime)).card
        + Nat.count Nat.Prime (2 * k + 3) = k + 1 := by
    intro k
    induction k with
    | zero =>
      rw [Finset.card_filter]
      norm_num [Finset.sum_range_succ, Nat.count_succ, Nat.odd_iff]
      intro x hx1 hx2 hx3
      omega
    | succ k ih =>
      rw [Finset.card_filter] at ih ⊢
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, Nat.count_succ _ (2 * k + 3 + 1), Nat.count_succ _ (2 * k + 3),
        if_neg (h4 k)]
      have ho : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
      have hne : ¬ Odd (2 * k + 3 + 1) := by
        rw [Nat.odd_iff]
        omega
      have e1 : (if (Odd (2 * k + 3 + 1) ∧ 1 < 2 * k + 3 + 1 ∧ ¬ (2 * k + 3 + 1).Prime)
          then 1 else 0 : ℕ) = 0 := if_neg (fun h => hne h.1)
      rw [e1]
      by_cases hp : (2 * k + 3).Prime
      · have e2 : (if (Odd (2 * k + 3) ∧ 1 < 2 * k + 3 ∧ ¬ (2 * k + 3).Prime)
            then 1 else 0 : ℕ) = 0 := if_neg (fun h => h.2.2 hp)
        rw [e2, if_pos hp]
        omega
      · have e2 : (if (Odd (2 * k + 3) ∧ 1 < 2 * k + 3 ∧ ¬ (2 * k + 3).Prime)
            then 1 else 0 : ℕ) = 1 := if_pos ⟨ho, by omega, hp⟩
        rw [e2, if_neg hp]
        omega
  intro n hn
  have hP : (Nat.nth Nat.Prime n).Prime := Nat.prime_nth_prime n
  have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime n :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
  have h2 : 2 ≤ Nat.nth Nat.Prime 0 := (Nat.prime_nth_prime 0).two_le
  have hodd : Nat.nth Nat.Prime n % 2 = 1 := by
    rcases hP.eq_two_or_odd with h | h
    · omega
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, Nat.nth Nat.Prime n = 2 * k + 3 :=
    ⟨(Nat.nth Nat.Prime n - 3) / 2, by omega⟩
  have hcount : Nat.count Nat.Prime (2 * k + 3) = n := by
    rw [← hk]
    exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime n
  have hpk : (2 * k + 3).Prime := hk ▸ hP
  have ha : a n = k := by
    unfold a
    have hc : Nat.count (fun j => (2 * j + 3).Prime) k = n - 1 := by
      have := hq k
      omega
    rw [← hc]
    exact Nat.nth_count (p := fun j => (2 * j + 3).Prime) hpk
  have hprime : prime (n + 1) = 2 * k + 3 := by
    unfold prime
    rw [Nat.add_sub_cancel]
    exact hk
  have h1 : A008507 n + n = k + 1 := by
    unfold A008507
    rw [hprime]
    have := hO k
    omega
  have h2' : A005097 n = k + 1 := by
    unfold A005097
    rw [hprime]
    omega
  have h3 : A102781 (n + 1) = k + 1 := by
    unfold A102781
    rw [hprime]
    exact hE k
  rw [ha, h2', h3]
  refine ⟨?_, ?_, ?_⟩
  · have : (A008507 n : ℤ) + n = k + 1 := by exact_mod_cast h1
    linarith
  · push_cast
    ring
  · push_cast
    ring
