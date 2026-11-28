import OMAStatements.S_oeis_a131626

open Nat in
theorem OMA.solution : type_of% @OMA.S_oeis_a131626.main := fun x _ => by
  have c (N : ℕ) (h : 3 ∣ N) (l : 3 < N) : ¬ N.Prime := fun p => by have := p.eq_one_or_self_of_dvd 3 h; omega
  have q (n p : ℕ) (h : count Nat.Prime p = n) (hp : p.Prime) : nth Nat.Prime n = p := h ▸ nth_count hp
  rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h
  · exact ⟨0, by rw [nth_prime_zero_eq_two, nth_prime_one_eq_three]; exact c _ (by omega) (by omega)⟩
  · exact ⟨8, by rw [q 8 23 (by decide) (by norm_num), q 9 29 (by decide) (by norm_num)]; exact c _ (by omega) (by omega)⟩
  · exact ⟨2, by rw [nth_prime_two_eq_five, nth_prime_three_eq_seven]; exact c _ (by omega) (by omega)⟩
