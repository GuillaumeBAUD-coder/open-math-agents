import OMAStatements.S_oeis_a280523

-- Problem: A280523, F(2n+1) - n = A215004(2n-2).
-- Credit: @ShoQo
-- Proof: by two-step induction, A215004(m) = F(m+3) - floor((m+1)/2) - 1; at m = 2n-2 this is
-- F(2n+1) - n.

open OMA.S_oeis_a280523

namespace OMA_A280523_Proof

lemma b_closed (m : ℕ) : b m = (Nat.fib (m + 3) : ℤ) - ((m + 1) / 2 : ℕ) - 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [b, Nat.fib_add_two]
    | 1, _ => simp [b, Nat.fib_add_two]
    | (k + 2), ih =>
      rw [b, ih (k + 1) (by omega), ih k (by omega),
        show k + 2 + 3 = (k + 3) + 2 by ring, Nat.fib_add_two (n := k + 3),
        show k + 1 + 3 = k + 4 by ring, show k + 3 + 1 = k + 4 by ring]
      have h1 : (k + 2 + 1) / 2 = (k + 1) / 2 + 1 := by omega
      have h2 : (k + 1 + 1) / 2 = (k + 2) / 2 := by omega
      rw [h1, h2]; simp only [Nat.cast_add, Nat.cast_one]; ring

end OMA_A280523_Proof

open OMA_A280523_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a280523.main := by
  intro n hn
  rw [b_closed, a, show 2 * n - 2 + 3 = 2 * n + 1 by omega, show (2 * n - 2 + 1) / 2 = n - 1 by omega]
  push_cast [Nat.cast_sub hn]
  ring

