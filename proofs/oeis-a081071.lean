import OMAStatements.S_oeis_a081071

-- Problem: A081071, Lucas(4n+2) - 2 = F(4n+3) + Sum_{k=2..2n} F(2k) for n >= 1.
-- Credit: @ShoQo
-- Proof: L(m+1) = F(m) + F(m+2) and Sum_{k=1..m} F(2k) = F(2m+1) - 1.

open OMA.S_oeis_a081071

namespace OMA_A081071_Proof

lemma lucas_succ (n : ℕ) : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [lucas]
    | 1, _ => simp [lucas, Nat.fib_add_two]
    | (m + 2), ih =>
      rw [lucas, ih (m + 1) (by omega), ih m (by omega)]
      simp only [Nat.fib_add_two]; ring

lemma sum_fib_even (m : ℕ) : ∑ k ∈ Finset.Icc 1 m, Nat.fib (2 * k) + 1 = Nat.fib (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_right_comm, ih,
      show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, Nat.fib_add_two,
      show 2 * (m + 1) = 2 * m + 2 by ring, Nat.fib_add_two (n := 2 * m)]

end OMA_A081071_Proof

open OMA_A081071_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a081071.main := by
  intro n hn
  have hs := sum_fib_even (2 * n)
  have hsplit : ∑ k ∈ Finset.Icc 1 (2 * n), Nat.fib (2 * k)
      = Nat.fib 2 + ∑ k ∈ Finset.Icc 2 (2 * n), Nat.fib (2 * k) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega)]
    rfl
  rw [hsplit, show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at hs
  have hl := lucas_succ (4 * n + 1)
  have hf2 : Nat.fib 2 = 1 := rfl
  have hf3 : Nat.fib (4 * n + 3) = Nat.fib (4 * n + 1) + Nat.fib (4 * n + 2) := Nat.fib_add_two
  unfold a
  rw [show 4 * n + 2 = 4 * n + 1 + 1 by ring, hl, show 4 * n + 1 + 2 = 4 * n + 3 by ring]
  omega

