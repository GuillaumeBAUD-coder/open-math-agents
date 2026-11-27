import OMAStatements.S_oeis_a163617
import Mathlib

/-!
# OEIS A163617 in terms of the binary reflected Gray code

The sequence is defined by `a(0) = 0`, `a(2m) = 2 a(m)`, `a(2m+1) = 2 a(m) + 2 + (-1)^m`. We show

  `4 a(n) = 4 g(n) + 6 n + 1 - (-1)^n`,   where `g(n) = n XOR ⌊n/2⌋` is the Gray code.

The Gray code obeys a recursion of the same shape: comparing the last bit and the remaining
bits of `n XOR ⌊n/2⌋` gives

  `g(n) = 2 g(⌊n/2⌋) + ((n + ⌊n/2⌋) mod 2)`.

With this, the claim follows by strong induction on `n`: after writing `(-1)^k` as
`1 - 2 (k mod 2)`, each parity case is a linear identity.
-/

open OMA.S_oeis_a163617

namespace OMA.A163617

/-- The recursion for the Gray code `g n = n ^^^ (n / 2)`. -/
lemma gray_eq (n : ℕ) :
    n ^^^ (n / 2) = 2 * ((n / 2) ^^^ (n / 2 / 2)) + (n + n / 2) % 2 := by
  have h := Nat.div_add_mod (n ^^^ (n / 2)) 2
  rw [Nat.xor_div_two, Nat.xor_mod_two_eq] at h
  exact h.symm

/-- `(-1) ^ n` in terms of the last binary digit of `n`. -/
lemma neg_one_pow_eq (n : ℕ) : (-1 : ℤ) ^ n = 1 - 2 * ((n % 2 : ℕ) : ℤ) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, (Nat.even_iff.2 h).neg_one_pow]; norm_num
  · rw [h, (Nat.odd_iff.2 h).neg_one_pow]; norm_num

/-- Unfolding the recursion at a positive argument. -/
lemma a_succ (n : ℕ) : a (n + 1) =
    if (n + 1) % 2 = 0 then 2 * a ((n + 1) / 2)
    else 2 * a ((n + 1) / 2) + 2 + (-1) ^ ((n + 1) / 2) := by
  rw [a]

end OMA.A163617

open OMA.A163617 in
theorem OMA.solution : type_of% @OMA.S_oeis_a163617.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | k
    · simp [a]
    · -- induction hypothesis at `⌊(k+1)/2⌋`, and the Gray code recursion, both over `ℤ`
      have ih' := ih ((k + 1) / 2) (by omega)
      have hg : ((((k + 1) ^^^ ((k + 1) / 2) : ℕ)) : ℤ)
          = 2 * ((((k + 1) / 2) ^^^ ((k + 1) / 2 / 2) : ℕ) : ℤ)
            + (((k + 1 + (k + 1) / 2) % 2 : ℕ) : ℤ) := by
        exact_mod_cast gray_eq (k + 1)
      rw [neg_one_pow_eq] at ih' ⊢
      rw [a_succ, hg]
      split_ifs with hpar
      · omega
      · rw [neg_one_pow_eq]
        omega
