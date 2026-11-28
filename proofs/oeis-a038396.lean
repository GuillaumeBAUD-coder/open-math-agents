import OMAStatements.S_oeis_a038396
import Mathlib

/-!
Every term from a(1) = 2 on is 2 modulo 4: the prepended block 2(n+1)·10^L has L ≥ 1, so it is a
multiple of 4. A power b^k with k ≥ 2 is never 2 modulo 4 (it is a multiple of 4 if b is even, odd
otherwise), so no term is a perfect power.
-/

namespace R038396
open OMA.S_oeis_a038396

theorem mod4 (n : ℕ) : a (n + 1) % 4 = 2 := by
  induction n with
  | zero =>
    show (2 * (0 + 1) * 10 ^ (Nat.digits 10 (a 0)).length + a 0) % 4 = 2
    simp [a]
  | succ n ih =>
    have hpos : 0 < a (n + 1) := by omega
    obtain ⟨L, hL⟩ : ∃ L, (Nat.digits 10 (a (n + 1))).length = L + 1 := by
      rw [Nat.digits_def' (by norm_num) hpos]
      exact ⟨_, rfl⟩
    show (2 * (n + 1 + 1) * 10 ^ (Nat.digits 10 (a (n + 1))).length + a (n + 1)) % 4 = 2
    rw [hL, show 2 * (n + 1 + 1) * 10 ^ (L + 1) = 4 * ((n + 2) * 10 ^ L * 5) by ring]
    generalize (n + 2) * 10 ^ L * 5 = X
    omega

end R038396

theorem OMA.solution : type_of% @OMA.S_oeis_a038396.main := by
  rintro n hn ⟨b, k, hk, h⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h4 := R038396.mod4 m
  rw [h] at h4
  rcases Nat.even_or_odd b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have h44 : 4 ∣ (c + c) ^ k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      exact ⟨c ^ 2 * (c + c) ^ j, by ring⟩
    omega
  · obtain ⟨d, hd⟩ : Odd ((2 * c + 1) ^ k) := Odd.pow ⟨c, rfl⟩
    omega
