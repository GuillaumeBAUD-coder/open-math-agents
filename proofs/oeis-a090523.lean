import OMAStatements.S_oeis_a090523
import Mathlib

/-!
# A090523: no term is zero for n > 2

Bertrand gives a prime p with n!/4 < p ≤ 2·floor(n!/4). Then 2p ≤ n! < 4p, so floor(n!/p) is 2
or 3, a prime; and 0 is not prime, so the infimum is not 0 (the Bertrand argument in the entry).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a090523.main := by
  intro n hn
  unfold OMA.S_oeis_a090523.a
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h | h
  · simp at h; exact Nat.not_prime_zero h
  · set N := n.factorial
    have hN : 6 ≤ N := by
      have h3 := Nat.factorial_le (show 3 ≤ n by omega)
      have : Nat.factorial 3 = 6 := rfl
      omega
    obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 4) (by omega)
    have h1 : N < 4 * p := by
      have := (Nat.div_lt_iff_lt_mul (show 0 < 4 by norm_num)).mp hlt
      linarith
    have h2 : 2 * p ≤ N := by omega
    have hq : N / p = 2 ∨ N / p = 3 := by
      have hp0 : 0 < p := hp.pos
      have hlo : 2 ≤ N / p := (Nat.le_div_iff_mul_le hp0).mpr (by linarith)
      have hhi : N / p < 4 := (Nat.div_lt_iff_lt_mul hp0).mpr (by linarith)
      omega
    have hmem : p ∈ {p : ℕ | p.Prime ∧ (N / p).Prime} := by
      refine ⟨hp, ?_⟩
      rcases hq with hq | hq <;> rw [hq] <;> norm_num
    rw [h] at hmem
    exact hmem
