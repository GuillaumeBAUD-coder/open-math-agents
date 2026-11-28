import OMAStatements.S_oeis_a283107
import Mathlib

-- Problem oeis-a283107: for k >= 2, if sigma(4(k-1)) is prime then tau(4(k-1)) is prime.
-- Upstream: statements/oeis-a283107.lean (declaration OMA.S_oeis_a283107.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: write n = 4(k-1) = 2^e * m with m odd. Since sigma is multiplicative,
-- sigma(n) = (2^(e+1) - 1) * sigma(m). A prime product has a factor equal to 1.
-- If 2^(e+1) - 1 = 1 then e = 0 and n = m would be odd, impossible. So sigma(m) = 1, hence m = 1, n = 2^e,
-- and 2^(e+1) - 1 is prime. A Mersenne number 2^r - 1 is prime only for prime r, so e + 1 is prime,
-- and tau(2^e) = e + 1.

open ArithmeticFunction

private lemma geom_two_a283107 (n : ℕ) : ∑ j ∈ Finset.range n, 2 ^ j = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Finset.sum_range_succ, ih, pow_succ]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a283107.main := by
  intro k hk hσ
  have hn : 4 * (k - 1) ≠ 0 := by omega
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  rw [he] at hσ ⊢
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow Nat.prime_two,
    geom_two_a283107] at hσ
  rcases Nat.prime_mul_iff.mp hσ with ⟨hP, h1⟩ | ⟨_, h1⟩
  · have hm1 : m = 1 := (sigma_eq_one_iff 1 m).mp h1
    have he1 : e + 1 ≠ 1 := by
      intro h0
      have h00 : e = 0 := by omega
      subst h00
      norm_num at hP
    have hprime := (Nat.prime_of_pow_sub_one_prime he1 hP).2
    rw [hm1, mul_one, sigma_zero_apply_prime_pow Nat.prime_two]
    exact hprime
  · exfalso
    rcases Nat.eq_zero_or_pos e with he0 | hpos
    · subst he0
      obtain ⟨t, ht⟩ := hm
      simp at he
      omega
    · have h4 : 2 ^ 2 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h4
      omega
