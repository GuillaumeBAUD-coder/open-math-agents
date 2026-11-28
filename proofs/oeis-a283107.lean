import OMAStatements.S_oeis_a283107
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic

open ArithmeticFunction

private theorem sum_two_powers (i : ℕ) :
    (∑ j ∈ Finset.range i, 2 ^ j) = mersenne i := by
  induction i with
  | zero => simp [mersenne]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [mersenne, pow_succ]
    have := pow_pos (by decide : 0 < (2 : ℕ)) i
    omega

private theorem self_le_sigma {n : ℕ} (hn : n ≠ 0) : n ≤ sigma 1 n := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors.mpr ⟨dvd_rfl, hn⟩)

theorem OMA.solution : type_of% @OMA.S_oeis_a283107.main := by
  intro k hk hp
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (show k - 1 ≠ 0 by omega)
  have hn : 4 * (k - 1) = 2 ^ (e + 2) * m := by rw [he, pow_add]; ring
  have hp' := hp
  rw [hn, isMultiplicative_sigma.map_mul_of_coprime (hm.coprime_two_left.pow_left _)] at hp'
  have htwo : 1 < sigma 1 (2 ^ (e + 2)) := by
    have h := self_le_sigma (n := 2 ^ (e + 2)) (by positivity)
    have hpow : 1 < (2 : ℕ) ^ (e + 2) := one_lt_pow₀ (by decide) (by omega)
    omega
  have hm1 : m = 1 := by
    by_contra h
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have hle := self_le_sigma hm0
    exact Nat.not_prime_mul (by omega) (by omega) hp'
  rw [hn, hm1, mul_one, sigma_zero_apply_prime_pow Nat.prime_two]
  rw [hn, hm1, mul_one, sigma_one_apply_prime_pow Nat.prime_two] at hp
  rw [sum_two_powers] at hp
  exact hp.of_mersenne
