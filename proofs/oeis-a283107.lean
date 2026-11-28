import OMAStatements.S_oeis_a283107
import Mathlib

/-
A283107 contains A281312: if sigma(4(k-1)) is prime, then tau(4(k-1)) is prime.

Write N = 4(k-1) = 2^e * t with t odd, so e >= 2. Since sigma is multiplicative,
sigma(N) = (2^(e+1) - 1) * sigma(t), and the first factor is at least 7. A prime value
forces sigma(t) = 1, that is t = 1, and 2^(e+1) - 1 prime, which forces e + 1 prime.
Then tau(N) = tau(2^e) = e + 1 is prime.
-/

namespace OMA.P283107
open ArithmeticFunction

lemma geom (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : 0 < 2 ^ n := by positivity
    rw [Finset.sum_range_succ, ih, pow_succ]; omega

lemma main' : ∀ k : ℕ, 2 ≤ k →
    Nat.Prime (sigma 1 (4 * (k - 1))) → Nat.Prime (sigma 0 (4 * (k - 1))) := by
  intro k hk hp
  obtain ⟨e, t, ht, hN⟩ := Nat.exists_eq_two_pow_mul_odd (n := 4 * (k - 1)) (by omega)
  have he : 2 ≤ e := by
    by_contra h
    obtain ⟨c, hc⟩ := ht
    have : e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl <;> omega
  rw [hN] at hp ⊢
  have hcop : Nat.Coprime (2 ^ e) t := (Nat.coprime_two_left.2 ht).pow_left e
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow Nat.prime_two,
    geom] at hp
  have h8 : 2 ^ 3 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases Nat.prime_mul_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ht1 : t = 1 := by
      have ht0 : t ≠ 0 := by rintro rfl; simp at ht
      have hle : t ≤ sigma 1 t := by
        rw [sigma_one_apply]
        exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
          (Nat.mem_divisors_self t ht0)
      omega
    subst ht1
    rw [mul_one, sigma_zero_apply_prime_pow Nat.prime_two]
    exact (Nat.prime_of_pow_sub_one_prime (by omega) h1).2
  · omega

end OMA.P283107

theorem OMA.solution : type_of% @OMA.S_oeis_a283107.main := OMA.P283107.main'
