import OMAReductions.R_oeis_a074777_R1

-- Step oeis-a074777.R1.H2: hypothesis H2 of reduction oeis-a074777.R1
-- Credit: @lettucrisp

namespace OeisA074777H2

open ArithmeticFunction

private lemma sum_two_pow : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1
  | 0 => by norm_num
  | k + 1 => by
    rw [Finset.sum_range_succ, sum_two_pow k]
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega

private lemma sigma_one_two_pow (k : ℕ) : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [ArithmeticFunction.sigma_apply, Nat.divisors_prime_pow Nat.prime_two,
      Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, pow_one]
  exact sum_two_pow k

private lemma totient_step {a p : ℕ} (hp : p.Prime) (hcop : a.Coprime p) :
    Nat.totient (a * p) = Nat.totient a * (p - 1) := by
  rw [Nat.totient_mul hcop, Nat.totient_prime hp]

private lemma totient_2 : Nat.totient 2 = 2 ^ 0 := by decide
private lemma totient_6 : Nat.totient 6 = 2 ^ 1 := by decide
private lemma totient_30 : Nat.totient 30 = 2 ^ 3 := by decide
private lemma totient_510 : Nat.totient 510 = 2 ^ 7 := by
  have h : (510 : ℕ) = 30 * 17 := by norm_num
  rw [h, totient_step (by norm_num) (by decide), totient_30]; norm_num

private lemma totient_131070 : Nat.totient 131070 = 2 ^ 15 := by
  have h : (131070 : ℕ) = 510 * 257 := by norm_num
  rw [h, totient_step (by norm_num) (by decide), totient_510]; norm_num

private lemma totient_8589934590 : Nat.totient 8589934590 = 2 ^ 31 := by
  have h : (8589934590 : ℕ) = 131070 * 65537 := by norm_num
  rw [h, totient_step (by norm_num) (by decide), totient_131070]; norm_num

end OeisA074777H2

theorem OMA.solution : OMA.R_oeis_a074777_R1.H2 := by
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [OeisA074777H2.totient_2, OeisA074777H2.sigma_one_two_pow]; norm_num
  · rw [OeisA074777H2.totient_6, OeisA074777H2.sigma_one_two_pow]; norm_num
  · rw [OeisA074777H2.totient_30, OeisA074777H2.sigma_one_two_pow]; norm_num
  · rw [OeisA074777H2.totient_510, OeisA074777H2.sigma_one_two_pow]; norm_num
  · rw [OeisA074777H2.totient_131070, OeisA074777H2.sigma_one_two_pow]; norm_num
  · rw [OeisA074777H2.totient_8589934590, OeisA074777H2.sigma_one_two_pow]; norm_num
