import OMAStatements.S_arxiv_2511_19744

/-!
# Toda primes (McKean, Conjecture 1.3): reduction to the multiples of 55 and of 273

Target: `OMA.S_arxiv_2511_19744.main`, every positive integer `n` has two distinct Toda primes,
where a Toda prime of `n` is an odd prime `p` with `p - 1 ∣ 4n` and `gcd(p, 4n / (p - 1)) = 1`.

This file proves the conjecture outright for every `n` divisible neither by `55 = 5 · 11` nor by
`273 = 3 · 7 · 13` (about 98% of all integers), and leaves exactly the two remaining families as
hypotheses:

* `H1`: the conjecture for the multiples of `55`;
* `H2`: the conjecture for the multiples of `273`.

The argument. For an odd prime `p` dividing neither `4` nor `p - 1`, the coprimality condition
reduces to `p ∤ n` (`isTodaPrime_of`). Since `2` and `4` divide `4n`, the primes `3` and `5` are
Toda primes of `n` unless they divide `n`; if `3 ∣ n` then `6, 12 ∣ 4n`, so `7` and `13` are Toda
primes unless they divide `n`; if `5 ∣ n` then `10 ∣ 4n`, so `11` is a Toda prime unless it divides
`n`. If `55 ∤ n` and `273 ∤ n`, a case split on `3 ∣ n`, `5 ∣ n`, `7 ∣ n` always leaves two of
`3, 5, 7, 11, 13` (`two_toda_primes_of_not_dvd`).

What remains is the hard core identified in the paper: there the small candidates are blocked and
one needs Toda primes such as `23 = 2 · 11 + 1` (for multiples of `55`) or `29, 43, 53, 79, 157,
547, 1093` (for multiples of `273`), and so on along Sophie Germain-like chains.
-/

namespace OMA.R_arxiv_2511_19744_R1

open OMA.S_arxiv_2511_19744

/-- Conjecture 1.3 for the multiples of `55 = 5 · 11`. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → 55 ∣ n → ∃ p q : ℕ, p ≠ q ∧ IsTodaPrime n p ∧ IsTodaPrime n q

/-- Conjecture 1.3 for the multiples of `273 = 3 · 7 · 13`. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → 273 ∣ n → ∃ p q : ℕ, p ≠ q ∧ IsTodaPrime n p ∧ IsTodaPrime n q

/-- For an odd prime `p` with `p - 1 ∣ 4n` and `p ∤ n`, `p` is a Toda prime of `n`. -/
lemma isTodaPrime_of {n p : ℕ} (hp : p.Prime) (hodd : Odd p) (hd : (p - 1) ∣ 4 * n)
    (hpn : ¬ p ∣ n) : IsTodaPrime n p := by
  have hp2 : p ≠ 2 := fun h => by subst h; exact absurd hodd (by decide)
  have hp4 : ¬ p ∣ 4 := fun h4 => by
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  refine ⟨hp, hodd, hd, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_⟩
  have h4n : p ∣ 4 * n := h.trans (Nat.div_dvd_of_dvd hd)
  rcases (Nat.Prime.dvd_mul hp).1 h4n with h1 | h1
  · exact hp4 h1
  · exact hpn h1

lemma toda3 {n : ℕ} (h : ¬ 3 ∣ n) : IsTodaPrime n 3 :=
  isTodaPrime_of Nat.prime_three (by decide) ⟨2 * n, by ring⟩ h

lemma toda5 {n : ℕ} (h : ¬ 5 ∣ n) : IsTodaPrime n 5 :=
  isTodaPrime_of (by norm_num) (by decide) ⟨n, by ring⟩ h

lemma toda7 {n : ℕ} (h3 : 3 ∣ n) (h : ¬ 7 ∣ n) : IsTodaPrime n 7 := by
  obtain ⟨m, rfl⟩ := h3
  exact isTodaPrime_of (by norm_num) (by decide) ⟨2 * m, by ring⟩ h

lemma toda13 {n : ℕ} (h3 : 3 ∣ n) (h : ¬ 13 ∣ n) : IsTodaPrime n 13 := by
  obtain ⟨m, rfl⟩ := h3
  exact isTodaPrime_of (by norm_num) (by decide) ⟨m, by ring⟩ h

lemma toda11 {n : ℕ} (h5 : 5 ∣ n) (h : ¬ 11 ∣ n) : IsTodaPrime n 11 := by
  obtain ⟨m, rfl⟩ := h5
  exact isTodaPrime_of (by norm_num) (by decide) ⟨2 * m, by ring⟩ h

/-- Conjecture 1.3 for every `n` divisible neither by `55` nor by `273`. -/
lemma two_toda_primes_of_not_dvd {n : ℕ} (h55 : ¬ 55 ∣ n) (h273 : ¬ 273 ∣ n) :
    ∃ p q : ℕ, p ≠ q ∧ IsTodaPrime n p ∧ IsTodaPrime n q := by
  have no5_11 : 5 ∣ n → ¬ 11 ∣ n := fun h5 h11 =>
    h55 (by simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h11)
  have no7_13 : 3 ∣ n → 7 ∣ n → ¬ 13 ∣ n := fun h3 h7 h13 => by
    have h21 : 21 ∣ n := by simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7
    exact h273 (by simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h21 h13)
  by_cases h3 : 3 ∣ n
  · by_cases h7 : 7 ∣ n
    · have h13 := no7_13 h3 h7
      by_cases h5 : 5 ∣ n
      · exact ⟨11, 13, by decide, toda11 h5 (no5_11 h5), toda13 h3 h13⟩
      · exact ⟨5, 13, by decide, toda5 h5, toda13 h3 h13⟩
    · by_cases h5 : 5 ∣ n
      · exact ⟨11, 7, by decide, toda11 h5 (no5_11 h5), toda7 h3 h7⟩
      · exact ⟨5, 7, by decide, toda5 h5, toda7 h3 h7⟩
  · by_cases h5 : 5 ∣ n
    · exact ⟨3, 11, by decide, toda3 h3, toda11 h5 (no5_11 h5)⟩
    · exact ⟨3, 5, by decide, toda3 h3, toda5 h5⟩

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2511_19744.main := by
  intro h1 h2 n hn
  by_cases h55 : 55 ∣ n
  · exact h1 n hn h55
  by_cases h273 : 273 ∣ n
  · exact h2 n hn h273
  exact two_toda_primes_of_not_dvd h55 h273

end OMA.R_arxiv_2511_19744_R1
