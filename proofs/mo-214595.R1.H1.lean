import OMAReductions.R_mo_214595_R1

/-!
# Proof of `mo-214595.R1.H1`

Proves via covering congruences modulo `7`, `19`, and `113` that for every `r ≥ 2` with
`r % 6 ≠ 3`, at least one of `10 ^ 2 ^ r + k` (`k ∈ {1, 3, 7, 9}`) is composite:
- `r % 2 = 0` (`r ≥ 2`): `2 ^ r ≡ 4 (mod 6)`, so `10 ^ (2 ^ r) ≡ 10 ^ 4 ≡ 4 (mod 7)` and
  `7 ∣ 10 ^ (2 ^ r) + 3`.
- `r % 6 = 5`: `2 ^ r ≡ 14 (mod 18)`, so `10 ^ (2 ^ r) ≡ 10 ^ 14 ≡ 16 (mod 19)` and
  `19 ∣ 10 ^ (2 ^ r) + 3`.
- `r % 6 = 1` (`r ≥ 7`): `2 ^ r ≡ 16 (mod 112)`, so `10 ^ (2 ^ r) ≡ 10 ^ 16 ≡ 106 (mod 113)` and
  `113 ∣ 10 ^ (2 ^ r) + 7`.
-/

namespace Mo214595R1H1Proof

private lemma two_pow_mod_six_even {k : ℕ} (hk : 1 ≤ k) : 2 ^ (2 * k) % 6 = 4 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add, Nat.mul_mod, ih]
    decide

private lemma two_pow_mod_18_of_mod6_eq5 (k : ℕ) : 2 ^ (6 * k + 5) % 18 = 14 := by
  induction k with
  | zero => decide
  | succ m ih =>
    rw [show 6 * (m + 1) + 5 = (6 * m + 5) + 6 by omega, pow_add, Nat.mul_mod, ih]
    decide

private lemma two_pow_mod_112_of_mod6_eq1 {k : ℕ} (hk : 1 ≤ k) : 2 ^ (6 * k + 1) % 112 = 16 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [show 6 * (m + 1) + 1 = (6 * m + 1) + 6 by omega, pow_add, Nat.mul_mod, ih]
    decide

private lemma ten_pow_mod_of_period {p period rem e val : ℕ} (hp : 1 < p)
    (hper : 10 ^ period % p = 1) (hrem : e % period = rem) (hval : 10 ^ rem % p = val) :
    10 ^ e % p = val := by
  have he : period * (e / period) + rem = e := by
    rw [← hrem]; exact Nat.div_add_mod e period
  rw [← he, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hper, one_pow, hval]
  have hlt : val < p := by
    rw [← hval]
    exact Nat.mod_lt _ (by omega)
  rw [Nat.mod_eq_of_lt hp, one_mul, Nat.mod_eq_of_lt hlt]

private lemma not_prime_of_dvd_of_lt {p n : ℕ} (hp : 1 < p) (hlt : p < n) (hd : p ∣ n) :
    ¬ n.Prime := by
  intro hpr
  rcases (Nat.dvd_prime hpr).mp hd with h1 | h2 <;> omega

private lemma ten_pow_two_pow_ge {r : ℕ} (hr : 2 ≤ r) : 10 ^ 4 ≤ 10 ^ (2 ^ r) := by
  have h4 : 4 ≤ 2 ^ r := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
  exact Nat.pow_le_pow_right (by decide) h4

end Mo214595R1H1Proof

theorem OMA.solution : OMA.R_mo_214595_R1.H1 := by
  intro r hr hne3
  have hge := Mo214595R1H1Proof.ten_pow_two_pow_ge hr
  by_cases hev : r % 2 = 0
  · refine ⟨3, by decide, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, r = 2 * k := ⟨r / 2, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have h2mod : 2 ^ r % 6 = 4 := hk ▸ Mo214595R1H1Proof.two_pow_mod_six_even hk1
    have h10mod : 10 ^ (2 ^ r) % 7 = 4 :=
      Mo214595R1H1Proof.ten_pow_mod_of_period (by decide) (by decide) h2mod (by decide)
    have hd : 7 ∣ 10 ^ (2 ^ r) + 3 := Nat.dvd_of_mod_eq_zero (by omega)
    exact Mo214595R1H1Proof.not_prime_of_dvd_of_lt (by decide) (by omega) hd
  · by_cases h5 : r % 6 = 5
    · refine ⟨3, by decide, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k, r = 6 * k + 5 := ⟨r / 6, by omega⟩
      have h2mod : 2 ^ r % 18 = 14 := hk ▸ Mo214595R1H1Proof.two_pow_mod_18_of_mod6_eq5 k
      have h10mod : 10 ^ (2 ^ r) % 19 = 16 :=
        Mo214595R1H1Proof.ten_pow_mod_of_period (by decide) (by decide) h2mod (by decide)
      have hd : 19 ∣ 10 ^ (2 ^ r) + 3 := Nat.dvd_of_mod_eq_zero (by omega)
      exact Mo214595R1H1Proof.not_prime_of_dvd_of_lt (by decide) (by omega) hd
    · have h1 : r % 6 = 1 := by omega
      refine ⟨7, by decide, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k, r = 6 * k + 1 := ⟨r / 6, by omega⟩
      have hk1 : 1 ≤ k := by omega
      have h2mod : 2 ^ r % 112 = 16 := hk ▸ Mo214595R1H1Proof.two_pow_mod_112_of_mod6_eq1 hk1
      have h10mod : 10 ^ (2 ^ r) % 113 = 106 :=
        Mo214595R1H1Proof.ten_pow_mod_of_period (by decide) (by decide) h2mod (by decide)
      have hd : 113 ∣ 10 ^ (2 ^ r) + 7 := Nat.dvd_of_mod_eq_zero (by omega)
      exact Mo214595R1H1Proof.not_prime_of_dvd_of_lt (by decide) (by omega) hd
