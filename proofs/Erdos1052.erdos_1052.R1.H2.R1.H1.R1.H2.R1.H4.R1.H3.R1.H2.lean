import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H3_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H3.R1.H2

Proves that no unitary perfect number has `11` as its unique repeated odd prime with exponent
`e ≡ 4 (mod 8)`, so `padicValNat 2 n ≤ 0` holds vacuously.

Proof: Since `e ≡ 4 (mod 8)`, we have `1 + 11 ^ 4 ∣ 1 + 11 ^ e`, and `1 + 11 ^ 4 = 2 * 7321`.
Thus the forced chain of simple primes is `7321 → 523 → 131`, and `3 ∣ 131 + 1`. Because `3` is
simple, `3` cannot also divide `2 ^ a + 1`, so `a` must be even. Then `2 ^ a + 1 ≡ 2 (mod 3)`, so
some prime `q ≡ 2 (mod 3)` divides `2 ^ a + 1`. We cannot have `q = 2` (since `a ≥ 1`) or `q = 11`
(since `2 ^ (2k) ≡ 1, 4, 5, 9, 3 (mod 11)`, never `-1`). Thus `q` is a simple prime with `3 ∣ q + 1`,
forcing `q = 131`. But then `131` divides both `2 ^ a + 1` and `523 + 1`, contradicting that `131`
is simple.
-/

namespace OMA.Helpers

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts kernel_balance_one one_add_pow_dvd_of_odd_mul
  prime_dvd_prime_pow two_dvd_of_isUnitaryPerfect three_dvd_two_pow_add_one exists_prime_mod3)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

private lemma four_pow_mod_three (k : ℕ) : 4 ^ k % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

private lemma four_pow_mod_eleven_ne_ten (k : ℕ) : 4 ^ k % 11 ≠ 10 := by
  have h5 : ∀ j : ℕ, 4 ^ (5 * j) % 11 = 1 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add, Nat.mul_mod, ih]
      norm_num
  have hsplit : 4 ^ k % 11 = 4 ^ (k % 5) % 11 := by
    have hk : k = 5 * (k / 5) + k % 5 := (Nat.div_add_mod k 5).symm
    conv_lhs => rw [hk, pow_add, Nat.mul_mod, h5 (k / 5)]
    simp
  rw [hsplit]
  have hr : k % 5 < 5 := Nat.mod_lt k (by norm_num)
  interval_cases (k % 5) <;> norm_num

theorem kill11_e4_mod8 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (he : e % 8 = 4) (hm1 : 1 ≤ m)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) :
    False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, -, -, S7, -⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 4 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  have g7321 : 7321 ∈ P :=
    S7 7321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7321 ∣ 1 + 11 ^ 4).trans hd)
  have g523 : 523 ∈ P := S1 523 (by norm_num) (by norm_num) (by decide) 7321 g7321 (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (by decide) 523 g523 (by norm_num)
  have hm_even : m % 2 = 0 := by
    by_contra hodd
    have h3m : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one (by omega)
    exact S4 3 (by norm_num) (by norm_num) (by decide) h3m 131 g131 (by norm_num)
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  have h2m4 : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  have hmod3 : (2 ^ (2 * k) + 1) % 3 = 2 := by
    rw [h2m4]
    have := four_pow_mod_three k
    omega
  obtain ⟨q, hq, hqd, hq3⟩ := exists_prime_mod3 (2 ^ (2 * k) + 1) hmod3
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2d : 2 ∣ 2 ^ (2 * k) := dvd_pow_self 2 (by omega)
    have : 2 ∣ 1 := (Nat.dvd_add_right h2d).mp hqd
    omega
  have hq11 : q ≠ 11 := by
    rintro rfl
    have h11m : (4 ^ k + 1) % 11 = 0 := by
      rw [← h2m4]
      exact Nat.mod_eq_zero_of_dvd hqd
    have hne := four_pow_mod_eleven_ne_ten k
    omega
  have hqnot : q ∉ ({11} : Finset ℕ) := by simp [hq11]
  have hqP : q ∈ P := S2 q hq hq2 hqnot hqd
  have h3q : 3 ∣ q + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hq_eq : q = 131 :=
    S3 3 (by norm_num) (by norm_num) (by decide) q hqP 131 g131 h3q (by norm_num)
  subst hq_eq
  exact S4 131 (by norm_num) (by norm_num) (by decide) hqd 523 g523 (by norm_num)

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H3_R1.H2 := by
  refine ⟨0, fun n h hS he _ _ _ _ _ _ _ _ _ => ?_⟩
  obtain ⟨hzn, hs⟩ :=
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.simple_of_unique_repeated h.2.ne' hS
  have hzpf : 11 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ :=
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have h2n := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.two_dvd_of_isUnitaryPerfect h
  have hm1 : 1 ≤ padicValNat 2 n := by
    rw [← Nat.factorization_def n Nat.prime_two]
    exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two h.2.ne' h2n
  exact (OMA.Helpers.kill11_e4_mod8 hP he hm1 E).elim
