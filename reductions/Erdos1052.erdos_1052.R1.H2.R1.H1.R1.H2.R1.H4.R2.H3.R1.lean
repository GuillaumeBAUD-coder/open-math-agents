import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2

/-!
The odd part of the core shift and the two-adic exponent cannot both be
unrestricted. If the seed supplies 3, or supplies a simple prime p with
3 dividing p+1, no odd prime of the core shift can be 3 or 2 modulo 3.
Indeed such a prime contributes a second factor of 3, directly or through
its own successor. The seed and the core shift cannot share a simple prime.

For an exceptional core shift the seeds 3, 5 and 257 exclude respectively
odd a, a = 2 modulo 4, and a = 8 modulo 16. Combining this with the
inherited Fermat-factor exclusions leaves only the 17-core exception at
a = 4 modulo 8, or a divisible by 2^20.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H3_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (facts S_sq)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (kernel_balance_one prime_dvd_prime_pow one_add_pow_dvd_of_odd_mul)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z ∈ ({7, 11, 17, 19, 31} : Finset ℕ),
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) → (z % 3 = 1 → padicValNat 2 n % 6 ≠ 5) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 1 + z ^ n.factorization z → q % 3 = 1) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z ∈ ({7, 11, 17, 19, 31} : Finset ℕ),
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) → (z % 3 = 1 → padicValNat 2 n % 6 ≠ 5) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ 1 + z ^ n.factorization z ∧ q % 3 ≠ 1) →
    ((z = 17 ∧ 4 ∣ n.factorization 17 ∧ padicValNat 2 n % 8 = 4) ∨ 2 ^ 20 ∣ padicValNat 2 n) →
    padicValNat 2 n ≤ A

/-- If the seed supplies 3 directly, or supplies a simple prime whose successor
is divisible by 3, every odd prime of the core shift is 1 modulo 3. -/
theorem core_shift_primes {m z e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hz3 : z ≠ 3)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) =
       2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (source : 3 ∣ 2 ^ m + 1 ∨ ∃ p ∈ P, p ∣ 2 ^ m + 1 ∧ 3 ∣ p + 1) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 1 + z ^ e → q % 3 = 1 := by
  have hK := prime_dvd_prime_pow (e := e) hz
  obtain ⟨_, _, unique, seed_shift, _, _, from_core, core_shift⟩ := facts hP hK E
  have outside : 3 ∉ ({z} : Finset ℕ) := by simpa [eq_comm] using hz3
  have disjoint (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (hout : q ∉ ({z} : Finset ℕ))
      (hs : q ∣ 2 ^ m + 1) (hc : q ∣ 1 + z ^ e) : False :=
    S_sq hP hK E hq h2 hout ((mul_dvd_mul hs hc).mul_right _)
  have no_three : ¬ 3 ∣ 1 + z ^ e := by
    intro hc
    rcases source with hs | ⟨p, hp, _, h3⟩
    · exact disjoint 3 (by decide) (by decide) outside hs hc
    · exact core_shift 3 (by decide) (by decide) outside hc p hp h3
  intro q hq h2 hc
  have hqz : q ∉ ({z} : Finset ℕ) := by
    intro hmem
    have heq := Finset.mem_singleton.mp hmem
    rw [heq] at hc h2
    cases e with
    | zero => simp only [pow_zero] at hc; exact h2 ((Nat.prime_dvd_prime_iff_eq hz Nat.prime_two).mp hc)
    | succ k =>
      have hd : z ∣ z ^ (k + 1) := dvd_pow_self _ (by omega)
      have h := Nat.dvd_sub hc hd
      exact hz.not_dvd_one (by simpa only [Nat.add_sub_cancel] using h)
  have hq3 : ¬ 3 ∣ q := fun hd => no_three (hd.trans hc)
  by_contra hbad
  have shift : 3 ∣ q + 1 := by omega
  have hmem := from_core q hq h2 hqz hc
  rcases source with hs | ⟨p, hp, hs, h3⟩
  · exact seed_shift 3 (by decide) (by decide) outside hs q hmem shift
  · have heq := unique 3 (by decide) (by decide) outside p hp q hmem h3 shift
    exact disjoint q hq h2 hqz (heq ▸ hs) hc

/-- With repeated prime 17, an odd exponent contributes 9 through 17+1.
An exponent twice an odd number forces both 5 and 29 through 17²+1;
their successors would both contribute 3. -/
theorem four_dvd_core17 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 17 ^ e) * ∏ p ∈ P, (p + 1) =
       2 ^ (m + 1) * 17 ^ e * ∏ p ∈ P, p) : 4 ∣ e := by
  have hK := prime_dvd_prime_pow (e := e) (by norm_num : Nat.Prime 17)
  obtain ⟨_, _, unique, _, _, _, from_core, _⟩ := facts hP hK E
  have oddImpossible : e % 2 ≠ 1 := by
    intro hr
    have hd := one_add_pow_dvd_of_odd_mul (e0 := 1) (z := 17) hr
    exact S_sq hP hK E (c := 3) (by decide) (by decide) (by decide)
      ((((by decide : 3 * 3 ∣ 1 + 17 ^ 1).trans hd).mul_left _).mul_right _)
  have twiceImpossible : e % 4 ≠ 2 := by
    intro hr
    have hd := one_add_pow_dvd_of_odd_mul (e0 := 2) (z := 17) hr
    have h5 := from_core 5 (by decide) (by decide) (by decide) ((by decide : 5 ∣ 1 + 17 ^ 2).trans hd)
    have h29 := from_core 29 (by decide) (by decide) (by decide) ((by decide : 29 ∣ 1 + 17 ^ 2).trans hd)
    exact (by decide : (5 : ℕ) ≠ 29) (unique 3 (by decide) (by decide) (by decide) 5 h5 29 h29 (by decide) (by decide))
  omega

/-- A divisor doubles unless the number is its odd multiple. -/
theorem double_dvd {a d : ℕ} (hd : d ∣ a) (hr : a % (d * 2) ≠ d) : d * 2 ∣ a := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.mul_mod_mul_left] at hr
  have even : k % 2 = 0 := by
    by_contra h
    have h1 : k % 2 = 1 := by omega
    exact hr (by simp [h1])
  refine ⟨k / 2, ?_⟩
  rw [Nat.mul_assoc, show 2 * (k / 2) = k by omega]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2.H3 := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  refine ⟨max A B, ?_⟩
  intro n hn z hzset hS he h7 h6 h10 h14 h35 h20 h28 h8 h16 h4096 hhi
  classical
  have hzlist : z = 7 ∨ z = 11 ∨ z = 17 ∨ z = 19 ∨ z = 31 := by simpa using hzset
  have hz : z.Prime := ((hS z).mpr rfl).1
  have hz2 : z ≠ 2 := by omega
  obtain ⟨hd, hsimple⟩ := simple_of_unique_repeated hn.2.ne' hS
  obtain ⟨hP, E⟩ := kernel_balance_one hn (Nat.mem_primeFactors.mpr ⟨hz, hd, hn.2.ne'⟩) hz2 hsimple
  rw [Nat.factorization_def n Nat.prime_two] at E
  let a := padicValNat 2 n
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ))
  change (2 ^ a + 1) * (1 + z ^ n.factorization z) * ∏ p ∈ P, (p + 1) =
    2 ^ (a + 1) * z ^ n.factorization z * ∏ p ∈ P, p at E
  by_cases good : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 1 + z ^ n.factorization z → q % 3 = 1
  · exact (hA n hn z hzset hS he h7 h6 h10 h14 h35 h20 h28 h8 h16 h4096 hhi good).trans (le_max_left _ _)
  have noSource := fun hs => good (core_shift_primes hP hz (by omega) E hs)
  have D (d : ℕ) (h : a % (2 * d) = d) : 1 + 2 ^ d ∣ 2 ^ a + 1 := by
    simpa only [Nat.add_comm 1 (2 ^ a)] using one_add_pow_dvd_of_odd_mul (z := 2) h
  have fromSeed := (facts hP (prime_dvd_prime_pow hz) E).2.1
  have noOdd : a % 2 ≠ 1 := fun h => noSource (Or.inl (D 1 h))
  have noTwo : a % 4 ≠ 2 := by
    intro h
    have hs : 5 ∣ 2 ^ a + 1 := D 2 h
    exact noSource (Or.inr ⟨5, fromSeed 5 (by decide) (by decide) (by simp; omega) hs, hs, by decide⟩)
  have noEight : a % 16 ≠ 8 := by
    intro h
    have hs : 257 ∣ 2 ^ a + 1 := D 8 h
    exact noSource (Or.inr ⟨257, fromSeed 257 (by norm_num) (by decide) (by simp; omega) hs, hs, by decide⟩)
  have gap : (z = 17 ∧ 4 ∣ n.factorization 17 ∧ a % 8 = 4) ∨ 2 ^ 20 ∣ a := by
    by_cases h4 : a % 8 = 4
    · have hz17 : z = 17 := by by_contra h; exact h8 h h4
      subst z
      exact Or.inl ⟨rfl, four_dvd_core17 hP E, h4⟩
    right
    have d2 : 2 ∣ a := double_dvd (d := 1) (one_dvd a) noOdd
    have d4 : 4 ∣ a := double_dvd d2 noTwo
    have d8 : 8 ∣ a := double_dvd d4 h4
    have d16 : 16 ∣ a := double_dvd d8 noEight
    have lift (r : ℕ) (lo : 4 ≤ r) (hi : r < 20) (hd : 2 ^ r ∣ a) : 2 ^ (r + 1) ∣ a := by
      rw [pow_succ]
      apply double_dvd hd
      by_cases h11 : r = 11
      · subst r
        exact h4096 (by omega)
      · apply hhi r
        interval_cases r <;> first | decide | omega
    have climb (j : ℕ) (hj : j ≤ 16) : 2 ^ (4 + j) ∣ a := by
      induction j with
      | zero => exact d16
      | succ j ih => exact lift (4 + j) (by omega) (by omega) (ih (by omega))
    exact climb 16 (by decide)
  push_neg at good
  exact (hB n hn z hzset hS he h7 h6 h10 h14 h35 h20 h28 h8 h16 h4096 hhi good gap).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H3_R1
