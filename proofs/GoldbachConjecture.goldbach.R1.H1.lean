import OMAReductions.R_GoldbachConjecture_goldbach_R1
import Mathlib

/-! Every even number in `(2, 10000]` is a sum of two primes, by a kernel-checked search:
trial division below `100`, coprimality with the primes up to `100` above it. -/

namespace OMA.Step_GoldbachConjecture_goldbach_R1_H1

/-- Trial division of `n` by `d, d + 1, ...`, for at most `fuel` divisors, succeeding once
`d * d > n`. Running out of fuel counts as failure. -/
def noDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else (n % d != 0) && noDiv n fuel (d + 1)

theorem noDiv_spec (n : ℕ) : ∀ fuel d : ℕ, noDiv n fuel d = true →
    ∀ m : ℕ, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDiv] at h
  | succ fuel ih =>
    intro d h m hdm hmn hdiv
    unfold noDiv at h
    by_cases hlt : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg hlt] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le hdm with rfl | hlt'
      · exact h.1 (Nat.mod_eq_zero_of_dvd hdiv)
      · exact ih (d + 1) h.2 m hlt' hmn hdiv

/-- The product of the primes up to `100`. -/
def P100 : ℕ := 2305567963945518424753102147331756070

theorem small_hit : ∀ m : ℕ, m ≤ 100 → 2 ≤ m → Nat.gcd m P100 ≠ 1 := by decide +kernel

/-- A Boolean primality test for `n ≤ 10000`: trial division below `100`, and above it
coprimality with the primes up to `100`. -/
def isPrimeB (n : ℕ) : Bool :=
  if n ≤ 100 then decide (2 ≤ n) && noDiv n n 2
  else decide (n ≤ 10000) && Nat.gcd n P100 == 1

theorem isPrimeB_spec {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  unfold isPrimeB at h
  split_ifs at h with hn
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h2, hd⟩ := h
    by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hne : n ≠ 1 := by omega
    have hmin := (Nat.minFac_prime hne).two_le
    exact noDiv_spec n n 2 hd (Nat.minFac n) hmin (by nlinarith) (Nat.minFac_dvd n)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨h2, hg⟩ := h
    by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hne : n ≠ 1 := by omega
    have hmin := (Nat.minFac_prime hne).two_le
    have hle : Nat.minFac n ≤ 100 := by nlinarith
    apply small_hit (Nat.minFac n) hle hmin
    exact Nat.eq_one_of_dvd_one (hg ▸ Nat.gcd_dvd_gcd_of_dvd_left P100 (Nat.minFac_dvd n))

/-- Search `p = d, d + 1, ...` (at most `fuel` values) for `p` and `n - p` both prime. -/
def findP (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => (isPrimeB d && isPrimeB (n - d)) || findP n fuel (d + 1)

theorem findP_spec (n : ℕ) : ∀ fuel d : ℕ, findP n fuel d = true →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [findP] at h
  | succ fuel ih =>
    intro d h
    simp only [findP, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · have hq := isPrimeB_spec h2
      have := hq.two_le
      exact ⟨d, n - d, isPrimeB_spec h1, hq, by omega⟩
    · exact ih (d + 1) h

/-- `n` is a sum of two primes, found by search from `2`. -/
def goldbachB (n : ℕ) : Bool := findP n n 2

theorem goldbachB_spec {n : ℕ} (h : goldbachB n = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  findP_spec n n 2 h

/-- Every even number in `[s, s + c)` passes `goldbachB`. -/
def checkFrom : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, s => (s % 2 == 1 || goldbachB s) && checkFrom c (s + 1)

theorem checkFrom_spec : ∀ c s : ℕ, checkFrom c s = true →
    ∀ n : ℕ, s ≤ n → n < s + c → n % 2 = 0 → goldbachB n = true := by
  intro c
  induction c with
  | zero => intro s _ n h1 h2; omega
  | succ c ih =>
    intro s h n h1 h2 h3
    simp only [checkFrom, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rcases h.1 with h' | h'
      · omega
      · exact h'
    · exact ih (s + 1) h.2 n hlt (by omega) h3

theorem check_a : checkFrom 9998 3 = true := by decide +kernel

theorem goldbach_le (n : ℕ) (h2 : 2 < n) (he : Even n) (hn : n ≤ 10000) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  goldbachB_spec (checkFrom_spec 9998 3 check_a n (by omega) (by omega) (Nat.even_iff.mp he))

end OMA.Step_GoldbachConjecture_goldbach_R1_H1

theorem OMA.solution : OMA.R_GoldbachConjecture_goldbach_R1.H1 := by
  intro n h2 he hn
  obtain ⟨p, q, hp, hq, rfl⟩ := OMA.Step_GoldbachConjecture_goldbach_R1_H1.goldbach_le n h2 he hn
  exact ⟨p, q, Nat.prime_iff.mp hp, Nat.prime_iff.mp hq, rfl⟩
