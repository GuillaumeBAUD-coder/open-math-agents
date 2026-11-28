import OMAReductions.R_EuclidNumbers_infinite_prime_euclid_numbers_R1
import Mathlib

/-! No Euclid number `1 + p₁ ⋯ pₙ` is a proper power. Write it as `b ^ q` with `q` prime. If `q` is
one of the first `n` primes, then `q ∣ b - 1` by Fermat, so `q ^ 2` divides the squarefree product.
Otherwise every one of the first `n` primes divides `b - 1` (its order divides both `q` and `r - 1`),
so the product is at most `b - 1 < b ^ q - 1`. -/

namespace OMA.Step_EuclidNumbers_infinite_prime_euclid_numbers_R1_H2

open EuclidNumbers Finset

/-- The product of the first `n` primes. -/
noncomputable def P (n : ℕ) : ℕ := ∏ i ∈ range n, Nat.nth Nat.Prime i

theorem nth_mono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem P_pos (n : ℕ) : 0 < P n :=
  Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos

/-- A prime dividing `P n` is one of the first `n` primes. -/
theorem prime_dvd_P {r n : ℕ} (hr : r.Prime) (h : r ∣ P n) : ∃ i < n, r = Nat.nth Nat.Prime i := by
  unfold P at h
  obtain ⟨i, hi, hd⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp h
  exact ⟨i, Finset.mem_range.mp hi, (Nat.prime_dvd_prime_iff_eq hr (Nat.prime_nth_prime i)).mp hd⟩

/-- A prime below the `i`-th prime is one of the first `i` primes. -/
theorem prime_lt_nth {q i : ℕ} (hq : q.Prime) (h : q < Nat.nth Nat.Prime i) :
    ∃ j < i, q = Nat.nth Nat.Prime j := by
  refine ⟨Nat.count Nat.Prime q, ?_, (Nat.nth_count hq).symm⟩
  rw [← nth_mono.lt_iff_lt, Nat.nth_count hq]
  exact h

theorem nth_dvd_P {i n : ℕ} (hi : i < n) : Nat.nth Nat.Prime i ∣ P n :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)

/-- `P n` is not divisible by the square of a prime. -/
theorem sq_not_dvd_P {q : ℕ} (hq : q.Prime) : ∀ n : ℕ, ¬ q ^ 2 ∣ P n := by
  intro n
  induction n with
  | zero => intro h; simp [P] at h; exact hq.one_lt.ne' (by simpa using h)
  | succ n ih =>
    intro h
    have hsplit : P (n + 1) = P n * Nat.nth Nat.Prime n := by
      simp [P, Finset.prod_range_succ]
    rw [hsplit] at h
    by_cases hqn : q = Nat.nth Nat.Prime n
    · have h' : q * q ∣ P n * q := by rw [← sq]; exact hqn ▸ h
      have hq' : q ∣ P n := Nat.dvd_of_mul_dvd_mul_right hq.pos (by simpa [mul_comm] using h')
      obtain ⟨i, hi, he⟩ := prime_dvd_P hq hq'
      have := nth_mono.injective (he.symm.trans hqn)
      omega
    · have hcop : Nat.Coprime (q ^ 2) (Nat.nth Nat.Prime n) :=
        Nat.Coprime.pow_left 2 ((Nat.coprime_primes hq (Nat.prime_nth_prime n)).mpr hqn)
      exact ih (hcop.dvd_of_dvd_mul_right h)

theorem euclid_eq (n : ℕ) : Euclid n = 1 + P n := rfl

theorem not_power (n a k : ℕ) (hk : 1 < k) : Euclid n ≠ a ^ k := by
  intro hE
  rw [euclid_eq] at hE
  obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  obtain ⟨m, rfl⟩ := hqk
  set b := a ^ m with hb
  have hbq : b ^ q = 1 + P n := by rw [hb, ← pow_mul, mul_comm]; exact hE.symm
  have hPpos := P_pos n
  have hb2 : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with h | h
    · interval_cases b
      · rw [zero_pow hq.ne_zero] at hbq; omega
      · rw [one_pow] at hbq; omega
    · exact h
  have hPeq : P n = b ^ q - 1 := by omega
  by_cases hqP : q ∣ P n
  · -- q divides b ^ q - 1, so q divides b - 1, so q ^ 2 divides b ^ q - 1
    have h1 : ((q : ℤ)) ∣ (b : ℤ) ^ q - 1 := by
      have : ((q : ℤ)) ∣ ((P n : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hqP
      rw [hPeq, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))] at this
      simpa using this
    have h2 : ((q : ℤ)) ∣ (b : ℤ) ^ q - b := (Int.ModEq.pow_prime_eq_self hq b).symm.dvd
    have h3 : ((q : ℤ)) ∣ (b : ℤ) - 1 := by
      have := dvd_sub h1 h2
      simpa using this
    have h4 := dvd_sub_pow_of_dvd_sub h3 1
    simp only [pow_one, one_pow] at h4
    have h5 : ((q ^ 2 : ℕ) : ℤ) ∣ ((P n : ℕ) : ℤ) := by
      rw [hPeq, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
      push_cast
      exact h4
    exact sq_not_dvd_P hq n (Int.natCast_dvd_natCast.mp h5)
  · -- every one of the first n primes divides b - 1, so P n ≤ b - 1 < b ^ q - 1
    have hall : ∀ i < n, Nat.nth Nat.Prime i ∣ b - 1 := by
      intro i hi
      set r := Nat.nth Nat.Prime i with hr
      have hrp : r.Prime := Nat.prime_nth_prime i
      have hrP : r ∣ b ^ q - 1 := hPeq ▸ nth_dvd_P hi
      have hrb : ¬ r ∣ b := by
        intro hd
        have h1 : r ∣ b ^ q := dvd_pow hd hq.ne_zero
        have h2 : r ∣ b ^ q - (b ^ q - 1) := Nat.dvd_sub h1 hrP
        rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h2
        exact hrp.one_lt.ne' (Nat.dvd_one.mp h2)
      have hcop : Nat.Coprime b r :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hrp).mpr hrb))
      have hferm : r ∣ b ^ (r - 1) - 1 := by
        have := Nat.ModEq.pow_totient hcop
        rw [Nat.totient_prime hrp] at this
        exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp this.symm
      have hg : r ∣ b ^ Nat.gcd q (r - 1) - 1 := by
        rw [← Nat.pow_sub_one_gcd_pow_sub_one]
        exact Nat.dvd_gcd hrP hferm
      have hcq : Nat.Coprime q (r - 1) := by
        rw [Nat.Prime.coprime_iff_not_dvd hq]
        intro hdv
        have hlt : q < r :=
          Nat.lt_of_le_of_lt (Nat.le_of_dvd (Nat.sub_pos_of_lt hrp.one_lt) hdv)
            (Nat.sub_lt hrp.pos one_pos)
        obtain ⟨j, hj, he⟩ := prime_lt_nth hq hlt
        exact hqP (he ▸ nth_dvd_P (hj.trans hi))
      rw [hcq, pow_one] at hg
      exact hg
    have hdiv : P n ∣ b - 1 := by
      unfold P
      rw [show (∏ i ∈ range n, Nat.nth Nat.Prime i) = ∏ r ∈ (range n).image (Nat.nth Nat.Prime), r by
        rw [Finset.prod_image fun i _ j _ h => nth_mono.injective h]]
      apply Finset.prod_primes_dvd
      · intro r hr
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
        exact (Nat.prime_nth_prime i).prime
      · intro r hr
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
        exact hall i (Finset.mem_range.mp hi)
    have hle := Nat.le_of_dvd (by omega) hdiv
    have hsq : b ^ 2 ≤ b ^ q := Nat.pow_le_pow_right (by omega) hq.two_le
    have hb3 : b + 1 ≤ b ^ 2 := by nlinarith
    omega

end OMA.Step_EuclidNumbers_infinite_prime_euclid_numbers_R1_H2

theorem OMA.solution : OMA.R_EuclidNumbers_infinite_prime_euclid_numbers_R1.H2 :=
  OMA.Step_EuclidNumbers_infinite_prime_euclid_numbers_R1_H2.not_power
